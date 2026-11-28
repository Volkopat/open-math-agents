#!/usr/bin/env bash
# The merger: one long-running trusted job that gives every finished check-proof run its verdict (tools/verdict_one.sh)
# and runs the backlog pass (tools/backlog_pass.sh) when the API budget allows. One runner slot instead of one queued
# verdict job per proof. Never checks out or runs pull request code.
# GitHub's API budget for GITHUB_TOKEN is shared by every job of the repository, so polling is kept cheap: the runs
# in progress are listed every loop (1-2 calls) and a run that leaves that list is read once; a full scan of the last
# three hours runs every 10 minutes, in 30-minute slices (GitHub returns at most 1,000 runs per query: a single query
# over hours silently dropped the oldest runs, whose proofs then waited for hours without a verdict).
# v3: a green check run means accepted and its title carries the PR number, so accepted runs need no artifact
# download; the loop also restarts itself on a new version of this script pushed to main (state kept in done/).
# v4: verdicts go oldest pull request first (the filing order decides who solves a problem first), slots fed without a barrier,
# loop so polling never pauses for long; runs listed in base/tools/requeue.tsv (lost by earlier versions) are given
# their verdict once; an accepted run whose merge was refused is retried even after a restart; credits that the site
# did not record are retried every 10 minutes.
# Needs: GH_TOKEN REPO [OMA_SITE]; base/ (a checkout of main) in the current directory.
set -uo pipefail
export MERGER_V2=1 MERGER_V3=1
# Every GitHub call has a time limit: one call that never answers must not stall all verdicts.
GH_BIN="$(type -P gh)"; export GH_BIN
ROOT="$PWD"; mkdir -p "$ROOT/done" "$ROOT/remerge"
# API calls use the GitHub App's installation token when the App is set up (secrets OMA_APP_ID and
# OMA_APP_PRIVATE_KEY: its own budget, 15,000 calls an hour, apart from GITHUB_TOKEN's, which check-proof and the
# batch checker share), else GITHUB_TOKEN. Git pushes always use the checkout's GITHUB_TOKEN (a push made with an App
# token would start the push workflows on main). The token lasts an hour; app_token() mints a new one every 45 minutes.
export GH_TOKEN_BASE="$GH_TOKEN" OMA_TOKEN_FILE="$ROOT/.app_token"
gh() { local T=""; [ -s "$OMA_TOKEN_FILE" ] && T=$(cat "$OMA_TOKEN_FILE"); GH_TOKEN="${T:-$GH_TOKEN_BASE}" timeout 90 "$GH_BIN" "$@"; }
export -f gh
app_token() {  # mint an installation token for this repository from the App's key; on any failure, GITHUB_TOKEN
  [ -n "${OMA_APP_ID:-}" ] && [ -n "${OMA_APP_KEY:-}" ] || return 0
  [ -s "$OMA_TOKEN_FILE" ] && [ $(( $(date -u +%s) - $(stat -c %Y "$OMA_TOKEN_FILE") )) -lt 2700 ] && return 0
  local K NOW H P S J INST TOK; K=$(umask 077; mktemp); printf '%s\n' "$OMA_APP_KEY" > "$K"; NOW=$(date -u +%s)
  b64u() { openssl base64 -A | tr '+/' '-_' | tr -d '='; }
  H=$(printf '{"alg":"RS256","typ":"JWT"}' | b64u)
  P=$(printf '{"iat":%d,"exp":%d,"iss":"%s"}' $((NOW - 60)) $((NOW + 540)) "$OMA_APP_ID" | b64u)
  S=$(printf '%s.%s' "$H" "$P" | openssl dgst -sha256 -sign "$K" 2>/dev/null | b64u); rm -f "$K"
  J="$H.$P.$S"
  INST=$(curl -sS -m 30 -H "Authorization: Bearer $J" -H "Accept: application/vnd.github+json" "https://api.github.com/repos/$REPO/installation" | jq -r '.id // empty' 2>/dev/null)
  [ -n "$INST" ] && TOK=$(curl -sS -m 30 -X POST -H "Authorization: Bearer $J" -H "Accept: application/vnd.github+json" "https://api.github.com/app/installations/$INST/access_tokens" | jq -r '.token // empty' 2>/dev/null)
  if [ -n "${TOK:-}" ]; then
    echo "::add-mask::$TOK"; (umask 077; printf '%s' "$TOK" > "$OMA_TOKEN_FILE.tmp") && mv "$OMA_TOKEN_FILE.tmp" "$OMA_TOKEN_FILE"
    echo "merger: GitHub App token minted (installation $INST)"
  else
    echo "merger: GitHub App token not minted, using GITHUB_TOKEN"
    # an expired token must not stay in use: drop it once it is older than 55 minutes
    [ -s "$OMA_TOKEN_FILE" ] && [ $(( NOW - $(stat -c %Y "$OMA_TOKEN_FILE") )) -ge 3300 ] && rm -f "$OMA_TOKEN_FILE"
  fi
  return 0
}
app_token
export CREDIT_RETRY_FILE="$ROOT/credit_retry.txt"; touch "$CREDIT_RETRY_FILE"
# Credit ledger: credit.sh appends a line per merge (tools/ledger_entry.py), tools/ledger_post.sh sends them to the site.
export LEDGER_FILE="$ROOT/ledger.jsonl"; touch "$LEDGER_FILE"
SELF="$ROOT/base/tools/merger_loop.sh"; SELF_SHA=$(sha1sum "$SELF" | cut -d' ' -f1)
# Hand-over without a gap: a job lasts at most 6 hours and a new one waits in GitHub's runner queue (behind hundreds of
# proof checks) before it starts, so the next merger is started early (every 20 minutes, no concurrency group) and
# waits on standby until the running merger ends. A job that finds a merger with more than 75 minutes left, or another
# standby, stops at once (a few seconds of a runner).
INITIAL_BACK=10800
if [ -z "${MERGER_RESUME:-}" ] && [ -n "${GITHUB_RUN_ID:-}" ]; then
  TOOK_OVER=0
  while :; do
    gh api "repos/$REPO/actions/workflows/backlog.yml/runs?status=in_progress&per_page=30" \
      --jq '.workflow_runs[] | [.id, (.run_started_at // .created_at)] | @tsv' > mergers.tsv 2>/dev/null || { sleep 30; continue; }
    MINE=$(awk -F'\t' -v me="$GITHUB_RUN_ID" '$1 == me {print $2}' mergers.tsv); MINE=${MINE:-$(date -u +%FT%TZ)}
    OLDEST=$(awk -F'\t' -v me="$GITHUB_RUN_ID" '$1 != me' mergers.tsv | sort -t$'\t' -k2 | head -n 1)
    [ -n "$OLDEST" ] || break                                   # no other merger: this one works
    TKO=$(cat base/tools/merger_takeover 2>/dev/null | tr -cd '0-9'); TKO=${TKO:-0}
    OSTART=$(printf '%s' "$OLDEST" | cut -f2)
    [[ "$OSTART" > "$MINE" ]] && break                          # the others started after this one: this one works
    LEFT=$(( $(date -u -d "$OSTART" +%s) + ${MERGER_SECONDS:-20400} + 300 - $(date -u +%s) ))
    OTHERS=$(awk -F'\t' -v me="$GITHUB_RUN_ID" -v o="$OSTART" -v m="$MINE" '$1 != me && $2 > o && $2 < m' mergers.tsv | wc -l)
    # a takeover asked on main (tools/merger_takeover, a unix time): a merger started before it stops at its next
    # pass, and a job started after it waits on standby for that instead of leaving
    [ "$(date -u -d "$OSTART" +%s)" -lt "$TKO" ] && [ "$(date -u -d "$MINE" +%s)" -ge "$TKO" ] && [ "$OTHERS" = 0 ] && LEFT=1
    if [ "$OTHERS" -gt 0 ] || [ "$LEFT" -gt 4500 ]; then
      echo "merger: another merger is running (${LEFT}s left, $OTHERS on standby): nothing to do"; exit 0
    fi
    echo "merger: standby, the running merger ends in about ${LEFT}s"; TOOK_OVER=1; sleep 60
  done
  # taking over from a merger that just ended: it handled everything but the last minutes
  [ "$TOOK_OVER" = 1 ] && INITIAL_BACK=2400
fi
if [ -n "${MERGER_RESUME:-}" ]; then
  # restarted by an older version of this loop after an update: same job, same deadline, same state
  START=$MERGER_START; END=$MERGER_END; BPID=${MERGER_BPID:-}; LAST_BACKLOG=${MERGER_LAST_BACKLOG:-0}; LAST_SCAN=0
  INITIAL_BACK=${MERGER_INITIAL_BACK:-10800}
  touch "$ROOT/watch.txt" "$ROOT/prev_inprog.tsv"
  echo "merger: resumed on version $SELF_SHA"
else
  : > "$ROOT/watch.txt"; : > "$ROOT/prev_inprog.tsv"
  START=$(date -u +%s); END=$(( START + ${MERGER_SECONDS:-20400} ))   # 5 h 40 min, under the 6 h job limit
  BPID=""; LAST_BACKLOG=0; LAST_SCAN=0
fi
touch "$ROOT/queue.tsv"
SLOTS=${SLOTS:-32}; declare -A SPID; LAST_REFRESH=0; LAST_OLD=0; OLDJOBS=1; LAST_CREDIT=0; REQ_SHA=""; LAST_PENDING=0; CPID=""
wait_slots() { local i; for i in $(seq 1 "$SLOTS"); do [ -n "${SPID[$i]:-}" ] && wait "${SPID[$i]}" 2>/dev/null; SPID[$i]=""; done; }
iso() { date -u -d "@$1" +%Y-%m-%dT%H:%M:%SZ; }
nap() { local S=$1 L=$(( END - $(date -u +%s) )); [ "$S" -gt "$L" ] && S=$L; [ "$S" -gt 0 ] && sleep "$S"; return 0; }
# The merger's state (the queue, what was given, refused merges to retry, credits to resend) is pushed every 5 minutes
# to the branch merger-state, as one commit that replaces the previous one, and read back by the next merger: a
# hand-over used to drop the whole queue (2,805 items on 28 November). Git, not the API: no budget. Never main.
state_save() {
  local D="$ROOT/state_out" G="git -C $ROOT/base" T C F; rm -rf "$D"; mkdir -p "$D"
  cp "$ROOT/queue.tsv" "$D/queue.tsv" 2>/dev/null || : > "$D/queue.tsv"
  ls "$ROOT/done" > "$D/done.list" 2>/dev/null
  (cd "$ROOT/remerge" && for F in *; do [ -f "$F" ] && printf '%s\t%s\n' "$F" "$(cat "$F")"; done) > "$D/remerge.tsv" 2>/dev/null
  cp "$ROOT/rejected.txt" "$D/rejected.txt" 2>/dev/null || : > "$D/rejected.txt"
  cp "$CREDIT_RETRY_FILE" "$D/credit_retry.txt" 2>/dev/null || : > "$D/credit_retry.txt"
  date -u +%s > "$D/saved"
  tail -n 400 "$ROOT/vlog.txt" > "$D/vlog.txt" 2>/dev/null || : > "$D/vlog.txt"
  { tail -n 40 "$ROOT/merger_out.txt" 2>/dev/null; } > "$D/status.txt"
  T=$(for F in queue.tsv done.list remerge.tsv rejected.txt credit_retry.txt saved vlog.txt status.txt; do
        printf '100644 blob %s\t%s\n' "$($G hash-object -w "$D/$F")" "$F"; done | $G mktree) || return 0
  C=$($G -c user.name=oma-merger -c user.email=oma-merger@users.noreply.github.com commit-tree "$T" -m "merger state") || return 0
  timeout 60 $G push -q --force origin "$C:refs/heads/merger-state" 2>/dev/null && echo "merger: state saved ($(wc -l < "$D/queue.tsv") queued)"
  LAST_STATE=$(date -u +%s)
}
state_load() {  # a new merger (not a restart in place): what the previous one left, if it is less than 12 hours old
  local G="git -C $ROOT/base" S
  timeout 60 $G fetch -q --depth 1 origin merger-state 2>/dev/null || { echo "merger: no saved state"; return 0; }
  S=$($G show FETCH_HEAD:saved 2>/dev/null || echo 0)
  [ $(( $(date -u +%s) - S )) -lt 43200 ] || { echo "merger: saved state too old, ignored"; return 0; }
  $G show FETCH_HEAD:queue.tsv >> "$ROOT/queue.tsv" 2>/dev/null
  (cd "$ROOT/done" && $G show FETCH_HEAD:done.list 2>/dev/null | grep -E '^[A-Za-z0-9._-]+$' | xargs -r touch)
  $G show FETCH_HEAD:remerge.tsv 2>/dev/null | while IFS=$'\t' read -r F N; do
    [[ "$F" =~ ^[0-9]+$ && "$N" =~ ^[0-9]+$ ]] && echo "$N" > "$ROOT/remerge/$F"; done
  $G show FETCH_HEAD:rejected.txt >> "$ROOT/rejected.txt" 2>/dev/null
  $G show FETCH_HEAD:credit_retry.txt >> "$CREDIT_RETRY_FILE" 2>/dev/null
  echo "merger: resumed the saved state of $(iso "$S"): $(wc -l < "$ROOT/queue.tsv") queued, $(ls "$ROOT/done" | wc -l) given"
}
LAST_STATE=0
JQ_RUN='[.id, .head_sha, .run_attempt, .html_url, .updated_at, (.conclusion // ""), (.display_title // "")] | @tsv'
remaining() { gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset)"' 2>/dev/null || echo "999 0"; }
budget() {  # never let the repository run dry: other jobs (checks, deploys) need the API too; GraphQL is checked too
  local rem reset grem greset; read -r rem reset grem greset < <(gh api rate_limit --jq '"\(.resources.core.remaining) \(.resources.core.reset) \(.resources.graphql.remaining) \(.resources.graphql.reset)"' 2>/dev/null || echo "999 0 999 0")
  echo "$(date -u +%H:%M:%S) budget ($([ -s "$OMA_TOKEN_FILE" ] && echo "App token" || echo GITHUB_TOKEN), limit $(gh api rate_limit --jq .resources.core.limit 2>/dev/null)): core $rem, graphql $grem, queue $(wc -l < "$ROOT/queue.tsv"), busy $(cat "$ROOT/busy" 2>/dev/null || echo ?)/$SLOTS" >> "$ROOT/merger_out.txt"
  echo "budget: core $rem, graphql $grem, queue $(wc -l < "$ROOT/queue.tsv"), busy slots $(cat "$ROOT/busy" 2>/dev/null || echo ?)/$SLOTS, verdicts in 10 min $(awk -v t=$(( $(date -u +%s) - 600 )) '$1 >= t' "$ROOT/verdicts.log" 2>/dev/null | wc -l)"
  # the wait never runs past the end of this job, and the queue is saved first (the next merger resumes it)
  if [ "${rem:-999}" -lt 300 ]; then echo "API budget low ($rem left), waiting for the reset"; touch "$ROOT/budget_low"; nap $(( reset - $(date -u +%s) + 5 )); fi
  if [ "${grem:-999}" -lt 60 ]; then echo "GraphQL budget low ($grem left), waiting for the reset"; touch "$ROOT/budget_low"; nap $(( greset - $(date -u +%s) + 5 )); fi
  rm -f "$ROOT/budget_low"
  # Spread the budget over the hour: from the burn since the last look, the slots the dispatcher may use until the
  # reset (all of them while the budget lasts at the current pace; fewer, down to 2, when it would run out first).
  local NOWB=$(date -u +%s) CAP=$SLOTS
  if [ -n "${PREV_REM:-}" ] && [ "$NOWB" -gt "${PREV_T:-0}" ] && [ "${reset:-0}" = "${PREV_RESET:-}" ] && [ "${rem:-0}" -le "$PREV_REM" ] && [ "${reset:-0}" -gt "$NOWB" ]; then
    local BURN=$(( (PREV_REM - rem) * 60 / (NOWB - PREV_T) )) MINS=$(( (reset - NOWB) / 60 + 1 ))
    [ "$BURN" -gt 3000 ] && BURN=0   # not one bucket's burn (two buckets answered in turn): ignored
    BURN_AVG=$(( (${BURN_AVG:-$BURN} * 2 + BURN) / 3 )); BURN=$BURN_AVG
    [ "$BURN" -gt 0 ] && CAP=$(( SLOTS * (rem - 500) / (BURN * MINS) ))
    [ "$CAP" -gt "$SLOTS" ] && CAP=$SLOTS; [ "$CAP" -lt 2 ] && CAP=2
    echo "$(date -u +%H:%M:%S) budget pace: $BURN calls/min, $MINS min to reset, slots allowed $CAP" >> "$ROOT/merger_out.txt"
  fi
  echo "$CAP" > "$ROOT/slots_cap"; PREV_REM=$rem; PREV_T=$NOWB; PREV_RESET=$reset
}
refresh() {  # main moved on (merges): pull it; each verdict slot's copy is synced when the slot next starts (sync_slot)
  ( flock -w 300 7
    git -C "$ROOT/base" fetch -q --depth 1 origin main && git -C "$ROOT/base" reset -q --hard FETCH_HEAD; git -C "$ROOT/base" clean -fdq
  ) 7> "$ROOT/base.lock"
  BASE_REV=$(git -C "$ROOT/base" rev-parse HEAD 2>/dev/null || date +%s%N)
  TOOLS_REV=$(git -C "$ROOT/base" rev-parse HEAD:tools 2>/dev/null || echo "$BASE_REV")
}
declare -A SYNCED SYNCED_AT
sync_slot() {  # $1 slot: bring its copy of main up to date (rsync: only what changed), never while it works
  # Only when tools/ changed, or every 15 minutes: verdict_one.sh fetches main's statements, reductions and data
  # itself and git_merge.sh fetches main, so a slot needs a fresh copy for the code only. (Re-syncing every slot after
  # each refresh, one after the other in the dispatcher, left the slots without new work for most of the time.)
  [ -d "$ROOT/base_$1" ] && [ "${SYNCED[$1]:-}" = "$TOOLS_REV" ] && [ $(( $(date +%s) - ${SYNCED_AT[$1]:-0} )) -lt 900 ] && return 0
  ( flock -w 300 7
    if command -v rsync >/dev/null; then rsync -a --delete "$ROOT/base/" "$ROOT/base_$1/"; else rm -rf "$ROOT/base_$1"; cp -a "$ROOT/base" "$ROOT/base_$1"; fi
  ) 7> "$ROOT/base.lock"
  SYNCED[$1]=$TOOLS_REV; SYNCED_AT[$1]=$(date +%s)
}
scan() {  # completed runs created in the last $1 seconds, in 30-minute slices (at most 1,000 runs per query)
  local NOW A B FLOOR; NOW=$(date -u +%s); FLOOR=$(( START - INITIAL_BACK ))
  A=$(( NOW - $1 )); [ "$A" -lt "$FLOOR" ] && A=$FLOOR      # never before what this merger is responsible for
  for (( ; A < NOW; A += 1800 )); do
    B=$(( A + 1800 ))
    gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=completed&per_page=100&created=$(iso $A)..$(iso $B)" \
      --jq ".workflow_runs[] | select(.conclusion != \"cancelled\") | $JQ_RUN" 2>/dev/null || true
  done
}
publish_pending() {  # the open pull requests, by problem id (their title), to the site: the desk stops handing them out
  # only those opened in the last 12 hours and not rejected by this merger: an abandoned or rejected pull request must
  # not keep a problem away from everyone
  # Also (prs, queue) every open pull request with its author and what this merger knows of it (check running, checked
  # and waiting for its verdict, rejected with the reason, labelled needs-human-review) and the size of GitHub's queue:
  # the site shows each contributor where their submissions stand (/a/<handle>, /api/pending?handle=). Same single
  # listing of the open pull requests as before, plus one call for the number of queued checks.
  local CUT REJ PID; CUT=$(iso $(( $(date -u +%s) - 43200 )))
  PID='def pid: .title | sub("^(proof|disproof|statement|reduction|reduce|step|formalize|Proof)\\s*:\\s*"; "") | gsub("^\\s+|\\s+$"; "");'
  gh api --paginate "repos/$REPO/pulls?state=open&per_page=100" \
    --jq '.[] | {number, title, created_at, by: .user.login, review: any(.labels[]?; .name == "needs-human-review")}' > open_all.jsonl 2>/dev/null || return 0
  REJ=$(sort -un "$ROOT/rejected.txt" 2>/dev/null | jq -cs '.'); [ -n "$REJ" ] || REJ='[]'
  jq -c --arg cut "$CUT" --argjson rej "$REJ" "$PID"' select(.created_at > $cut and ((.number as $n | $rej | index($n)) | not)) | {id: pid, pr: .number, since: .created_at}' \
    open_all.jsonl 2>/dev/null | jq -s '.' > open_prs.json || return 0
  [ -s open_prs.json ] || return 0
  local CHK='$7 ~ /^(check-proof|batch) #[0-9]+$/ { sub(/^[a-z-]+ #/, "", $7); print $7 }' QUEUED RUNNING PERHOUR
  awk -F'\t' "$CHK" prev_inprog.tsv 2>/dev/null | sort -un | jq -cs '.' > st_checking.json
  awk -F'\t' "$CHK" "$ROOT/queue.tsv" 2>/dev/null | sort -un | jq -cs '.' > st_verdict.json
  jq -cs 'map({key: (.pr | tostring), value: .reason}) | from_entries' "$ROOT/reasons.jsonl" > st_reasons.json 2>/dev/null || echo '{}' > st_reasons.json
  jq -c --argjson rej "$REJ" --slurpfile chk st_checking.json --slurpfile ver st_verdict.json --slurpfile why st_reasons.json "$PID"'
    .number as $n | {pr: $n, id: pid, by: .by, since: .created_at} +
    (if ($chk[0] | index($n)) then {st: "checking"} elif ($ver[0] | index($n)) then {st: "verdict"}
     elif ($rej | index($n)) then {st: "rejected"} + (if $why[0][$n | tostring] then {reason: $why[0][$n | tostring]} else {} end)
     elif .review then {st: "review"} else {} end)' open_all.jsonl 2>/dev/null | jq -s '.' > open_states.json 2>/dev/null || echo '[]' > open_states.json
  QUEUED=$(gh api "repos/$REPO/actions/workflows/check-proof.yml/runs?status=queued&per_page=1" --jq '.total_count' 2>/dev/null)
  [[ "$QUEUED" =~ ^[0-9]+$ ]] || QUEUED=null
  RUNNING=$(awk 'END { print NR }' prev_inprog.tsv 2>/dev/null); [[ "$RUNNING" =~ ^[0-9]+$ ]] || RUNNING=0
  # verdicts given in the last hour (one done/pr.<n>.<head> per verdict): the pace that the site's wait estimates use
  PERHOUR=$(awk -v t=$(( $(date -u +%s) - 3600 )) '$1 >= t' "$ROOT/verdicts.log" 2>/dev/null | wc -l); [[ "$PERHOUR" =~ ^[0-9]+$ ]] || PERHOUR=0
  local OIDC=""
  if [ -n "${ACTIONS_ID_TOKEN_REQUEST_URL:-}" ]; then
    OIDC=$(curl -sS -m 30 -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=lefttosolve.com" | jq -r '.value // ""')
  fi
  jq -n --slurpfile items open_prs.json --slurpfile prs open_states.json --arg oidc "$OIDC" --argjson running "$RUNNING" --argjson queued "$QUEUED" --argjson perhour "$PERHOUR" \
    '{oidc: $oidc, items: $items[0], prs: ($prs[0] // []), queue: {running: $running, queued: $queued, perHour: $perhour}}' > pending_post.json \
    || jq -n --slurpfile items open_prs.json --arg oidc "$OIDC" '{oidc: $oidc, items: $items[0]}' > pending_post.json
  echo "merger: pending list $(jq length open_prs.json) open pull requests: $(curl -sS -m 60 -X POST "${OMA_SITE:-https://lefttosolve.com}/api/pending" -H 'Content-Type: application/json' --data @pending_post.json 2>&1 | head -c 120)"
}
verdict() {  # $1 run id, $2 head sha, $3 attempt, $4 url, $5 old (1/0), $6 slot, $7 conclusion, $8 title, $9 mode
  local ID="$1" SHA="$2" ATT="$3" URL="$4" OLD="$5" B="$ROOT/base_$6" W="$ROOT/work_$6" CONC="$7" TITLE="$8" MODE="${9:-}" PR
  rm -rf "$W"; mkdir -p "$W"; ln -s "$B" "$W/base"
  # green = accepted, but only for a run of the current check-proof (it ends with the step "Fail unless accepted"):
  # an old copy of the workflow on another branch is green whatever the verdict and is titled with the PR title, so
  # its title must never be trusted; those runs (and anything unusual) go through the artifact, whose pr.txt is the
  # run's own pull request number. Kind and polarity come from the trusted re-lint either way.
  local GREEN_PR=""
  if [ "$CONC" = success ] && [[ "$TITLE" =~ ^check-proof\ \#([0-9]+)$ ]]; then
    GREEN_PR="${BASH_REMATCH[1]}"
    [ "$(gh api "repos/$REPO/actions/runs/$ID/jobs" --jq '[.jobs[].steps[]? | select(.name == "Fail unless accepted" and .conclusion == "success")] | length' 2>/dev/null)" -ge 1 ] 2>/dev/null || GREEN_PR=""
  fi
  if [ -n "$GREEN_PR" ]; then
    mkdir -p "$W/artifact"; echo "$GREEN_PR" > "$W/artifact/pr.txt"; echo '{"verdict":"accepted","reason":""}' > "$W/artifact/verdict.json"
  elif [ "$MODE" = batch ]; then
    # a batch checker verdict, read from a trusted batch-check run by tools/batch_verdicts.sh (attempt 3: never re-run)
    [ -s "$ROOT/batch/$ID/verdict.json" ] || return 0
    cp -r "$ROOT/batch/$ID" "$W/artifact"
  elif ! gh run download "$ID" --repo "$REPO" -n verdict -D "$W/artifact" >/dev/null 2>&1; then
    # not finished yet (left the in-progress list for a re-run or a queue) or no artifact: look again later, twice at
    # most (an artifact that is gone stays gone; the batch checker answers that head instead)
    local NA; NA=$(( $(cat "$ROOT/noart/$ID.$ATT" 2>/dev/null || echo 0) + 1 )); [ -e "$ROOT/budget_low" ] && NA=$(( NA - 1 )); mkdir -p "$ROOT/noart"; echo "$NA" > "$ROOT/noart/$ID.$ATT"
    if [ "$NA" -ge 3 ]; then
      echo "$(date -u +%H:%M:%S) run $ID.$ATT ($TITLE): no artifact after $NA tries, left to the batch checker" >> "$ROOT/vlog.txt"; return 0
    fi
    echo "$(date -u +%H:%M:%S) run $ID.$ATT ($TITLE): no artifact yet (try $NA)" >> "$ROOT/vlog.txt"
    echo "$ID" >> "$ROOT/watch.txt"; rm -f "$ROOT/done/$ID.$ATT"; return 0
  fi
  PR=$(head -c 12 "$W/artifact/pr.txt" 2>/dev/null | tr -cd '0-9'); [ -n "$PR" ] || return 0
  [ -e "$ROOT/done/pr.$PR.$SHA" ] && return 0   # this head already has its verdict (from check-proof or the batch checker)
  # On hold (tools/merger_hold.txt on main, one pull request number per line, # comments): no verdict and no merge yet,
  # nothing posted. The run is not marked done, so the scans find it again and it gets its verdict, in its place in the
  # filing order, once its number leaves the file. For a person's review of an unexpected claim (28 Nov: three PRs that
  # together would close an open variant of Erdős #142).
  if [ -s "$B/tools/merger_hold.txt" ] && grep -qx "$PR" <(sed 's/#.*//; s/[^0-9]//g' "$B/tools/merger_hold.txt"); then
    echo "$(date -u +%H:%M:%S) #$PR run $ID.$ATT: held (tools/merger_hold.txt), no verdict yet" >> "$ROOT/vlog.txt"
    rm -f "$ROOT/done/$ID.$ATT"; return 0
  fi
  local RM; RM=$(cat "$ROOT/remerge/$PR" 2>/dev/null || echo 0)
  [ "$MODE" = remerge ] && [ "$RM" = 0 ] && RM=1               # requeued: accepted and reported before, merge again
  if [ "$OLD" = 1 ] && [ "$CONC" != success ] && gh api "repos/$REPO/issues/$PR/comments?per_page=100" --jq '.[].body' 2>/dev/null | grep -qF "$URL"; then
    # already reported (by an earlier merger): a rejection stays reported; an accepted proof still open was not merged
    # (a refused merge whose retries were lost in a restart): merge it now without repeating the verdict
    [ "$CONC" = success ] || return 0
    [ "$RM" = 0 ] && RM=1
  fi
  local VT0; VT0=$(date +%s)
  ( cd "$W" && VERDICT_MODE="$MODE" RELINT="$W/relint.json" RUN_ID="$ID" RUN_ATTEMPT="$ATT" HEAD_SHA="$SHA" RUN_URL="$URL" REMERGE="$RM" \
      timeout 900 bash "$B/tools/verdict_one.sh" ) > "$W/log.txt" 2>&1
  local RC=$? SUM VT; VT=$(( $(date +%s) - VT0 ))
  SUM="#$PR run $ID.$ATT: ${VT}s $(grep -m1 'group commit:' "$W/git_merge.log" 2>/dev/null | sed -E 's/ in one push \([0-9a-f]+\)//') $(grep -m1 -oE '^T[a-z_]+=[0-9 a-z_=]+' "$W/log.txt" 2>/dev/null)exit $RC $(grep -m1 -oiE 'merged by git|comment deferred|without a comment|skip: stale|rate limit|ACCEPTED|REJECTED|FAULT|already on main|not into main|secondary' "$W/log.txt" || true)"
  # a rejection whose comment GitHub refused (secondary rate limit on comments): the verdict is not given yet, retry
  # it later (three times at most), instead of marking it given with nobody told
  if [ "$RC" != 0 ] && [ -s "$W/reason.txt" ] && [ ! -e "$W/remerge.flag" ]; then
    local NC; NC=$(( $(cat "$ROOT/noart/c.$ID.$ATT" 2>/dev/null || echo 0) + 1 )); mkdir -p "$ROOT/noart"; echo "$NC" > "$ROOT/noart/c.$ID.$ATT"
    if [ "$NC" -lt 3 ]; then rm -f "$ROOT/done/$ID.$ATT"; echo "$ID" >> "$ROOT/watch.txt"; touch "$W/rerun.flag"; SUM="$SUM (comment refused, retried later)"; fi
  fi
  echo "$SUM"
  # readable while the job runs (the job log is not): the last lines of each verdict go to the saved state (state_save)
  { echo "$(date -u +%H:%M:%S) $SUM"; [ "$RC" = 0 ] || tail -n 4 "$W/log.txt" | cut -c1-300 | sed 's/^/    /'; } >> "$ROOT/vlog.txt"
  grep -qE 'REJECTED|already on main' "$W/log.txt" && echo "$PR" >> "$ROOT/rejected.txt"
  # A rejection: verdict_one.sh writes its reason to reason.txt (the grep above only sees what it prints; the verdict
  # itself goes to a comment). The pull request leaves the pending list and its reason is published (publish_pending).
  if [ -s "$W/reason.txt" ]; then
    echo "$PR" >> "$ROOT/rejected.txt"
    jq -nc --argjson pr "$PR" --arg r "$(head -c 300 "$W/reason.txt")" '{pr: $pr, reason: $r}' >> "$ROOT/reasons.jsonl" 2>/dev/null || true
  fi
  # a batch rejection whose comment waits for the gate: not given yet, it comes back with the next batch pass
  [ -e "$W/defer.flag" ] && { rm -f "$ROOT/done/$ID.$ATT"; git -C "$B" clean -fdq -- proofs reductions statements 2>/dev/null; return 0; }
  [ -e "$W/rerun.flag" ] && echo "$ID" >> "$ROOT/watch.txt"   # a fault re-runs the check: same run id, next attempt
  if [ -e "$W/remerge.flag" ]; then                               # merge refused: try the same verdict again later
    echo $((RM + 1)) > "$ROOT/remerge/$PR"; rm -f "$ROOT/done/$ID.$ATT"
    [ "$MODE" = batch ] || echo "$ID" >> "$ROOT/watch.txt"        # a batch verdict comes back with the next pass
  fi
  [ -e "$W/remerge.flag" ] || [ -e "$W/rerun.flag" ] || touch "$ROOT/done/pr.$PR.$SHA"
  echo "$(date -u +%s) $PR" >> "$ROOT/verdicts.log"
  git -C "$B" clean -fdq -- proofs reductions statements 2>/dev/null || true
}
refresh
[ -n "${MERGER_RESUME:-}" ] || state_load
# As many slots as the disk holds (each has a full copy of main), keeping 3 GB free.
SZ=$(du -sm "$ROOT/base" 2>/dev/null | cut -f1); SZ=$(( ${SZ:-500} + 20 ))
HAVE=$(ls -d "$ROOT"/base_* 2>/dev/null | wc -l); FREE=$(df -Pm "$ROOT" | awk 'NR == 2 {print $4}')
MAXS=$(( (${FREE:-0} + HAVE * SZ - 3072) / SZ )); [ "$MAXS" -lt 1 ] && MAXS=1
[ "$SLOTS" -gt "$MAXS" ] && { echo "merger: disk for $MAXS slots only (copy of main ${SZ} MB, ${FREE} MB free)"; SLOTS=$MAXS; }
echo "merger: $SLOTS slots"
LLID="$$-$(date +%s%N)"; echo "$LLID" > "$ROOT/ledger_loop.id"; bash "$ROOT/base/tools/ledger_post.sh" loop "$LLID" & LLOOP=$!
SPOOL="$ROOT/spool"; mkdir -p "$SPOOL"; touch watch.txt pending.txt
spool() { local F="$SPOOL/.c.$BASHPID.$(date +%s%N)"; cat > "$F"; [ -s "$F" ] && mv "$F" "${F/\/.c./\/c.}" || rm -f "$F"; }
# The work is split in three processes, so that polling never leaves a slot idle:
# - fast_poll: the check-proof runs that left the in-progress list, and the watched ones (every ~15 s);
# - slow_poll: the 10-minute scan, the batch checker's verdicts, old verdict jobs, requeued runs, credits to resend,
#   the pending list for the site, the backlog pass and the saved state;
# - the dispatcher (this shell): merges what the pollers found into the queue (oldest pull request first) and keeps
#   every slot busy; it also refreshes main and restarts in place on a new version of this script.
fast_poll() {
  while [ "$(date -u +%s)" -lt "$END" ]; do
    local T=$(date -u +%s); app_token; budget
    { gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=in_progress&per_page=100" --jq ".workflow_runs[] | $JQ_RUN" > inprog.tsv 2>/dev/null || cp prev_inprog.tsv inprog.tsv
      cut -f1 inprog.tsv | sort > now_ids; cut -f1 prev_inprog.tsv | sort > prev_ids
      for LID in $(comm -23 prev_ids now_ids); do
        gh api "repos/$REPO/actions/runs/$LID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" 2>/dev/null \
          || echo "$LID" >> watch.txt
      done
      mv inprog.tsv prev_inprog.tsv
      mv watch.txt watch.cur 2>/dev/null || : > watch.cur; touch watch.txt
      for WID in $(sort -u watch.cur); do
        gh api "repos/$REPO/actions/runs/$WID" --jq "select(.status == \"completed\" and .conclusion != \"cancelled\") | $JQ_RUN" 2>/dev/null || true
      done
    } | spool
    local L=$(( 15 - $(date -u +%s) + T )); [ "$L" -gt 0 ] && sleep "$L"
  done
}
slow_poll() {
  local LAST_SCAN=0 LAST_BATCH=0 LAST_OLD=0 OLDJOBS=1 LAST_CREDIT=0 LAST_PENDING=0 LAST_SUCC=0 SUCC_N="" LAST_LAT=0 LAT="" LATS="" LATC="" REQ_SHA="" CPID="" NOW REM B
  while [ "$(date -u +%s)" -lt "$END" ]; do
    NOW=$(date -u +%s)
    if [ $(( NOW - LAST_SCAN )) -ge 600 ]; then LAST_SCAN=$NOW; scan 10800 | spool; fi
    # Latency watch (28 Nov: /solved was slow again): every 30 minutes one cold render of /solved (a random _lat
    # parameter bypasses the page cache). Over 3 s: a line in the vlog and one GitHub issue "Slow page: /solved" (a new
    # one only when none is open). No paging, no retry storm: one GET per half hour.
    if [ -n "${GITHUB_RUN_ID:-}" ] && [ $(( NOW - LAST_LAT )) -ge 1800 ]; then
      LAST_LAT=$NOW
      LAT=$(curl -s -o /dev/null -m 30 -w '%{http_code} %{time_total}' "${OMA_SITE:-https://lefttosolve.com}/solved?_lat=$RANDOM$RANDOM" 2>/dev/null || echo "000 30")
      LATS=${LAT#* }; LATC=${LAT%% *}
      if [ "$LATC" != 200 ] || awk -v t="$LATS" 'BEGIN { exit !(t > 3) }'; then
        echo "$(date -u +%H:%M:%S) latency watch: /solved cold render $LATS s (HTTP $LATC)" >> "$ROOT/vlog.txt"
        SUCC_N=$(GH_TOKEN="$GH_TOKEN_BASE" timeout 60 "$GH_BIN" api "repos/$REPO/issues?state=open&creator=github-actions%5Bbot%5D&per_page=100" \
          --jq '[.[] | select(.pull_request == null and .title == "Slow page: /solved")] | length' 2>/dev/null)
        [ "$SUCC_N" = 0 ] && GH_TOKEN="$GH_TOKEN_BASE" timeout 60 "$GH_BIN" api -X POST "repos/$REPO/issues" -f title="Slow page: /solved" \
          -f body="The merger's latency watch measured a cold render of https://lefttosolve.com/solved (page cache bypassed) at ${LATS} s, HTTP ${LATC}, at $(date -u +%FT%TZ) (threshold 3 s). It checks every 30 minutes and opens no new issue while this one is open." >/dev/null 2>&1 || true
      fi
    fi
    # The successor: GitHub's schedule (*/20) can stay silent for hours under load (none from 10:35 to 15:20 on
    # 28 November, so the merger that ended at 15:08 had no successor and nothing merged until one was started by hand).
    # In its last 65 minutes this merger asks for one itself (workflow_dispatch, with the workflow's own token), every 15
    # minutes while no other merger job is queued or running; the new job waits on standby as usual.
    if [ -n "${GITHUB_RUN_ID:-}" ] && [ $(( END - NOW )) -lt 3900 ] && [ $(( NOW - LAST_SUCC )) -ge 900 ]; then
      LAST_SUCC=$NOW
      SUCC_N=$(GH_TOKEN="$GH_TOKEN_BASE" timeout 60 "$GH_BIN" api "repos/$REPO/actions/workflows/backlog.yml/runs?per_page=30" \
        --jq "[.workflow_runs[] | select(.id != $GITHUB_RUN_ID and .status != \"completed\")] | length" 2>/dev/null)
      if [ "$SUCC_N" = 0 ]; then
        GH_TOKEN="$GH_TOKEN_BASE" timeout 60 "$GH_BIN" api -X POST "repos/$REPO/actions/workflows/backlog.yml/dispatches" -f ref=main >/dev/null 2>&1 \
          && echo "merger: successor requested ($(( (END - NOW) / 60 )) min left)" || echo "merger: successor request refused"
      fi
    fi
    if [ -f base/tools/batch_verdicts.sh ] && [ $(( NOW - LAST_BATCH )) -ge 90 ]; then
      # three hours back even after a hand-over: a queue lost with the previous merger is found again (cheaply: verdicts
      # of pull requests merged or closed since are dropped without an API call)
      LAST_BATCH=$NOW; ROOT="$ROOT" START="$START" FLOOR=$(( START - 10800 )) timeout 240 bash base/tools/batch_verdicts.sh 2>> batchv.log | spool || true
    fi
    # verdict jobs queued by the old per-proof trigger still run: leave their commits to them (no double report)
    if [ "$OLDJOBS" = 1 ] && [ $(( NOW - LAST_OLD )) -ge 300 ]; then
      LAST_OLD=$NOW
      gh api --paginate "repos/$REPO/actions/workflows/verdict.yml/runs?status=queued&per_page=100" \
        --jq '.workflow_runs[] | select(.event == "workflow_run") | .head_sha' > pending.new 2>/dev/null || echo x >> pending.new
      mv pending.new pending.txt; [ -s pending.txt ] || OLDJOBS=0
    fi
    # runs that earlier versions lost (base/tools/requeue.tsv, same columns plus a mode): queued once per version of it
    if [ -s base/tools/requeue.tsv ] && [ "$(sha1sum base/tools/requeue.tsv | cut -d' ' -f1)" != "$REQ_SHA" ]; then
      REQ_SHA=$(sha1sum base/tools/requeue.tsv | cut -d' ' -f1); grep -v '^#' base/tools/requeue.tsv | spool
      echo "merger: requeued $(grep -vc '^#' base/tools/requeue.tsv) runs"
    fi
    # credits the site did not record (it answered an error): retry every 10 minutes, at most 5 minutes per pass
    if [ -s "$CREDIT_RETRY_FILE" ] && [ $(( NOW - LAST_CREDIT )) -ge 600 ] && { [ -z "$CPID" ] || ! kill -0 "$CPID" 2>/dev/null; }; then
      LAST_CREDIT=$NOW; sort -u "$CREDIT_RETRY_FILE" > credit_all.txt; head -n 30 credit_all.txt > credit_todo.txt
      tail -n +31 credit_all.txt > "$CREDIT_RETRY_FILE"
      ( C="$ROOT/credit_work"; rm -rf "$C"; mkdir -p "$C"; cd "$C"
        timeout 300 bash -c 'for P in $(cat "$1"); do bash "$2/tools/credit.sh" "$P" >/dev/null 2>&1 || true; done' _ "$ROOT/credit_todo.txt" "$ROOT/base" || true
        echo "merger: retried $(wc -l < "$ROOT/credit_todo.txt") credits in the background" ) &
      CPID=$!
    fi
    # every 10 minutes: the numbers of the open pull requests (complete listings only), so the dispatcher drops queued
    # runs of pull requests merged or closed since without spending two API calls on each
    if [ $(( NOW - ${LAST_OPEN:-0} )) -ge 600 ]; then
      LAST_OPEN=$NOW
      gh api --paginate "repos/$REPO/pulls?state=open&per_page=100" --jq '.[].number' > open_nums.new 2>/dev/null \
        && [ -s open_nums.new ] && sort -un open_nums.new > open_nums.tmp && mv open_nums.tmp open_nums.txt
      rm -f open_nums.new
    fi
    # every 15 minutes: the open pull requests to the site, so no agent is sent to a problem with a proof waiting
    if [ $(( NOW - LAST_PENDING )) -ge 900 ]; then LAST_PENDING=$NOW; publish_pending; fi
    # backlog: only when no pass is running, at most every 15 minutes, and with budget to spare for the verdicts
    read -r REM _ < <(remaining)
    if { [ -z "$BPID" ] || ! kill -0 "$BPID" 2>/dev/null; } && [ $(( NOW - LAST_BACKLOG )) -ge 900 ] && [ "${REM:-0}" -gt 1500 ] && [ ! -s queue.tsv ]; then
      LAST_BACKLOG=$NOW; B="$ROOT/backlog"; rm -rf "$B"; mkdir -p "$B"
      ( flock -w 300 7; cp -a "$ROOT/base" "$B/base" ) 7> "$ROOT/base.lock"
      ( cd "$B" && LANES=1 BACKLOG_MIN_BUDGET=800 timeout 3000 bash "$B/base/tools/backlog_pass.sh" 2>&1 | grep -E "merged|batch|done:|budget" | sed 's/^/backlog: /' ) &
      BPID=$!
    fi
    [ $(( NOW - LAST_STATE )) -ge 120 ] && state_save
    sleep 10
  done
}
fast_poll & FPID=$!
slow_poll & SPPID=$!
stop_pollers() { kill "$FPID" "$SPPID" 2>/dev/null; wait "$FPID" "$SPPID" 2>/dev/null; }
mapfile -t QL < <(awk 'NF' queue.tsv); QI=0; LAST_MERGE=0; LAST_QSAVE=0
while [ "$(date -u +%s)" -lt "$END" ]; do
  NOW=$(date -u +%s)
  if [ $(( NOW - LAST_REFRESH )) -ge 120 ]; then
    LAST_REFRESH=$NOW; refresh
    TKO=$(cat base/tools/merger_takeover 2>/dev/null | tr -cd '0-9')
    if [ -n "$TKO" ] && [ "$START" -lt "$TKO" ] && [ -n "${GITHUB_RUN_ID:-}" ]; then
      echo "merger: takeover asked on main: handing over to the newer job"; break
    fi
    if [ "$(sha1sum "$SELF" | cut -d' ' -f1)" != "$SELF_SHA" ]; then
      echo "merger: new version on main, restarting in place"; stop_pollers; wait_slots
      printf '%s\n' "${QL[@]:$QI}" | awk 'NF' > queue.tsv
      export MERGER_RESUME=1 MERGER_START=$START MERGER_END=$END MERGER_BPID="" MERGER_LAST_BACKLOG=$NOW MERGER_INITIAL_BACK=$INITIAL_BACK
      exec bash "$SELF"
    fi
  fi
  # what the pollers found joins the queue, oldest pull request first (every 5 s at most: the sort reads the whole queue)
  if [ $(( NOW - LAST_MERGE )) -ge 5 ] && ls "$SPOOL"/c.* >/dev/null 2>&1; then
    LAST_MERGE=$NOW; ls "$SPOOL"/c.* > spool.list
    { printf '%s\n' "${QL[@]:$QI}"; xargs -r cat < spool.list; } | awk -F'\t' 'NF >= 6 && !seen[$1]++' > all.tsv
    xargs -r rm -f < spool.list
    # open pull requests as of the last complete listing (at most 20 minutes old); newer pull requests are kept
    : > open_set.txt; OMAX=0
    if [ -s open_nums.txt ] && [ $(( NOW - $(stat -c %Y open_nums.txt) )) -lt 1200 ]; then cp open_nums.txt open_set.txt; OMAX=$(tail -n 1 open_set.txt); fi
    declare -A OPEN=(); while read -r n; do OPEN[$n]=1; done < open_set.txt; DROPPED=0
    : > next.tsv
    while IFS=$'\t' read -r ID SHA ATT URL UPD CONC TITLE MODE; do
      [ -n "$ID" ] || continue
      [ -n "$CONC" ] || { echo "$ID" >> watch.txt; continue; }   # not finished yet
      [ "$CONC" = skipped ] && continue   # check-proof switched off (vars.OMA_CHECK_PROOF): the batch checker answers
      # a fork's first run waiting for approval never runs (no artifact, no verdict): the batch checker answers it
      [ "$CONC" = action_required ] && { touch "done/$ID.$ATT"; continue; }
      [ -e "done/$ID.$ATT" ] && continue
      [ -s pending.txt ] && grep -qx "$SHA" pending.txt 2>/dev/null && { touch "done/$ID.$ATT"; continue; }   # an old verdict job reports it
      N=999999; [[ "$TITLE" =~ ([0-9]+)$ ]] && N=${BASH_REMATCH[1]}
      if [ "$OMAX" -gt 0 ] && [ "$N" -le "$OMAX" ] && [ -z "${OPEN[$N]:-}" ] && [ -z "${MODE:-}" ]; then
        touch "done/$ID.$ATT"; DROPPED=$((DROPPED + 1)); continue   # merged or closed since: nothing to report
      fi
      # rejections and faults first: they merge nothing, so the filing order does not apply to them, and their authors
      # should hear at once; accepted runs stay oldest pull request first
      P=1; [ "$CONC" = success ] || [ -n "${MODE:-}" ] || P=0
      printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$P" "$N" "$ID" "$SHA" "$ATT" "$URL" "$UPD" "$CONC" "$TITLE" "${MODE:-}" >> next.tsv
    done < all.tsv
    # one check-proof run per pull request: the newest (an older run is of an older head, which verdict_one.sh would
    # only find stale after an API call); runs of the batch checker and requeued runs are kept
    sort -t$'\t' -k2,2n -k3,3nr next.tsv | awk -F'\t' -v D="$ROOT/done" '$10 != "" || $2 == 999999 || !seen[$2]++ {print; next} {print D "/" $3 "." $5 > "dupes.txt"}' > next_u.tsv
    [ -s dupes.txt ] && { xargs -r touch < dupes.txt; DROPPED=$((DROPPED + $(wc -l < dupes.txt))); rm -f dupes.txt; }
    mapfile -t QL < <(sort -t$'\t' -k1,1n -k2,2n -k3,3n next_u.tsv | cut -f3-); QI=0
    [ "$DROPPED" -gt 0 ] && echo "$(date -u +%H:%M:%S) queue: dropped $DROPPED runs of closed pull requests, ${#QL[@]} left" >> "$ROOT/merger_out.txt"
  fi
  # every free slot takes the next item at once
  BUSY=0
  for i in $(seq 1 "$SLOTS"); do
    if [ -n "${SPID[$i]:-}" ] && kill -0 "${SPID[$i]}" 2>/dev/null; then BUSY=$((BUSY + 1)); continue; fi
    [ -n "${SPID[$i]:-}" ] && wait "${SPID[$i]}" 2>/dev/null; SPID[$i]=""
    [ "$QI" -lt "${#QL[@]}" ] && [ ! -e "$ROOT/budget_low" ] && [ "$BUSY" -lt "$(cat "$ROOT/slots_cap" 2>/dev/null || echo "$SLOTS")" ] || continue
    IFS=$'\t' read -r ID SHA ATT URL UPD CONC TITLE MODE <<< "${QL[$QI]}"; QI=$((QI + 1))
    [ -e "done/$ID.$ATT" ] && continue
    touch "done/$ID.$ATT"
    OLD=0; [ "$(date -u -d "$UPD" +%s 2>/dev/null || echo 0)" -lt "$START" ] && OLD=1
    [ -n "${MODE:-}" ] && OLD=0   # requeued runs: checked by hand to have no verdict (or a refused merge)
    sync_slot "$i"
    verdict "$ID" "$SHA" "$ATT" "$URL" "$OLD" "$i" "$CONC" "$TITLE" "${MODE:-}" & SPID[$i]=$!; BUSY=$((BUSY + 1))
  done
  echo "$BUSY" > "$ROOT/busy"
  # the queue on disk, for the saved state and the pending list (written by the pollers' side)
  if [ $(( NOW - LAST_QSAVE )) -ge 30 ]; then LAST_QSAVE=$NOW; printf '%s\n' "${QL[@]:$QI}" | awk 'NF' > queue.tmp && mv queue.tmp queue.tsv; fi
  sleep 1
done
stop_pollers; wait_slots; printf '%s\n' "${QL[@]:$QI}" | awk 'NF' > queue.tsv; state_save
echo stop > "$ROOT/ledger_loop.id"; kill "$LLOOP" 2>/dev/null; bash "$ROOT/base/tools/ledger_post.sh" once   # last lines
wait
echo "merger: time is up; the next scheduled run takes over"
