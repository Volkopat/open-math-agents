#!/usr/bin/env bash
# Census for the batch checker: the first job of .github/workflows/batch-check.yml, before the shards start. It writes
# $OUT (uploaded as the artifact bcensus of the same run, which every shard downloads):
#   done.tsv        heads the batch checker already answered: the newest trusted artifact of every shard (bv-0 ..
#                   bv-<MAX_SHARDS - 1>, whatever the shard count was) and the previous census
#   rej.tsv         heads check-proof.yml rejected (runs concluded "failure"): the previous census plus the runs created
#                   since its cursor minus 6 hours (a run can finish hours after it was created); the first census
#                   reads them all, in 6-hour slices (GitHub lists at most 1,000 runs per query)
#                   Only rejections whose verdict can still reach the pull request count (see REJ_FROM below).
#   verdicts.jsonl  the batch verdicts of the last 3 hours, which the shards publish again (so a merger that was away
#                   finds them even though this run's artifacts replace the previous run's)
#   cursor          the newest creation time seen
# Only artifacts of runs of this workflow on main started by a schedule, a dispatch or a push are read: an artifact of
# the same name uploaded by a pull request's run is ignored. A check-proof run counts by its title and head together:
# a run can only say something about the head it ran on. Nothing here can make a head be accepted: at worst a forged
# entry makes the batch checker skip a head, which check-proof (or a new push) still answers.
# API: ~2 calls per shard artifact, 1 per trusted run, 1-2 per 6 hours of check-proof runs. Needs GH_TOKEN, REPO, OUT.
set -uo pipefail
OUT="${OUT:?}"; MAX_SHARDS="${MAX_SHARDS:-16}"; mkdir -p "$OUT" "$OUT/tmp"
T="$OUT/tmp"; : > "$T/done.tsv"; : > "$T/rej.tsv"; : > "$T/verdicts.jsonl"
declare -A TRUSTED=()
trusted() {  # $1 run id: a run of batch-check.yml on main, not from a pull request
  if [ -z "${TRUSTED[$1]:-}" ]; then
    local OK; OK=$(gh api "repos/$REPO/actions/runs/$1" --jq 'select(.path == ".github/workflows/batch-check.yml" and .head_branch == "main" and (.event == "schedule" or .event == "workflow_dispatch" or .event == "push") and .repository.full_name == .head_repository.full_name) | .id' 2>/dev/null || true)
    if [ "$OK" = "$1" ]; then TRUSTED[$1]=1; else TRUSTED[$1]=0; fi
  fi
  [ "${TRUSTED[$1]}" = 1 ]
}
newest() {  # $1 artifact name, $2 directory: unpack its newest trusted copy there; fails when there is none
  local A AID RID
  A=$(gh api "repos/$REPO/actions/artifacts?name=$1&per_page=10" --jq '.artifacts[] | select(.expired | not) | [.id, .workflow_run.id] | @tsv') || { echo "cannot list artifacts" >&2; exit 1; }
  while IFS=$'\t' read -r AID RID; do
    [ -n "$AID" ] && trusted "$RID" || continue
    rm -rf "$2"; mkdir -p "$2"
    gh api "repos/$REPO/actions/artifacts/$AID/zip" > "$2/a.zip" && (cd "$2" && unzip -o -q a.zip) && { echo "$1: run $RID"; return 0; }
  done <<< "$A"
  return 1
}
CURSOR=""
if newest bcensus "$T/prev"; then
  cat "$T/prev/done.tsv" >> "$T/done.tsv" 2>/dev/null; cat "$T/prev/rej.tsv" >> "$T/rej.tsv" 2>/dev/null
  cat "$T/prev/verdicts.jsonl" >> "$T/verdicts.jsonl" 2>/dev/null; CURSOR=$(cat "$T/prev/cursor" 2>/dev/null)
fi
for K in $(seq 0 $(( MAX_SHARDS - 1 ))); do
  if newest "bv-$K" "$T/s$K"; then
    cat "$T/s$K/done.tsv" >> "$T/done.tsv" 2>/dev/null; cat "$T/s$K/verdicts.jsonl" >> "$T/verdicts.jsonl" 2>/dev/null
  fi
done
# check-proof rejections, in 6-hour slices from the cursor minus 6 hours (the first time: from the start)
FROM=$(( $(date -u -d "${CURSOR:-2026-11-25T00:00:00Z}" +%s) - 21600 )); NOW=$(date -u +%s)
for (( A = FROM; A < NOW; A += 21600 )); do
  B=$(( A + 21600 ))
  gh api --paginate "repos/$REPO/actions/workflows/check-proof.yml/runs?status=failure&per_page=100&created=$(date -u -d "@$A" +%FT%TZ)..$(date -u -d "@$B" +%FT%TZ)" \
    --jq '.workflow_runs[] | [.display_title, .head_sha, .created_at] | @tsv' >> "$T/runs.tsv" || { echo "cannot list check-proof runs" >&2; exit 1; }
done
# The repository moved to lefttosolve2 on 28 Nov 2026 at 08:22 UTC and the artifacts of earlier check-proof runs did
# not come along: the merger cannot read those verdicts, so a rejection from before the move never reached its pull
# request (956 open PRs from 02:00-03:30 alone had no comment). Rejections from runs created before REJ_FROM are not
# skipped any more: the batch checker checks those heads again and its verdict goes out like any other. Pull requests
# that already carry a comment (a verdict was reported) stay skipped. Search API: its own budget, ~1 call per 100.
REJ_FROM="${REJ_FROM:-2026-11-28T08:30:00Z}"
: > "$T/commented.txt"
for PAGE in $(seq 1 10); do
  gh api "search/issues?q=repo:$REPO+is:pr+is:open+comments:%3E0&per_page=100&page=$PAGE" --jq '.items[].number' >> "$T/commented.txt" 2>/dev/null || break
  [ "$(wc -l < "$T/commented.txt")" -lt $(( PAGE * 100 )) ] && break
done
export REJ_FROM
python3 -I - "$T" "$OUT" <<'PY'
import json, os, re, sys, time
t, out = sys.argv[1], sys.argv[2]
done = {}
for line in open(os.path.join(t, "done.tsv")):
    p = line.rstrip("\n").split("\t")
    if len(p) >= 3 and p[0].isdigit() and re.fullmatch(r"[0-9a-f]{40}", p[1]):
        done[(p[0], p[1])] = p[2]
rej_from = os.environ.get("REJ_FROM", "")
commented = set(open(os.path.join(t, "commented.txt")).read().split()) if os.path.exists(os.path.join(t, "commented.txt")) else set()
rej, cursor = {}, ""
for line in open(os.path.join(t, "rej.tsv")):
    p = line.split()
    # entries of censuses before REJ_FROM have no creation time: kept only when the PR already has a comment
    if len(p) >= 3 and p[2] >= rej_from or len(p) >= 2 and p[0] in commented:
        rej[(p[0], p[1])] = p[2] if len(p) >= 3 else ""
if os.path.exists(os.path.join(t, "runs.tsv")):
    for line in open(os.path.join(t, "runs.tsv")):
        p = line.rstrip("\n").split("\t")
        m = re.fullmatch(r"check-proof #(\d+)", p[0]) if len(p) >= 3 else None
        if m and re.fullmatch(r"[0-9a-f]{40}", p[1]):
            cursor = max(cursor, p[2])
            if p[2] >= rej_from or m.group(1) in commented:
                rej[(m.group(1), p[1])] = p[2]
seen, lines, now = set(), [], time.time()
for line in open(os.path.join(t, "verdicts.jsonl"), encoding="utf-8"):
    try:
        d = json.loads(line)
    except Exception:
        continue
    k = (d.get("pr"), d.get("head"))
    if k not in seen and now - d.get("t", 0) <= 10800:
        seen.add(k); lines.append(json.dumps(d, ensure_ascii=False) + "\n")
with open(os.path.join(out, "done.tsv"), "w") as f:
    f.writelines("%s\t%s\t%s\n" % (a, b, c) for (a, b), c in done.items())
with open(os.path.join(out, "rej.tsv"), "w") as f:
    f.writelines("%s\t%s\t%s\n" % (a, b, c) for (a, b), c in sorted(rej.items()))
open(os.path.join(out, "verdicts.jsonl"), "w", encoding="utf-8").writelines(lines)
prev = open(os.path.join(t, "prev", "cursor")).read().strip() if os.path.exists(os.path.join(t, "prev", "cursor")) else ""
open(os.path.join(out, "cursor"), "w").write(max(cursor, prev) or time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
print("census: %d heads answered by the batch checker, %d rejected by check-proof, %d recent verdicts" % (len(done), len(rej), len(lines)))
PY
rm -rf "$T"
