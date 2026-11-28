#!/usr/bin/env bash
# Batch checker: one runner restores the Lean tree once and checks many pull requests, each in its own sandbox.
# Runs in .github/workflows/batch-check.yml (on main, read-only token, no secrets). Trusted harness: this script, and
# the checker it runs (tools/check.sh, tools/lint.py, tools/prooflen.py), come from main; a pull request contributes
# its one Lean file and nothing else. Verdicts are those of check-proof.yml, step for step (same diff rule, same
# duplicate rule, same lint, same compile and axiom audit); the merger reads them from this job's artifact bv-<shard>
# (tools/batch_verdicts.sh) and gives them exactly as it gives a check-proof run's (tools/verdict_one.sh).
#
#   batch_check.sh worker     long-running (started in the background by the workflow): finds every open pull
#                             request of this shard whose head has no verdict yet (git ls-remote and git fetch: no API
#                             budget) and checks them, newest and oldest interleaved, LANES at a time (a Lean check
#                             uses about one core of the runner's four); see pick() for the order
#   batch_check.sh publish    one round: waits (bounded) for new verdicts and writes $BC/pub (the next step uploads it)
#   batch_check.sh stop       end of the job: no new check, running ones may finish, last publish
#   batch_check.sh once <pr>  check one pull request now and print the verdict (by hand; nothing is recorded)
#
# Each pull request is checked by tools/check.sh inside bubblewrap: no network, empty environment (no token), its own
# pid/ipc/uts/user namespaces, the toolchain, Mathlib and the repository read-only, a fresh writable copy of
# formal-conjectures (its sources and prebuilt libraries) that is thrown away afterwards, a private /tmp, and one output
# directory that only this harness reads. Nothing a check writes survives into another one. A check that fails to
# compile or runs out of time while others ran beside it is checked again alone before that verdict is given, so
# sharing the runner never turns a proof that passes alone into a rejection.
#
# Env: SHARD SHARDS (this job takes the files whose crc32 % SHARDS == SHARD), BC (work dir), WS (checkout of main:
# tools data reductions statements), OMA_FC, ELAN_HOME, BATCH_DEADLINE (unix time: no new check after it), LANES.
# State in $BC: done.tsv (pull request, head, time: verdict given, all shards), rej.tsv (heads check-proof rejected),
# verdicts.jsonl; the census job of the workflow gathers them from the previous run's artifacts.
set -uo pipefail
CMD="${1:-}"
BC="${BC:?}"; WS="${WS:?}"; SHARD="${SHARD:-0}"; SHARDS="${SHARDS:-1}"; LANES="${LANES:-2}"
mkdir -p "$BC/pub"
touch "$BC/done.tsv" "$BC/verdicts.jsonl" "$BC/rej.tsv"
log() { echo "$(date -u +%T) $*"; }

# ---- one check, in two parts -----------------------------------------------------------------------------------------
# prepare: everything that reads git (the diff rule, the duplicate rule, the tree the check will see). Runs in the
# worker itself, one at a time, never while main is being refreshed. Returns 0 with $W/verdict.json when that is the
# verdict already, 1 when the sandbox must decide ($W/file names the file).
prepare() {  # $1 work dir, $2 PR, $3 merge commit
  local W="$1" PR="$2" M="$3" ST F
  rm -rf "$W"; mkdir -p "$W/root" "$W/out"
  # Exactly one new file under proofs/, reductions/ or statements/ (check-proof.yml, same texts).
  git -C "$WS" diff --name-status "$M^1" "$M" > "$W/diff.txt" 2>/dev/null || { echo '{"verdict":"fault","reason":"could not read the pull request diff"}' > "$W/verdict.json"; return 0; }
  if [ "$(wc -l < "$W/diff.txt")" != "1" ]; then
    echo '{"verdict":"rejected","reason":"a pull request must add exactly one file under proofs/, reductions/ or statements/ and change nothing else"}' > "$W/verdict.json"; return 0
  fi
  read -r ST F < "$W/diff.txt"
  if ! printf '%s' "$F" | grep -Eq "^(proofs|reductions|statements)/[A-Za-z0-9_.'-]+\.lean$" || { [ "$ST" != "A" ] && ! { [ "$ST" = "M" ] && printf '%s' "$F" | grep -q '^proofs/'; }; }; then
    echo '{"verdict":"rejected","reason":"the one change must be a new file proofs/<id>.lean, reductions/<id>.R<n>.lean or statements/<id>.lean (letters, digits, _ . - only), or a shorter version of a proofs/<id>.lean already on main"}' > "$W/verdict.json"; return 0
  fi
  # The tree the check sees: main as it is now (hard links, read-only in the sandbox) plus the submitted file.
  cp -al "$WS/tools" "$WS/data" "$WS/reductions" "$WS/statements" "$W/root/"
  mkdir -p "$W/root/$(dirname "$F")"; rm -f "$W/root/$F"
  git -C "$WS" show "$M:$F" > "$W/root/$F" 2>/dev/null || { echo '{"verdict":"fault","reason":"could not read the submitted file"}' > "$W/verdict.json"; return 0; }
  # Already on main? (shortest-proof rule for a proof; anything else is turned away)
  if git -C "$WS" cat-file -e "HEAD:$F" 2>/dev/null; then
    if printf '%s' "$F" | grep -q '^proofs/'; then
      git -C "$WS" show "HEAD:$F" > "$W/old.lean"
      local RES NEW OLD; read -r RES NEW OLD < <(python3 -I "$WS/tools/prooflen.py" "$W/old.lean" "$W/root/$F")
      if [ "$RES" != shorter ]; then
        FILE="$F" NEW="$NEW" OLD="$OLD" OUTF="$W/verdict.json" python3 -I -c 'import json,os; json.dump({"verdict":"rejected","reason":"already proved: "+os.environ["FILE"]+" is on main. A new proof replaces it only if it is at least 5% and 20 characters shorter, comments and spaces not counted (yours: "+os.environ["NEW"]+", current: "+os.environ["OLD"]+"); otherwise take another problem"},open(os.environ["OUTF"],"w"))'
        return 0
      fi
    else
      FILE="$F" OUTF="$W/verdict.json" python3 -I -c 'import json,os; json.dump({"verdict":"rejected","reason":"already on main: "+os.environ["FILE"]+" (someone else'"'"'s was merged first); take another problem"},open(os.environ["OUTF"],"w"))'
      return 0
    fi
  fi
  printf '%s' "$F" > "$W/file"
  return 1
}

# sandbox: lint, compile and audit (tools/check.sh) in bubblewrap. formal-conjectures gets a fresh writable copy
# (sources and prebuilt libraries); Mathlib and the toolchain are bound read-only. Writes $W/verdict.json.
sandbox() {  # $1 work dir
  local W="$1" F FW RC; F=$(cat "$W/file"); FW="$W/up"; mkdir -p "$FW/.lake/packages"
  (cd "$OMA_FC" && tar --exclude=./.lake -cf - .) | tar -xf - -C "$FW"
  cp -a "$OMA_FC/.lake/build" "$FW/.lake/build"
  # Memory cap per check (a cgroup through systemd-run, where sudo allows it): one heavy proof is killed alone instead
  # of the whole runner (shards died with "The runner has received a shutdown signal", exit 143). Exit 137 = the cap.
  local CAP=()
  if [ -n "${CHECK_MEM:-}" ] && sudo -n true 2>/dev/null && command -v systemd-run > /dev/null; then
    CAP=(sudo -n systemd-run --quiet --scope -p "MemoryMax=$CHECK_MEM" -p MemorySwapMax=0 --uid="$(id -u)" --gid="$(id -g)" --)
    # probed once per job: if the runner cannot make the scope, checks run uncapped as before (never all faults)
    if [ ! -e "$BC/cap.ok" ] && [ ! -e "$BC/cap.no" ]; then
      if "${CAP[@]}" bwrap --unshare-all --die-with-parent --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/lib /lib \
          --symlink usr/lib64 /lib64 --proc /proc --dev /dev --tmpfs /tmp /usr/bin/true > /dev/null 2>&1; then touch "$BC/cap.ok"; log "memory cap $CHECK_MEM per check: on"
      else touch "$BC/cap.no"; log "memory cap: systemd-run scope unavailable, checks run uncapped"; fi
    fi
    [ -e "$BC/cap.ok" ] || CAP=()
  fi
  "${CAP[@]}" timeout -k 30 3400 bwrap --unshare-all --die-with-parent --new-session --clearenv \
    --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/sbin /sbin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
    --ro-bind /etc /etc --proc /proc --dev /dev --tmpfs /tmp \
    --ro-bind "$ELAN_HOME" "$ELAN_HOME" \
    --bind "$FW" "$OMA_FC" --ro-bind "$OMA_FC/.lake/packages" "$OMA_FC/.lake/packages" \
    --ro-bind "$W/root" /work/root --bind "$W/out" /work/out --chdir /work/root \
    --setenv PATH "$ELAN_HOME/bin:/usr/bin:/bin" --setenv HOME /tmp --setenv LANG C.UTF-8 \
    --setenv ELAN_HOME "$ELAN_HOME" --setenv OMA_FC "$OMA_FC" \
    bash tools/check.sh "$F" /work/out/verdict.json > "$W/sandbox.log" 2>&1
  RC=$?
  if [ -s "$W/out/verdict.json" ]; then cp "$W/out/verdict.json" "$W/verdict.json"
  elif [ "$RC" = 137 ] && [ "${#CAP[@]}" -gt 0 ]; then printf '{"verdict":"fault","reason":"checker produced no verdict: out of memory (over %s)"}' "$CHECK_MEM" > "$W/verdict.json"
  else printf '{"verdict":"fault","reason":"checker produced no verdict (exit %s)"}' "$RC" > "$W/verdict.json"; fi
  rm -rf "$FW"
}

# ---- record a verdict ------------------------------------------------------------------------------------------------
# Only the fields the merger reads, with their types checked; the pull request and commits come from here, never from
# the file a check wrote. A fault is retried (up to 3 checks) before it is published.
record() {  # $1 work dir, $2 PR, $3 merge, $4 head; sets RECORDED=1 once the verdict is kept for publishing
  local W="$1" PR="$2" M="$3" H="$4" OUT V; RECORDED=0
  OUT=$(PR="$PR" M="$M" H="$H" python3 -I - "$W/verdict.json" <<'PY'
import json, os, sys, time
try:
    d = json.load(open(sys.argv[1]))
    assert isinstance(d, dict)
except Exception:
    d = {"verdict": "fault", "reason": "unreadable verdict"}
v = d.get("verdict")
if v not in ("accepted", "rejected", "fault"):
    v, d["reason"] = "fault", "unknown verdict"
s = lambda k: d.get(k) if isinstance(d.get(k), str) else None
print(json.dumps({"pr": int(os.environ["PR"]), "head": os.environ["H"], "merge": os.environ["M"], "verdict": v,
                  "reason": (s("reason") or "")[:2000], "problem": s("problem"), "kind": s("kind"),
                  "polarity": s("polarity"), "t": int(time.time())}, ensure_ascii=False))
PY
)
  [ -n "$OUT" ] || return 0
  V=$(printf '%s' "$OUT" | python3 -I -c 'import json,sys;print(json.load(sys.stdin)["verdict"])')
  if [ "$V" = fault ]; then
    local T; T=$(( $(cat "$BC/tries.$PR.$H" 2>/dev/null || echo 0) + 1 )); echo "$T" > "$BC/tries.$PR.$H"
    if [ "$T" -lt 3 ]; then log "#$PR ${H:0:10}: fault (attempt $T), retried later: $(printf '%s' "$OUT" | head -c 300)"; return 0; fi
  fi
  printf '%s\n' "$OUT" >> "$BC/verdicts.jsonl"
  printf '%s\t%s\t%s\n' "$PR" "$H" "$(date -u +%s)" >> "$BC/done.tsv"; RECORDED=1
  log "#$PR ${H:0:10}: $V $(printf '%s' "$OUT" | python3 -I -c 'import json,sys;print(json.load(sys.stdin)["reason"][:120])')"
}

# did this check fail in a way that sharing the runner could have caused? (then it is checked again alone)
contended() {  # $1 work dir
  python3 -I -c 'import json,sys
try: d = json.load(open(sys.argv[1]))
except Exception: sys.exit(1)
r = d.get("reason") or ""
sys.exit(0 if d.get("verdict") in ("rejected", "fault") and (r.startswith("does not compile") or r.startswith("timeout") or r.startswith("compiler reported errors") or r.startswith("checker produced no verdict") or r.startswith("could not build")) else 1)' "$1/verdict.json"
}

# ---- what to check next ----------------------------------------------------------------------------------------------
# Every open pull request whose current head has no verdict yet: none from this checker (done.tsv, all shards) and no
# rejection by check-proof.yml (rej.tsv, from the census job). Pull requests are grouped by the one file they add or
# change; a group belongs to shard crc32(file) % SHARDS, and inside a group the oldest pull request is checked first and
# alone, so a later copy of the same proof is never answered (and merged) before an earlier one: the first solve stays
# with whoever filed first. Two picks in three take the group with the freshest head (new submissions are answered in
# minutes), the third the group with the oldest pull request (the backlog drains in filing order).

# describe(): for each open pull request's merge commit not described yet, one line of meta.tsv:
# merge, head, head commit time, number of changed paths, the path (when there is one), touches proofs/reductions/statements
describe() {
  awk 'FILENAME == ARGV[1] {seen[$1] = 1; next} !($3 in seen)' "$BC/meta.tsv" "$BC/open.txt" > "$BC/new.txt"
  [ -s "$BC/new.txt" ] || return 0
  # merge commits not held yet (refs are compared, not objects: asking a partial clone for a missing object fetches it)
  git -C "$WS" for-each-ref --format='%(refname:lstrip=3) %(objectname)' refs/oma/m/ > "$BC/fetched.txt"
  awk 'FILENAME == ARGV[1] {f[$1] = $2; next} f[$1] != $3 {print "+refs/pull/" $1 "/merge:refs/oma/m/" $1}' "$BC/fetched.txt" "$BC/new.txt" \
    | xargs -r -n 100 git -C "$WS" fetch -q --no-tags --depth 2 origin 2>/dev/null || true
  git -C "$WS" for-each-ref --format='%(refname:lstrip=3) %(objectname)' refs/oma/m/ > "$BC/fetched.txt"
  awk 'FILENAME == ARGV[1] {f[$1] = $2; next} f[$1] == $3 {print $3}' "$BC/fetched.txt" "$BC/new.txt" > "$BC/new_m.txt"
  [ -s "$BC/new_m.txt" ] || return 0
  git -C "$WS" log --no-walk=unsorted --stdin --format='%H %P' < "$BC/new_m.txt" > "$BC/new_parents.txt" 2>/dev/null
  awk 'NF == 3 {print $3}' "$BC/new_parents.txt" | git -C "$WS" log --no-walk=unsorted --stdin --format='%H %ct' > "$BC/new_times.txt" 2>/dev/null
  awk 'NF == 3 {print $1, $2}' "$BC/new_parents.txt" | git -C "$WS" diff-tree --stdin -r --name-status --no-renames > "$BC/new_diffs.txt" 2>/dev/null
  python3 -I - "$BC" <<'PY' >> "$BC/meta.tsv"
import os, re, sys
bc = sys.argv[1]
parents = {}
for line in open(os.path.join(bc, "new_parents.txt")):
    p = line.split()
    if len(p) == 3:
        parents[p[0]] = p[2]
times = dict(l.split() for l in open(os.path.join(bc, "new_times.txt")) if len(l.split()) == 2)
paths, cur = {}, None
for line in open(os.path.join(bc, "new_diffs.txt")):
    line = line.rstrip("\n")
    if re.fullmatch(r"[0-9a-f]{40}( [0-9a-f]{40})*", line):
        cur = line.split()[0]; paths.setdefault(cur, [])
    elif cur and "\t" in line:
        paths[cur].append(line.split("\t")[-1])
for m, h in parents.items():
    if m not in paths or h not in times:
        continue
    ps = paths[m]
    touch = any(re.match(r"(proofs|reductions|statements)/", x) for x in ps)
    print("\t".join([m, h, times[h], str(len(ps)), ps[0] if len(ps) == 1 else "", "1" if touch else "0"]))
PY
}

# pick(): the next pull request for this shard, or nothing
pick() {  # $1 pick counter
  printf '%s\n' "${LANE_ITEM[@]}" | awk 'NF {print $1}' > "$BC/running.txt"
  python3 -I - "$BC" "$SHARD" "$SHARDS" "$1" <<'PY'
import os, sys, zlib
bc, shard, shards, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
def rows(name, k):
    path = os.path.join(bc, name)
    if not os.path.exists(path):
        return []
    return [l.rstrip("\n").split("\t") if "\t" in l else l.split() for l in open(path) if len(l.split()) >= k]
meta = {r[0]: r for r in rows("meta.tsv", 4)}
done = {(r[0], r[1]) for r in rows("done.tsv", 2)} | {(r[0], r[1]) for r in rows("rej.tsv", 2)}
running = {r[0] for r in rows("running.txt", 1)}
groups = {}
for p, h, m in rows("open.txt", 3):
    d = meta.get(m)
    if not d or d[1] != h or d[5] != "1" or (p, h) in done:
        continue   # not described yet, merge ref older than the head, no submission, or already answered
    key = d[4] if d[3] == "1" else "#" + p
    if zlib.crc32(key.encode()) % shards != shard:
        continue
    groups.setdefault(key, []).append((int(p), h, m, int(d[2])))
cands = []
for key, items in groups.items():
    if any(str(i[0]) in running for i in items):
        continue   # one check per file at a time
    items.sort()
    p, h, m, _ = items[0]
    cands.append((max(i[3] for i in items), p, h, m))
if cands:
    c = min(cands, key=lambda c: c[1]) if n % 3 == 2 else max(cands, key=lambda c: (c[0], -c[1]))
    print(c[1], c[2], c[3])
PY
}

# ---- the worker loop -------------------------------------------------------------------------------------------------
worker() {
  declare -A LANE_ITEM=() LANE_PID=() LANE_T0=()
  local LAST_MAIN=0 LAST_REFS=0 SOLO="" L PICKS=0
  touch "$BC/meta.tsv" "$BC/rej.tsv"
  log "worker: shard $SHARD of $SHARDS, $LANES lanes; $(wc -l < "$BC/done.tsv") heads answered by this checker and $(wc -l < "$BC/rej.tsv") rejected by check-proof are not checked again"
  busy() { local n=0 l; for l in "${!LANE_PID[@]}"; do n=$((n + 1)); done; echo "$n"; }
  finish() {  # $1 lane: its check ended
    local L="$1" P H M W="$BC/w$1"; read -r P H M <<< "${LANE_ITEM[$1]}"
    if [ "$LANES" -gt 1 ] && contended "$W"; then
      SOLO="$P $H $M"; log "#$P ${H:0:10}: $(python3 -I -c 'import json,sys;print(json.load(open(sys.argv[1])).get("reason","")[:60])' "$W/verdict.json") beside other checks: checked again alone"
    else
      record "$W" "$P" "$M" "$H"
      log "#$P checked in $(( $(date -u +%s) - ${LANE_T0[$1]:-0} )) s"
    fi
    unset "LANE_ITEM[$1]" "LANE_PID[$1]" "LANE_T0[$1]"
  }
  while :; do
    # collect the lanes whose check ended
    for L in "${!LANE_PID[@]}"; do kill -0 "${LANE_PID[$L]}" 2>/dev/null || { wait "${LANE_PID[$L]}" 2>/dev/null; finish "$L"; }; done
    if [ "$(date -u +%s)" -ge "$BATCH_DEADLINE" ] || [ -e "$BC/stop" ]; then
      [ "$(busy)" = 0 ] && break; sleep 2; continue
    fi
    # a check to repeat alone: wait until the runner is free, then run it in the foreground
    if [ -n "$SOLO" ]; then
      [ "$(busy)" = 0 ] || { sleep 2; continue; }
      local P H M; read -r P H M <<< "$SOLO"; SOLO=""
      local T0; T0=$(date -u +%s)
      LANE_ITEM[0]="$P $H $M"
      prepare "$BC/w0" "$P" "$M" || sandbox "$BC/w0"
      record "$BC/w0" "$P" "$M" "$H"; unset "LANE_ITEM[0]"
      log "#$P checked alone in $(( $(date -u +%s) - T0 )) s"; continue
    fi
    if [ "$(busy)" -ge "$LANES" ]; then sleep 2; continue; fi
    local NOW; NOW=$(date -u +%s)
    # main as it is now, at most every 2 minutes, only while no check is being prepared (they read it)
    if [ $(( NOW - LAST_MAIN )) -ge 120 ]; then
      git -C "$WS" fetch -q --depth 1 origin main 2>/dev/null && git -C "$WS" checkout -q -f FETCH_HEAD 2>/dev/null && LAST_MAIN=$NOW
    fi
    # open pull requests (GitHub keeps refs/pull/<n>/merge only while a pull request is open and mergeable), at most
    # every 15 seconds
    if [ $(( NOW - LAST_REFS )) -ge 15 ]; then
      LAST_REFS=$NOW
      if git -C "$WS" ls-remote origin 'refs/pull/*/head' 'refs/pull/*/merge' > "$BC/refs.txt" 2>/dev/null; then
        awk '{split($2, a, "/"); if (a[4] == "head") h[a[3]] = $1; else m[a[3]] = $1} END {for (p in m) if (p in h) print p, h[p], m[p]}' \
          "$BC/refs.txt" | sort -n > "$BC/open.txt"
        describe
      fi
    fi
    local PICK P H M
    PICK=$(pick "$PICKS")
    if [ -z "$PICK" ]; then sleep 5; continue; fi
    PICKS=$(( PICKS + 1 ))
    read -r P H M <<< "$PICK"
    # a free lane
    for L in $(seq 1 "$LANES"); do [ -z "${LANE_PID[$L]:-}" ] && break; done
    LANE_T0[$L]=$(date -u +%s); LANE_ITEM[$L]="$P $H $M"
    if prepare "$BC/w$L" "$P" "$M"; then
      record "$BC/w$L" "$P" "$M" "$H"
      log "#$P decided before compiling"; unset "LANE_ITEM[$L]" "LANE_T0[$L]"; continue
    fi
    sandbox "$BC/w$L" & LANE_PID[$L]=$!
  done
  log "worker: stopped"
  touch "$BC/worker.done"
}

# ---- publishing ------------------------------------------------------------------------------------------------------
# pub/verdicts.jsonl: every verdict of the last 3 hours (this job's and the ones it inherited), so a merger that was
# slow to read one round still finds them in the next; pub/done.tsv: what the next job of this shard must not redo.
publish_now() {
  python3 -I - "$BC" <<'PY'
import json, os, sys, time
bc = sys.argv[1]; now = time.time(); keep = []; n = 0
for line in open(os.path.join(bc, "verdicts.jsonl"), encoding="utf-8"):
    if not line.endswith("\n"):
        break   # being written: the next round takes it
    n += 1
    try:
        d = json.loads(line)
    except Exception:
        continue
    if now - d.get("t", 0) <= 10800:
        keep.append(line)
open(os.path.join(bc, "pub", "verdicts.jsonl"), "w", encoding="utf-8").writelines(keep)
# heads answered, kept while their pull request is open (a rejected one can stay open for days)
openp = None
if os.path.exists(os.path.join(bc, "open.txt")):
    openp = {l.split()[0] for l in open(os.path.join(bc, "open.txt")) if l.split()}
rows = {}
for line in open(os.path.join(bc, "done.tsv")):
    p = line.rstrip("\n").split("\t")
    if len(p) >= 3 and p[2].isdigit() and (openp is None or not openp or p[0] in openp):
        rows[(p[0], p[1])] = p[2]
with open(os.path.join(bc, "pub", "done.tsv"), "w") as f:
    for (a, b), t in rows.items():
        f.write(f"{a}\t{b}\t{t}\n")
open(os.path.join(bc, "published.count"), "w").write("%d\n" % n)
PY
  [ -n "${GITHUB_ENV:-}" ] && echo "BV_CHANGED=1" >> "$GITHUB_ENV"
  log "published $(wc -l < "$BC/pub/verdicts.jsonl") verdicts"
}
publish() {  # one round: new verdicts go out at most once a minute; a round waits at most PUBLISH_WAIT seconds
  [ -n "${GITHUB_ENV:-}" ] && echo "BV_CHANGED=0" >> "$GITHUB_ENV"
  local START; START=$(date -u +%s)
  while :; do
    local N P NOW LASTP; N=$(wc -l < "$BC/verdicts.jsonl"); P=$(cat "$BC/published.count" 2>/dev/null || echo 0)
    NOW=$(date -u +%s); LASTP=$(stat -c %Y "$BC/published.count" 2>/dev/null || echo 0)
    if [ "$N" -gt "$P" ] && { [ $(( NOW - LASTP )) -ge "${PUBLISH_EVERY:-60}" ] || [ -e "$BC/worker.done" ] || [ $(( NOW - START )) -ge "${PUBLISH_WAIT:-120}" ]; }; then
      publish_now; break
    fi
    if [ -e "$BC/worker.done" ] || [ $(( NOW - START )) -ge "${PUBLISH_WAIT:-120}" ]; then break; fi
    sleep 5
  done
  tail -n 3 "$BC/worker.log" 2>/dev/null || true
  # what killed shards before: memory and disk, visible in every round's log
  echo "mem: $(free -m | awk '/^Mem:/ {print $3 " MB used, " $7 " MB available"}') · disk: $(df -h /mnt 2>/dev/null | awk 'NR==2 {print $4 " free on /mnt"}'), $(df -h / | awk 'NR==2 {print $4 " free on /"}')"
}
stop() {
  touch "$BC/stop"
  local I; for I in $(seq 1 "${STOP_WAIT:-600}"); do [ -e "$BC/worker.done" ] && break; sleep 1; done
  publish_now
  echo "--- worker log (last 40 lines)"; tail -n 40 "$BC/worker.log" 2>/dev/null || true
}

once() {  # $1 PR
  local P="$1" M H
  git -C "$WS" fetch -q --no-tags --depth 2 origin "+refs/pull/$P/merge:refs/oma/m/$P" || { echo "no merge ref for #$P" >&2; return 1; }
  M=$(git -C "$WS" rev-parse "refs/oma/m/$P"); H=$(git -C "$WS" rev-parse "$M^2")
  prepare "$BC/w0" "$P" "$M" || sandbox "$BC/w0"
  python3 -I -c 'import json,sys;d=json.load(open(sys.argv[1]));d.pop("log",None);print(json.dumps(d))' "$BC/w0/verdict.json"
}

case "$CMD" in
  worker) worker ;;
  once) once "${2:?pull request number}" ;;
  publish) publish ;;
  stop) stop ;;
  *) echo "usage: batch_check.sh worker|publish|stop|once <pr>" >&2; exit 2 ;;
esac
