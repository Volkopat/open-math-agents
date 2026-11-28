#!/usr/bin/env bash
# Merger side of the batch checker (batch-check.yml, tools/batch_check.sh). Called by tools/merger_loop.sh every 90 s at
# most; prints the batch verdicts not given yet as queue lines (id, head, attempt, url, updated, conclusion, title,
# mode "batch") and prepares batch/<id>/pr.txt and verdict.json for verdict(), which hands them to
# tools/verdict_one.sh exactly like a check-proof run's artifact (same diff re-check, trusted re-lint, comment, merge).
# Trusted: never runs pull request code. Artifacts are read only from runs of .github/workflows/batch-check.yml on
# main started by a schedule, a dispatch or a push: an artifact of the same name uploaded by a pull request's run
# (which runs whatever workflow the pull request brings) is never read.
# API: one call per pass, one per new artifact, one per new batch run; every 10 minutes one per shard.
# Needs: ROOT (the merger's directory), REPO, GH_TOKEN, FLOOR (unix time: older verdicts are not this merger's),
# START (unix time the merger started).
set -uo pipefail
D="$ROOT/batchv"; mkdir -p "$D/runs" "$D/art"
SHARDS=$(sed -n 's/^SHARDS = \([0-9][0-9]*\).*/\1/p' "$ROOT/base/tools/batch_check_yml.py" 2>/dev/null); SHARDS=${SHARDS:-8}
JQ='.artifacts[] | select(.name | test("^bv-[0-9]+$")) | select(.expired | not) | [.id, .name, .workflow_run.id] | @tsv'
gh api "repos/$REPO/actions/artifacts?per_page=100" --jq "$JQ" > "$D/list.tsv" 2>/dev/null || : > "$D/list.tsv"
# every 10 minutes, the newest of each shard by name: the newest 100 artifacts of the repository span only a few minutes
if [ $(( $(date -u +%s) - $(cat "$D/last_full" 2>/dev/null || echo 0) )) -ge 600 ]; then
  date -u +%s > "$D/last_full"
  for K in $(seq 0 $(( SHARDS - 1 ))); do
    gh api "repos/$REPO/actions/artifacts?name=bv-$K&per_page=3" --jq "$JQ" >> "$D/list.tsv" 2>/dev/null || true
  done
fi
# the newest artifact of each name (ids grow); bv-<k> is overwritten by every round, so the newest holds the rest
sort -t$'\t' -k1,1nr "$D/list.tsv" | awk -F'\t' 'NF >= 3 && !seen[$2]++' > "$D/newest.tsv"
while IFS=$'\t' read -r AID NAME RID; do
  case "$AID$RID" in *[!0-9]*|'') continue ;; esac
  if [ ! -e "$D/runs/$RID" ]; then
    gh api "repos/$REPO/actions/runs/$RID" --jq 'select(.path == ".github/workflows/batch-check.yml" and .head_branch == "main" and (.event == "schedule" or .event == "workflow_dispatch" or .event == "push") and .repository.full_name == .head_repository.full_name) | .html_url' > "$D/runs/$RID.tmp" 2>/dev/null \
      && mv "$D/runs/$RID.tmp" "$D/runs/$RID"   # an empty file: not a trusted run (kept, so it is asked once)
  fi
  [ -s "$D/runs/$RID" ] || continue
  if [ ! -e "$D/art/$AID.jsonl" ]; then
    rm -f "$D/a.zip"
    gh api "repos/$REPO/actions/artifacts/$AID/zip" > "$D/a.zip" 2>/dev/null && unzip -p "$D/a.zip" verdicts.jsonl > "$D/art/$AID.tmp" 2>/dev/null \
      && mv "$D/art/$AID.tmp" "$D/art/$AID.jsonl" || continue
  fi
  printf '%s\t%s\n' "$AID" "$(cat "$D/runs/$RID")" > "$D/cur.$NAME"
done < "$D/newest.tsv"
ls "$D"/cur.bv-* >/dev/null 2>&1 || exit 0
# open pull requests and their heads (git, no API): a verdict for a closed pull request or an older head is dropped
git ls-remote "https://github.com/$REPO" 'refs/pull/*/head' 'refs/pull/*/merge' > "$D/refs.txt" 2>/dev/null || : > "$D/refs.txt"
python3 -I - "$D" "$ROOT" "${FLOOR:-0}" "${START:-0}" <<'PY'
import datetime, glob, json, os, re, sys
d, root, floor, start = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
head, merge = {}, {}
for line in open(os.path.join(d, "refs.txt")):
    m = re.fullmatch(r"([0-9a-f]{40})\trefs/pull/(\d+)/(head|merge)", line.strip())
    if m:
        (head if m.group(3) == "head" else merge)[int(m.group(2))] = m.group(1)
check_refs = bool(head)
for cur in sorted(glob.glob(os.path.join(d, "cur.bv-*"))):
    aid, url = open(cur).read().strip().split("\t", 1)
    if not re.fullmatch(r"https://github\.com/[\w.-]+/[\w.-]+/actions/runs/\d+", url):
        continue
    for line in open(os.path.join(d, "art", aid + ".jsonl"), encoding="utf-8"):
        try:
            v = json.loads(line)
            pr, h, t, verdict = int(v["pr"]), str(v["head"]), int(v["t"]), v["verdict"]
        except Exception:
            continue
        if not re.fullmatch(r"[0-9a-f]{40}", h) or verdict not in ("accepted", "rejected", "fault") or t < floor:
            continue
        if check_refs and head.get(pr) != h:
            continue   # updated since: nothing to say about this head
        if check_refs and pr not in merge and t < start:
            continue   # given before this merger started and merged or closed since (or in conflict): not again
        vid = "b%d-%s" % (pr, h[:12])
        if os.path.exists(os.path.join(root, "done", vid + ".3")):
            continue
        w = os.path.join(root, "batch", vid); os.makedirs(w, exist_ok=True)
        open(os.path.join(w, "pr.txt"), "w").write("%d\n" % pr)
        json.dump({k: v.get(k) for k in ("verdict", "reason", "problem", "kind", "polarity")}, open(os.path.join(w, "verdict.json"), "w"))
        when = datetime.datetime.fromtimestamp(t, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
        # attempt 3: a fault (published after 3 failed checks) is never answered by re-running the batch run.
        # The url names the pull request and head, so an earlier verdict of the same run for another head of the same
        # pull request is not taken for this one by the merger's "already reported" check.
        print("\t".join([vid, h, "3", "%s#pr-%d-%s" % (url, pr, h[:12]), when, "success" if verdict == "accepted" else "failure", "batch #%d" % pr, "batch"]))
PY
