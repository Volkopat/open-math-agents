#!/usr/bin/env bash
# Sends the credit ledger to the site: the lines credit.sh appended to $LEDGER_FILE (tools/ledger_entry.py, one per
# merged pull request) go to /api/ledger with the workflow's OIDC token. Started by the merger (tools/merger_loop.sh);
# trusted, never runs pull request code, and never in the way of the verdicts (it runs in the background).
#   ledger_post.sh once      the lines the site has not confirmed, with the 200 before them again (an upsert by pull
#                            request: a line posted twice changes nothing, and a write the site lost is repaired);
#                            with nothing new, the latest lines again every 15 minutes only
#   ledger_post.sh loop ID   "once" every 2 minutes, until another loop (a restarted merger) or the end of the job
#                            replaces ID in ledger_loop.id
# State next to $LEDGER_FILE: ledger.sent (lines confirmed), ledger.resent, ledger_loop.id.
set -uo pipefail
[ -n "${LEDGER_FILE:-}" ] || exit 0
D=$(dirname "$LEDGER_FILE")
if [ "${1:-once}" = loop ]; then
  while sleep 120; do
    [ "$(cat "$D/ledger_loop.id" 2>/dev/null)" = "${2:-}" ] || exit 0
    bash "$0" once   # the current version of this file (main is pulled every 2 minutes)
  done
fi
N=$(wc -l < "$LEDGER_FILE" 2>/dev/null || echo 0); S=$(cat "$D/ledger.sent" 2>/dev/null || echo 0); NOWS=$(date -u +%s)
[ "${N:-0}" -gt 0 ] 2>/dev/null || exit 0
[[ "$S" =~ ^[0-9]+$ ]] || S=0
if [ "$N" -le "$S" ] && [ $(( NOWS - $(cat "$D/ledger.resent" 2>/dev/null || echo 0) )) -lt 900 ]; then exit 0; fi
echo "$NOWS" > "$D/ledger.resent"
FROM=$(( S - 199 )); [ "$FROM" -lt 1 ] && FROM=1
TO=$(( FROM + 999 )); [ "$TO" -gt "$N" ] && TO=$N
OIDC=""
if [ -n "${ACTIONS_ID_TOKEN_REQUEST_URL:-}" ] && [ -n "${ACTIONS_ID_TOKEN_REQUEST_TOKEN:-}" ]; then
  OIDC=$(curl -sS -m 30 -H "Authorization: bearer $ACTIONS_ID_TOKEN_REQUEST_TOKEN" "$ACTIONS_ID_TOKEN_REQUEST_URL&audience=lefttosolve.com" | jq -r '.value // ""')
fi
sed -n "${FROM},${TO}p" "$LEDGER_FILE" | jq -cR 'fromjson? | select(type == "object")' \
  | jq -sc --arg oidc "$OIDC" '{oidc: $oidc, entries: .}' > "$D/ledger_post.json" || exit 0
OUT=$(curl -sS -m 60 -X POST "${OMA_SITE:-https://lefttosolve.com}/api/ledger" -H 'Content-Type: application/json' --data @"$D/ledger_post.json" 2>&1 | head -c 200)
echo "merger: ledger lines $FROM-$TO of $N: $OUT"
if printf '%s' "$OUT" | grep -qE '"ok": ?true' && [ "$TO" -gt "$S" ]; then echo "$TO" > "$D/ledger.sent"; fi
exit 0
