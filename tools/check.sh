#!/usr/bin/env bash
# Compile one submitted proof against the pinned formal-conjectures and audit its axioms.
# Usage: tools/check.sh proofs/<id>.lean [verdict.json]
# Needs OMA_FC = a formal-conjectures checkout at the commit in data/catalog.json, with the Mathlib cache.
set -uo pipefail
FILE="$1"
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The verdict path is made absolute now: the script later moves into the formal-conjectures checkout, and a relative
# path would land the verdict there instead of where the caller looks for it.
if [ -n "${2:-}" ]; then OUT="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"; else OUT=/dev/stdout; fi
FC="${OMA_FC:-$ROOT/.oma/formal-conjectures}"
LINT="$(python3 -I "$ROOT/tools/lint.py" "$FILE" "$ROOT/data/catalog.json")"; LINT_OK=$?
# Only the end of the log is kept, and it is cut here: one argument may not exceed 128 KB, and a long compiler log used
# to make python fail to start, leaving an empty verdict ("checker produced no verdict") for a proof that just failed.
emit() { local L="${3:-}"; [ "${#L}" -le 6000 ] || L="${L: -6000}"
  python3 -I -c 'import json,sys; d=json.loads(sys.argv[1]); d.update(verdict=sys.argv[2], reason=sys.argv[3], log=sys.argv[4][-6000:]); print(json.dumps(d, ensure_ascii=False))' "$LINT" "$1" "$2" "$L" > "$OUT"; }
if [ $LINT_OK -ne 0 ]; then emit rejected "lint: $(python3 -I -c 'import json,sys;print("; ".join(json.loads(sys.argv[1])["errors"]))' "$LINT")"; exit 1; fi
field() { python3 -I -c 'import json,sys;print(json.loads(sys.argv[1])[sys.argv[2]])' "$LINT" "$1"; }
MODULE="$(field imports)"; THM="$(field theorem)"
WANT="$(python3 -I -c 'import json;print(json.load(open("'"$ROOT"'/data/catalog.json"))["meta"]["upstreamCommit"])')"
HAVE="$(git -C "$FC" rev-parse HEAD 2>/dev/null || echo none)"
[ "$HAVE" = "$WANT" ] || { emit fault "formal-conjectures checkout is at $HAVE, expected $WANT (run tools/oma.sh setup)"; exit 2; }
cd "$FC"
# Merged reductions become the Lean library OMAReductions, so steps (and reductions of steps) can import them.
if [ -d "$ROOT/reductions" ]; then
  mkdir -p OMAReductions
  for R in "$ROOT"/reductions/*.lean; do
    [ -e "$R" ] || continue
    ID="$(basename "$R" .lean)"
    cp "$R" "OMAReductions/R_$(printf '%s' "$ID" | sed 's/[^A-Za-z0-9]/_/g').lean"
  done
  grep -q 'name = "OMAReductions"' lakefile.toml || printf '\n[[lean_lib]]\nname = "OMAReductions"\nglobs = ["OMAReductions.+"]\n' >> lakefile.toml
fi
# Merged statements (problems first stated here) become the Lean library OMAStatements.
if [ -d "$ROOT/statements" ]; then
  mkdir -p OMAStatements
  for S in "$ROOT"/statements/*.lean; do
    [ -e "$S" ] || continue
    ID="$(basename "$S" .lean)"
    cp "$S" "OMAStatements/S_$(printf '%s' "$ID" | sed 's/[^A-Za-z0-9]/_/g').lean"
  done
  grep -q 'name = "OMAStatements"' lakefile.toml || printf '\n[[lean_lib]]\nname = "OMAStatements"\nglobs = ["OMAStatements.+"]\n' >> lakefile.toml
fi
TYPE="$(field type)"
if [ "$MODULE" != "Mathlib" ]; then
  # Builds only what the submission imports: one problem file, or a chain of merged reductions (seconds to a few
  # minutes when formal-conjectures' libraries come prebuilt, as in CI). 20 minutes, so that with the 30 for the
  # submission itself a check ends with a verdict inside its job's 60-minute limit.
  LOG="$(timeout 1200 lake build "$MODULE" 2>&1)" || { emit fault "could not build imported module $MODULE" "$LOG"; exit 2; }
fi
SUB="OMASubmission_$$.lean"
# A problem that asks for a value: audit with the placeholder's value skipped (tools/oma_audit.lean).
SKIP="$(python3 -I -c 'import json,sys;print(" ".join(json.loads(sys.argv[1]).get("skipAxiomsOf") or []))' "$LINT")"
# Statement guard. `theorem OMA.solution : type_of% @X` elaborates with namespace OMA open, so a file that also
# declared its own OMA.X (or, in a reduction, a lemma named X inside its namespace) would prove that instead of the
# catalogue's statement and still pass the axiom audit. This line, appended after the file, re-states the expected
# type with every name taken from the root namespace and checks the submitted theorem against it: if the file proved
# anything else, the file does not compile. (Reported privately by Ryan of Sentria, 28 Nov 2026.)
GUARD="$(python3 -I -c '
import json, sys
d = json.loads(sys.argv[1]); t = d.get("target") or ""; th = d.get("theorem") or ""; ty = d.get("type")
if not t or not th or ty == "statement":
    sys.exit()
root = ("type_of% @_root_." + t[len("type_of% @"):]) if t.startswith("type_of% @") else ("_root_." + t)
if ty == "reduction":
    ns = th[: -len(".main")]
    chain = "".join("_root_.%s.H%d → " % (ns, i) for i in range(1, len(d.get("hypotheses") or []) + 1))
    print("example : %s%s := _root_.%s" % (chain, root, th))
elif d.get("skipAxiomsOf"):
    print("example : _root_.%s = _root_.OMA.answer → %s := _root_.%s" % (d["skipAxiomsOf"][0], root, th))
elif th.endswith(".disproof"):
    print("example : ¬ (%s) := _root_.%s" % (root, th))
else:
    print("example : %s := _root_.%s" % (root, th))
' "$LINT")"
if [ -n "$SKIP" ]; then
  { cat "$ROOT/$FILE" 2>/dev/null || cat "$FILE"; printf '\n%s\n' "$GUARD"; cat "$ROOT/tools/oma_audit.lean"; printf '\n#oma_axioms %s skipping %s\n' "$THM" "$SKIP"; } > "$SUB"
else
  { cat "$ROOT/$FILE" 2>/dev/null || cat "$FILE"; printf '\n%s\n#print axioms %s\n' "$GUARD" "$THM"; } > "$SUB"
fi
LOG="$(timeout 1800 lake env lean "$SUB" 2>&1)"; RC=$?
rm -f "$SUB"
[ $RC -eq 124 ] && { emit rejected "timeout: over 30 minutes" "$LOG"; exit 1; }
[ $RC -ne 0 ] && { emit rejected "does not compile" "$LOG"; exit 1; }
if [ "$TYPE" = "statement" ]; then
  # A statement keeps exactly one sorry (the body of main); the only question a machine can answer is
  # whether it elaborates. Whether it says what the problem says is decided by a person.
  if echo "$LOG" | grep -qE "(^|:)[0-9]+:[0-9]+: error"; then emit rejected "compiler reported errors" "$LOG"; exit 1; fi
  emit accepted "the statement compiles; it now needs a human review of the translation" "$LOG"; exit 0
fi
AX="$(python3 -I - "$LOG" "$THM" <<'PY'
import re, sys
log, thm = sys.argv[1], sys.argv[2]
if re.search(r"'%s' does not depend on any axioms" % re.escape(thm), log):
    print("OK"); sys.exit()
m = re.search(r"'%s' depends on axioms: \[(.*?)\]" % re.escape(thm), log, re.S)
if not m:
    print("NOAX"); sys.exit()
ax = {a.strip() for a in m.group(1).replace("\n", " ").split(",") if a.strip()}
bad = ax - {"propext", "Classical.choice", "Quot.sound"}
print("OK" if not bad else "BAD " + ", ".join(sorted(bad)))
PY
)"
if echo "$LOG" | grep -qE "(^|:)[0-9]+:[0-9]+: error"; then emit rejected "compiler reported errors" "$LOG"; exit 1; fi
case "$AX" in
  OK) emit accepted "kernel accepted; axioms within propext, Classical.choice, Quot.sound" "$LOG"; exit 0 ;;
  NOAX) emit rejected "no axiom report for $THM" "$LOG"; exit 1 ;;
  *) emit rejected "uses forbidden axioms: ${AX#BAD }" "$LOG"; exit 1 ;;
esac
