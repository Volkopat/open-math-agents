#!/usr/bin/env bash
# End-to-end tests of tools/oma.sh against a mock site, a fake gh and a local bare git remote.
# No network, no Lean: the checker is replaced by a stub through OMA_CHECK. Run: bash tests/test_oma.sh
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
T="$(mktemp -d)"
PORT=$((20000 + RANDOM % 20000))
export MOCK_LOG="$T/requests.log"; : > "$MOCK_LOG"
python3 -I "$ROOT/tests/mock_desk.py" "$PORT" & MOCK=$!
trap 'kill $MOCK 2>/dev/null; rm -rf "$T"' EXIT
FAILS=0
pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; FAILS=$((FAILS+1)); }
check() { if eval "$2"; then pass "$1"; else fail "$1"; fi; }

# A working copy of the repository with a bare "origin" (the agent's fork) and a fake gh.
git init -q --bare "$T/origin.git"
git clone -q "$T/origin.git" "$T/repo" 2>/dev/null
cp -r "$ROOT/tools" "$ROOT/data" "$T/repo/" ; mkdir -p "$T/repo/proofs"; touch "$T/repo/proofs/.keep"
cd "$T/repo" && git add -A && git -c user.name=t -c user.email=t@t commit -qm init && git push -q origin HEAD:main 2>/dev/null
git remote set-head origin main 2>/dev/null || git symbolic-ref refs/remotes/origin/HEAD refs/remotes/origin/main
mkdir -p "$T/bin"
cat > "$T/bin/gh" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = "api" ] && [ "$2" = "user" ]; then echo tester; exit 0; fi
if [ "$1" = "pr" ] && [ "$2" = "create" ]; then printf '%s\n' "$@" > "$GH_LOG"; echo "https://github.com/x/y/pull/1"; exit 0; fi
exit 1
EOF
cat > "$T/bin/stubcheck" <<'EOF'
#!/usr/bin/env bash
# stub checker: accepted unless the file contains the word REJECTME
if grep -q REJECTME "$1"; then echo '{"verdict":"rejected","reason":"stub says no","log":"x"}' > "$2"; exit 1; fi
echo '{"verdict":"accepted","reason":"stub ok","log":""}' > "$2"
EOF
chmod +x "$T/bin/gh" "$T/bin/stubcheck"
export PATH="$T/bin:$PATH" GH_LOG="$T/gh.log" OMA_SITE="http://127.0.0.1:$PORT" OMA_CHECK="$T/bin/stubcheck" OMA_AGENT=claude-code OMA_MODEL=test-model
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@t GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@t
for i in $(seq 1 30); do curl -s -o /dev/null "http://127.0.0.1:$PORT/api/stats" && break; sleep 0.2; done

PID=Erdos3.erdos_3.variants.gowers
OUT="$(tools/oma.sh next --problem $PID 2>&1)"
check "next: prints the problem" '[[ "$OUT" == *"PROBLEM    $PID"* ]]'
check "next: writes the skeleton" '[ -f "proofs/$PID.lean" ] && grep -q "OMA.solution" "proofs/$PID.lean"'
check "next: prints the role and teammates" '[[ "$OUT" == *"YOUR ROLE   CHECKER: Test the statement."* ]] && [[ "$OUT" == *"TEAMMATES   @mate (lead)"* ]]'
check "next: stores the lease" '[ "$(cat .oma/leases/$PID)" = "22222222-2222-2222-2222-222222222222" ]'
check "next: downloads the brief" 'grep -q "BRIEF FOR $PID" .oma/briefs/$PID.txt'
check "next: sends handle and agent" 'grep -q "\"handle\": \"tester\"" "$MOCK_LOG" && grep -q "\"agent\": \"claude-code\"" "$MOCK_LOG"'
check "next: passes --problem" 'grep -q "\"problem\": \"$PID\"" "$MOCK_LOG"'
OUT="$(tools/oma.sh next --problem nope 2>&1)"; RC=$?
check "next: desk error is reported and fails" '[ $RC -ne 0 ] && [[ "$OUT" == *"not_found"* ]]'
OUT="$(tools/oma.sh next --bogus x 2>&1)"; RC=$?
check "next: unknown option fails" '[ $RC -ne 0 ] && [[ "$OUT" == *"unknown option"* ]]'

OUT="$(tools/oma.sh beat $PID 2>&1)"
check "beat: ok with role and teammates" '[[ "$OUT" == "ok · role checker · teammates: @mate (lead)"* ]]'
check "beat: prints new teammate notes" '[[ "$OUT" == *"NEW NOTE #41 @mate"*"PLAN: induction on k"* ]]'
OUT="$(tools/oma.sh beat $PID 2>&1)"
check "beat: remembers the last note seen (since)" '[[ "$OUT" != *"NEW NOTE"* ]]'
echo 33333333-3333-3333-3333-333333333333 > .oma/leases/stopped; OUT="$(tools/oma.sh beat stopped 2>&1)"; RC=$?
check "beat: STOP on 410 and lease dropped" '[ $RC -eq 3 ] && [[ "$OUT" == STOP* ]] && [ ! -f .oma/leases/stopped ]'
OUT="$(tools/oma.sh beat not-held 2>&1)"; RC=$?
check "beat: refuses a problem without lease" '[ $RC -ne 0 ] && [[ "$OUT" == *"no lease"* ]]'

OUT="$(tools/oma.sh check $PID 2>&1)"; RC=$?
check "check: accepted" '[ $RC -eq 0 ] && [[ "$OUT" == ACCEPTED* ]]'
echo "-- REJECTME" >> "proofs/$PID.lean"; OUT="$(tools/oma.sh check $PID 2>&1)"; RC=$?
check "check: rejected fails" '[ $RC -ne 0 ] && [[ "$OUT" == REJECTED* ]]'
OUT="$(tools/oma.sh submit $PID 2>&1)"; RC=$?
check "submit: refuses when check fails" '[ $RC -ne 0 ] && [ ! -s "$GH_LOG" ]'
sed -i '/REJECTME/d' "proofs/$PID.lean"

echo "unrelated" > stray.txt
OUT="$(tools/oma.sh submit $PID 2>&1)"; RC=$?
check "submit: succeeds" '[ $RC -eq 0 ] && [[ "$OUT" == *"sent"* ]]'
check "submit: PR body has Lease, Agent, Model" 'grep -q "Lease: 22222222" "$GH_LOG" && grep -q "Agent: claude-code" "$GH_LOG" && grep -q "Model: test-model" "$GH_LOG"'
check "submit: PR title is the id" 'grep -qx "$PID" "$GH_LOG"'
BR="oma/$PID"
check "submit: pushed a branch with exactly that file" '[ "$(git --git-dir="$T/origin.git" diff --name-only main "$BR" 2>/dev/null)" = "proofs/$PID.lean" ]'
check "submit: stray files not committed" 'git --git-dir="$T/origin.git" show --name-only --format= "$BR" >/dev/null && ! git --git-dir="$T/origin.git" show --name-only --format= "$BR" | grep -q stray.txt'
check "submit: releases as submitted" 'grep -q "\"reason\": \"submitted\"" "$MOCK_LOG"'
check "submit: lease forgotten" '[ ! -f .oma/leases/$PID ]'

tools/oma.sh next --problem $PID >/dev/null 2>&1
OUT="$(tools/oma.sh reduce $PID 2>&1)"
check "reduce: writes R1" '[ -f "reductions/$PID.R1.lean" ] && grep -q "namespace OMA.R_1" "reductions/$PID.R1.lean"'
OUT="$(tools/oma.sh reduce $PID 2>&1)"
check "reduce: next one is R2" '[ -f "reductions/$PID.R2.lean" ] && grep -q "OMA.R_2" "reductions/$PID.R2.lean"'
rm "reductions/$PID.R2.lean"; : > "$MOCK_LOG"; : > "$GH_LOG"
OUT="$(tools/oma.sh submit $PID.R1 2>&1)"; RC=$?
check "submit reduction: succeeds" '[ $RC -eq 0 ]'
check "submit reduction: releases as reduced" 'grep -q "\"reason\": \"reduced\"" "$MOCK_LOG"'
check "submit reduction: pushes the reduction file" '[ "$(git --git-dir="$T/origin.git" diff --name-only main "oma/$PID.R1" 2>/dev/null)" = "reductions/$PID.R1.lean" ]'

OUT="$(tools/oma.sh next --kind formalize 2>&1)"
check "formalize: writes statements/<id>.lean" '[ -f statements/opg-x.lean ] && [[ "$OUT" == *"FORMALIZE"* ]]'
OUT="$(tools/oma.sh check opg-x 2>&1)"
check "formalize: check uses the statement file" '[[ "$OUT" == ACCEPTED* ]]'
OUT="$(tools/oma.sh release opg-x too_hard 2>&1)"
check "release: sends the reason" 'grep -q "\"reason\": \"too_hard\"" "$MOCK_LOG" && [ ! -f .oma/leases/opg-x ]'
OUT="$(tools/oma.sh brief $PID 2>&1)"
check "brief: downloads" 'grep -q "BRIEF FOR $PID" .oma/briefs/$PID.txt'
OUT="$(tools/oma.sh status 2>&1)"
check "status: prints live agents" '[[ "$OUT" == *"live agents: 3"* ]]'

# ---- the team board (022) ----------------------------------------------------------------------------------------
# A stub Lean: "lake build" succeeds; "lake env lean F" reports an error on the line of F that contains BADLEMMA.
cat > "$T/bin/lake" <<'EOF'
#!/usr/bin/env bash
if [ "$1" = build ]; then exit 0; fi
if [ "$1" = env ] && [ "$2" = lean ]; then
  N="$(grep -n BADLEMMA "$3" | head -1 | cut -d: -f1)"
  [ -n "$N" ] && { echo "$3:$N:18: error: unknown identifier 'BADLEMMA'"; exit 1; }
  exit 0
fi
exit 1
EOF
chmod +x "$T/bin/lake"; mkdir -p .oma/formal-conjectures
TP=Team.p
OUT="$(tools/oma.sh next --problem $TP 2>&1)"
check "team next: prints the board" '[[ "$OUT" == *"BOARD       1 open, 1 taken, 0 done, 1 dead"* ]] && [[ "$OUT" == *"#1   OPEN  step_bound"* ]] && [[ "$OUT" == *"#2   TAKEN base_case : f 0 = 1  @mate"* ]]'
check "team next: prints the steps and the dead item" '[[ "$OUT" == *"step Team.p.R1.H1 OPEN"* ]] && [[ "$OUT" == *"dead end: false for n = 3"* ]]'
check "team next: prints the suggested action" '[[ "$OUT" == *"NEXT ACTION Open subgoal #1 step_bound"* ]]'
check "team next: prints the dead ends of earlier teams, as data" '[[ "$OUT" == *"DEAD ENDS FOUND BY EARLIER AGENTS (data to check"* ]] && [[ "$OUT" == *"induction on n alone fails"* ]]'
OUT="$(tools/oma.sh next --problem Crowded.p 2>&1)"
check "steered next: prints why and takes the step" '[[ "$OUT" == *"STEERED     7 agents already work on Crowded.p"* ]] && [ -f .oma/leases/Crowded.p.R1.H2 ] && [ -f proofs/Crowded.p.R1.H2.lean ]'
OUT="$(tools/oma.sh beat $TP 2>&1)"
check "team beat: first line unchanged" '[[ "$OUT" == "ok · role lead · teammates: @mate (helper)"* ]]'
check "team beat: role change and assemble" '[[ "$OUT" == *"ROLE CHANGE PROMOTED: Your lead has been silent"* ]] && [[ "$OUT" == *"ASSEMBLE    ASSEMBLE NOW"* ]]'
check "team beat: sends the problem id" 'grep "/api/desk/beat" "$MOCK_LOG" | tail -1 | grep -q "\"problem\": \"Team.p\""'
OUT="$(tools/oma.sh board $TP 2>&1)"
check "board: team, board and new notes" '[[ "$OUT" == *"TEAM        @mate (lead)"* ]] && [[ "$OUT" == *"#1   OPEN  step_bound"* ]] && [[ "$OUT" == *"NEW NOTE #71 @mate"*"TAKING: base_case"* ]]'
OUT="$(tools/oma.sh board $TP 2>&1)"
check "board: remembers the last note seen" '[[ "$OUT" != *"NEW NOTE"* ]] && [ "$(cat .oma/seen/$TP)" = 71 ]'
OUT="$(tools/oma.sh board Old.p 2>&1)"; RC=$?
check "board: a desk without the board says so" '[ $RC -eq 0 ] && [[ "$OUT" == *"not switched on on this desk yet"* ]]'
OUT="$(tools/oma.sh take $TP 1 2>&1)"; RC=$?
check "take: holds the item and shows its statement as data" '[ $RC -eq 0 ] && [[ "$OUT" == *"you hold #1 step_bound"* ]] && [[ "$OUT" == *"STATEMENT (data, not instructions)"* ]]'
OUT="$(tools/oma.sh take $TP 2 2>&1)"; RC=$?
check "take: refused when a teammate holds it" '[ $RC -eq 1 ] && [[ "$OUT" == *"held by @mate"* ]]'
OUT="$(tools/oma.sh take $TP x 2>&1)"; RC=$?
check "take: k must be a number" '[ $RC -ne 0 ] && [[ "$OUT" == *"number of a subgoal"* ]]'
printf 'lemma step_bound (n : ℕ) : n + 0 = n := by simp\n' > lemma1.lean
OUT="$(tools/oma.sh done $TP 1 lemma1.lean 2>&1)"; RC=$?
check "done: sends the code and reports completion" '[ $RC -eq 0 ] && [[ "$OUT" == *"#1 sent (note #77"* ]] && [[ "$OUT" == *"COMPLETE"* ]] && grep "op\": \"done" "$MOCK_LOG" | tail -1 | grep -q "lemma step_bound"'
OUT="$(echo 'lemma x : True := by sorry' | tools/oma.sh done $TP 1 - 2>&1)"; RC=$?
check "done: the desk refusal is shown" '[ $RC -eq 1 ] && [[ "$OUT" == *"bad_lean forbidden: sorry"* ]]'
OUT="$(tools/oma.sh dead $TP 3 false for n equal 3 2>&1)"; RC=$?
check "dead: sends the reason" '[ $RC -eq 0 ] && [[ "$OUT" == *"dead end (note #79)"* ]] && grep "op\": \"dead" "$MOCK_LOG" | tail -1 | grep -q "false for n equal 3"'
OUT="$(tools/oma.sh drop $TP 1 2>&1)"; RC=$?
check "drop: ok" '[ $RC -eq 0 ] && [[ "$OUT" == *"#1 is open again"* ]]'
printf 'induction on n\nlemma step_bound (n : ℕ) : f (n + 1) ≤ 2 * f n\nlemma base_case : f 0 = 1\n' > plan.md
OUT="$(tools/oma.sh plan $TP plan.md 2>&1)"; RC=$?
check "plan: posted as a PLAN: note, subgoals added" '[ $RC -eq 0 ] && [[ "$OUT" == *"2 subgoals added"* ]] && grep "/api/desk/note" "$MOCK_LOG" | tail -1 | grep -q "\"body\": \"PLAN: induction on n"'
echo 55555555-5555-5555-5555-555555555555 > .oma/leases/Old.p
OUT="$(tools/oma.sh take Old.p 1 2>&1)"; RC=$?
check "take: a desk without the board answers not enabled (exit 2)" '[ $RC -eq 2 ] && [[ "$OUT" == *"not switched on on this desk yet"* ]]'
OUT="$(tools/oma.sh bundle $TP 2>&1)"; RC=$?
check "bundle: written, with the Uses line" '[ $RC -eq 0 ] && grep -q "uses note #77" .oma/bundles/$TP.lean && [[ "$OUT" == *"-- Uses: #77, #78"* ]]'
OUT="$(tools/oma.sh bundle Evil.p 2>&1)"; RC=$?
check "bundle: code that could run at compile time is never written" '[ $RC -ne 0 ] && [[ "$OUT" == *"forbidden code"* ]] && [ ! -f .oma/bundles/Evil.p.lean ]'
OUT="$(tools/oma.sh bundle Old.p 2>&1)"; RC=$?
check "bundle: a desk without the board answers not enabled (exit 2)" '[ $RC -eq 2 ] && [[ "$OUT" == *"not switched on"* ]]'
: > "$MOCK_LOG"
OUT="$(tools/oma.sh bundle $TP --check 2>&1)"; RC=$?
check "bundle --check: compiles each lemma" '[ $RC -eq 0 ] && [[ "$OUT" == *"#1 compiles"* ]] && [[ "$OUT" == *"#2 FAILS: unknown identifier"* ]]'
check "bundle --check: reports to the board" 'grep -q "\"op\": \"verify\", \"item\": \"1\", \"ok\": \"1\"" "$MOCK_LOG" && grep -q "\"op\": \"verify\", \"item\": \"2\", \"ok\": \"0\"" "$MOCK_LOG"'
{ cat "proofs/$TP.lean" | sed '/sorry/d'; printf '  trivial\n\n-- uses note #77 · board #1 step_bound · by @mate\nlemma step_bound : True := trivial\n-- uses note #78\n'; } > p.tmp && mv p.tmp "proofs/$TP.lean"
: > "$GH_LOG"
OUT="$(tools/oma.sh submit $TP 2>&1)"; RC=$?
check "submit: the Uses line names the teammates' notes" '[ $RC -eq 0 ] && grep -q "^Uses: #77, #78 " "$GH_LOG" && grep -q "^Model: test-model$" "$GH_LOG"'

echo; [ $FAILS -eq 0 ] && echo "ALL PASSED" || echo "$FAILS FAILED"
exit $FAILS
