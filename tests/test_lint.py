#!/usr/bin/env python3
"""Tests for tools/lint.py: every kind of file, and the attacks it must stop. Run: python3 -I tests/test_lint.py
Works on a temporary copy of the repository layout, so nothing in the working tree is touched."""
import json
import os
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CAT = json.load(open(os.path.join(ROOT, "data", "catalog.json")))
EXTRA = json.load(open(os.path.join(ROOT, "data", "extra.json")))
P = next(p for p in CAT["problems"] if p["id"] == "Erdos3.erdos_3.variants.gowers")
U = EXTRA["problems"][0]["id"]  # a problem waiting for a statement
SAN = lambda s: "".join(c if c.isalnum() else "_" for c in s)
RED = f"{P['id']}.R1"
RNS = f"OMA.R_{SAN(RED)}"
SNS = f"OMA.S_{SAN(U)}"

tmp = tempfile.mkdtemp()
os.makedirs(os.path.join(tmp, "data"))
shutil.copy(os.path.join(ROOT, "data", "catalog.json"), os.path.join(tmp, "data"))
shutil.copy(os.path.join(ROOT, "data", "extra.json"), os.path.join(tmp, "data"))
for d in ("proofs", "reductions", "statements"):
    os.makedirs(os.path.join(tmp, d))

failures = 0


def lint(rel, text, expect_ok, must_mention=None, name=""):
    global failures
    path = os.path.join(tmp, rel)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write(text)
    r = subprocess.run([sys.executable, "-I", os.path.join(ROOT, "tools", "lint.py"), rel, "data/catalog.json"], cwd=tmp, capture_output=True, text=True)
    os.remove(path)
    try:
        out = json.loads(r.stdout)
    except json.JSONDecodeError:
        out = {"ok": False, "errors": ["no JSON: " + r.stdout + r.stderr]}
    ok = out.get("ok") is True and r.returncode == 0
    good = ok == expect_ok and (must_mention is None or any(must_mention in e for e in out.get("errors", [])))
    print(("PASS" if good else "FAIL"), name or rel, "" if good else out)
    failures += not good
    return out


PROOF_HEAD = f"import {P['module']}\n\n"
GOOD_PROOF = PROOF_HEAD + f"lemma helper : 1 = 1 := rfl\n\ntheorem OMA.solution : type_of% @{P['decl']} := by\n  exact?\n"
PF = f"proofs/{P['id']}.lean"

# ---- proofs -----------------------------------------------------------------------------------
lint(PF, GOOD_PROOF, True, name="proof: valid")
lint(PF, PROOF_HEAD + f"theorem OMA.disproof : ¬ (type_of% @{P['decl']}) := by\n  intro h\n  exact?\n", True, name="proof: valid disproof")
lint(PF, PROOF_HEAD + "lemma a : 1 = 1 := rfl\nimport Mathlib.Tactic\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "imports must come first", "proof: import after code")
lint(PF, f"import {P['module']}\nimport Mathlib.Tactic\n\nset_option maxHeartbeats 400000 in\ntheorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", True, name="proof: extra Mathlib import and set_option")
lint(PF, PROOF_HEAD + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  sorry\n", False, "sorry", "attack: sorry")
lint(PF, PROOF_HEAD + "axiom cheat : False\n" + f"theorem OMA.solution : type_of% @{P['decl']} := cheat.elim\n", False, "axiom", "attack: axiom")
lint(PF, PROOF_HEAD + f"theorem OMA.solution : type_of% @{P['decl']} := {P['decl']}\n", False, "upstream declaration", "attack: reuse the sorried upstream theorem")
lint(PF, PROOF_HEAD + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  native_decide\n", False, "native_decide", "attack: native_decide")
lint(PF, PROOF_HEAD + "#eval IO.println 1\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "#eval", "attack: #eval")
lint(PF, PROOF_HEAD + "run_cmd pure ()\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "run_cmd", "attack: run_cmd")
lint(PF, PROOF_HEAD + "macro \\x22hi\\x22 : tactic => `(tactic| simp)\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "macro", "attack: macro")
lint(PF, PROOF_HEAD + "elab_rules : tactic | _ => pure ()\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "elab", "attack: elab_rules")
lint(PF, PROOF_HEAD + "@[implemented_by foo] def bar : Nat := 1\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, None, "attack: implemented_by attribute")
lint(PF, PROOF_HEAD + "initialize pure ()\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "initialize", "attack: initialize")
lint(PF, PROOF_HEAD + 'def s := "x"\n' + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "double-quote", "attack: string literal")
lint(PF, PROOF_HEAD + "set_option trace.Meta.synthInstance true in\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "set_option", "attack: arbitrary set_option")
lint(PF, PROOF_HEAD + f"theorem OMA.solution : True := trivial\n", False, "exactly one", "attack: weaker target")
# Conservative by design: any other name starting with OMA.solution is refused (no ambiguity for the axiom check).
lint(PF, PROOF_HEAD + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\ntheorem OMA.solution' : True := trivial\n", False, "exactly one", "proof: a look-alike name OMA.solution' is refused")
lint(PF, PROOF_HEAD + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\nexample : OMA.solution = OMA.solution := rfl\n", False, "exactly one", "attack: second mention of OMA.solution")
lint(PF, "import Mathlib\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "first line must be", "proof: wrong first import")
lint(PF, PROOF_HEAD + "/- unterminated comment\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", False, "unterminated", "attack: unterminated comment")
lint(PF, PROOF_HEAD + "-- #eval in a comment is fine\n" + f"theorem OMA.solution : type_of% @{P['decl']} := by\n  simp\n", True, name="proof: banned words inside comments are ignored")
lint("proofs/not-a-problem.lean", GOOD_PROOF, False, "unknown", "proof: unknown id")
lint("proofs/sub/x.lean", GOOD_PROOF, False, "file must be", "path: subdirectory")
lint(f"proofs/{U}.lean", "import Mathlib\ntheorem OMA.solution : True := trivial\n", False, "no Lean statement yet", "proof: problem without a statement")

# ---- statements -------------------------------------------------------------------------------
SF = f"statements/{U}.lean"
GOOD_ST = f"import Mathlib\n\nnamespace {SNS}\n\ndef Good (n : ℕ) : Prop := n = n\n\ntheorem main : ∀ n : ℕ, Good n := by\n  sorry\n\nend {SNS}\n"
lint(SF, GOOD_ST, True, name="statement: valid")
lint(SF, GOOD_ST.replace("n = n", "sorry"), False, "exactly one sorry", "statement: sorry in a definition")
lint(SF, GOOD_ST.replace("∀ n : ℕ, Good n", "sorry"), False, "placeholder", "statement: placeholder statement")
lint(SF, GOOD_ST + "theorem extra : 1 = 1 := rfl\n", False, "only `theorem main`", "statement: extra theorem")
lint(SF, GOOD_ST.replace(f"namespace {SNS}", "namespace Wrong"), False, "namespace", "statement: wrong namespace")
lint(SF, GOOD_ST.replace("import Mathlib", f"import {P['module']}"), False, "Mathlib only", "statement: non-Mathlib import")
lint(f"statements/{P['id']}.lean", GOOD_ST, False, "not a problem waiting", "statement: for a problem that already has one")

# ---- reductions -------------------------------------------------------------------------------
RF = f"reductions/{RED}.lean"
GOOD_RED = (f"import {P['module']}\n\nnamespace {RNS}\n\ndef H1 : Prop := ∀ k : ℕ, 3 ≤ k → 0 < k\n\ndef H2 : Prop :=\n  ∀ n : ℕ, n + 0 = n\n\n"
            f"lemma helper : 1 = 1 := rfl\n\ntheorem main : H1 → H2 → type_of% @{P['decl']} := by\n  intro h1 h2\n  exact?\n\nend {RNS}\n")
lint(RF, GOOD_RED, True, name="reduction: valid")
lint(RF, GOOD_RED.replace("def H2 : Prop :=\n  ∀ n : ℕ, n + 0 = n\n\n", "").replace("H1 → H2 →", "H1 →"), False, "2 to 4", "reduction: single hypothesis")
lint(RF, GOOD_RED.replace("∀ k : ℕ, 3 ≤ k → 0 < k", f"type_of% @{P['decl']}"), False, "may not mention", "reduction: hypothesis restates the target")
lint(RF, GOOD_RED.replace("∀ n : ℕ, n + 0 = n", "∀ k : ℕ, 3 ≤ k → 0 < k"), False, "identical", "reduction: duplicate hypotheses")
lint(RF, GOOD_RED.replace("lemma helper", "def Cheat : Prop := True\nlemma helper"), False, "only the H definitions", "reduction: extra definition")
lint(RF, GOOD_RED.replace("H1 → H2 → type_of%", "H2 → H1 → type_of%"), False, "theorem main", "reduction: wrong order in main")

# a step of that reduction needs the reduction merged first
SPF = f"proofs/{RED}.H2.lean"
GOOD_STEP = f"import OMAReductions.R_{SAN(RED)}\n\ntheorem OMA.solution : {RNS}.H2 := by\n  intro n\n  rfl\n"
lint(SPF, GOOD_STEP, False, "reduction merged first", "step: before its reduction is merged")
open(os.path.join(tmp, RF), "w").write(GOOD_RED)
lint(SPF, GOOD_STEP, True, name="step: valid once the reduction is merged")
lint(f"proofs/{RED}.H3.lean", GOOD_STEP.replace("H2", "H3"), False, None, "step: hypothesis that does not exist")
lint(SPF, GOOD_STEP.replace(f"{RNS}.H2", f"{RNS}.H1"), False, "exactly one", "step: proves the wrong hypothesis")
NESTED = f"{RED}.H1.R1"
NNS = f"OMA.R_{SAN(NESTED)}"
lint(f"reductions/{NESTED}.lean", f"import OMAReductions.R_{SAN(RED)}\n\nnamespace {NNS}\n\ndef H1 : Prop := ∀ m : ℕ, 2 ≤ m → 1 < m\n\ndef H2 : Prop := ∀ m : ℕ, m * 1 = m\n\n"
     f"theorem main : H1 → H2 → {RNS}.H1 := by\n  intro a b k hk\n  trivial\n\nend {NNS}\n", True, name="reduction of a step (nested)")

# a proof of a problem first stated here, once the statement is merged
open(os.path.join(tmp, SF), "w").write(GOOD_ST)
lint(f"proofs/{U}.lean", f"import OMAStatements.S_{SAN(U)}\n\ntheorem OMA.solution : type_of% @{SNS}.main := by\n  intro n\n  rfl\n", True, name="proof of a statement merged here")
out = lint(f"proofs/{U}.lean", f"import OMAStatements.S_{SAN(U)}\n\ntheorem OMA.disproof : ¬ (type_of% @{SNS}.main) := by\n  simp\n", True, name="refutation of a statement merged here")
assert out.get("polarity") == "disproof"

# Erdős #142: the formula is free in the statement, so value answers are refused automatically
E142 = next(p for p in CAT["problems"] if p["id"] == "Erdos142.erdos_142.variants.three")
lint(f"proofs/{E142['id']}.lean", f"import {E142['module']}\n\nnoncomputable def OMA.answer : ℕ → ℝ := fun N => N\n\n"
     f"theorem OMA.solution : Erdos142.erdos_142.variants.three.answer = OMA.answer → type_of% @{E142['decl']} := by\n  intro h\n  rw [h]\n  exact?\n",
     False, "not accepted automatically", "Erdős 142: value answer refused (formula is free in the statement)")

# a reduction with plainly trivial hypotheses farms step points: refused
for bad in ("True", "False", "(1:ℕ) = 1", "∀ n : ℕ, n = n", "∀ k : ℕ, 3 ≤ k → True",
            # wrappers and connectives around the same: each one used to pass
            "Eq x x", "∀ n : ℕ, (n = n)", "x = x ∧ True", "¬¬True", "1 = 1 ∨ False", "id True", "(fun _ => True) 0",
            "∃ n : ℕ, n = n", "P → P", "2 + 2 = 4", "1 = 2", "¬ (1 = 2)", "Iff True True", "And True True"):
    lint(RF, GOOD_RED.replace("∀ k : ℕ, 3 ≤ k → 0 < k", bad), False, "trivially", f"reduction: trivial hypothesis {bad}")
# real hypotheses that merely contain a trivial piece are not refused
for good in ("∀ n : ℕ, n ≤ n + 1", "∀ n : ℕ, (n ≤ n + 1) → 0 < n + 1", "FalseLemma ∧ ∀ n : ℕ, 0 < n + 1",
             "∀ n : ℕ, 0 < n + 1 ∧ ∀ m : ℕ, True", "(∀ n : ℕ, 0 < n + 1) ∧ (∀ n : ℕ, n < n + 1 → True)"):
    lint(RF, GOOD_RED.replace("∀ k : ℕ, 3 ≤ k → 0 < k", good), True, name=f"reduction: not trivial {good}")

shutil.rmtree(tmp)
print(f"\n{'ALL PASSED' if not failures else f'{failures} FAILED'}")
sys.exit(1 if failures else 0)
