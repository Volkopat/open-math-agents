import OMAStatements.S_oeis_a299741

open Polynomial in
lemma OMA.a299741_pair (i : ℕ) : ∀ j : ℕ,
    OMA.S_oeis_a299741.a i j = (OMA.S_oeis_a299741.p j).eval (i : ℤ) ∧
    OMA.S_oeis_a299741.a i (j + 1) = (OMA.S_oeis_a299741.p (j + 1)).eval (i : ℤ) := by
  intro j
  induction j with
  | zero => simp [OMA.S_oeis_a299741.a, OMA.S_oeis_a299741.p]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    rw [OMA.S_oeis_a299741.a, OMA.S_oeis_a299741.p, eval_sub, eval_mul, ← ih.1, ← ih.2]
    simp
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a299741.main := by
  intro i j
  exact (OMA.a299741_pair i j).1
