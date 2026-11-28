import OMAStatements.S_oeis_a002449

/-!
# OEIS A002449: the nested sums are shifted coefficients

By induction on `k`, `H k i = c (k + 1) (2 i)`: both sides satisfy the same recursion. Then
`a (n + 2) = c (n + 2) 1 = c (n + 1) 2 = H n 1`.
-/

namespace OMA.OeisA002449

open OMA.S_oeis_a002449

private lemma H_eq (k i : ℕ) : H k i = c (k + 1) (2 * i) := by
  induction k generalizing i with
  | zero =>
    simp [H, c]
  | succ k ih =>
    rw [H, c]
    exact Finset.sum_congr rfl fun t _ => ih t

end OMA.OeisA002449

theorem OMA.solution : type_of% @OMA.S_oeis_a002449.main := by
  intro n _
  rw [OMA.OeisA002449.H_eq]
  simp [OMA.S_oeis_a002449.a, OMA.S_oeis_a002449.c]
