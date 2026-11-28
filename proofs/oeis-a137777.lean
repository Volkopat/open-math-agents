import OMAStatements.S_oeis_a137777
import Mathlib

/-!
# OEIS A137777: row sums of the Bernoulli derivative triangle

The sum of all coefficients of the Bernoulli polynomial `B_{n+1}(x)` is its value at `x = 1`,
which is the Bernoulli number `B'_{n+1}` (with the convention `B'_1 = 1/2`). So the row sum is
`2 (n+2)! B'_{n+1}`.

* For `n = 0` this is `2 · 2 · (1/2) = 2`, the value `2 · 1` on the right.
* For `n ≥ 1` we have `B'_{n+1} = B_{n+1}`, and the right side is `2 (n+2)! B_{n+1}`.
-/

open Finset OMA.S_oeis_a137777

namespace OMA.A137777

/-- The Bernoulli polynomial `B_n(x)` has degree at most `n`. -/
lemma natDegree_le (n : ℕ) : (Polynomial.bernoulli n).natDegree ≤ n := by
  unfold Polynomial.bernoulli
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  exact (Polynomial.natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hi; omega)

/-- The coefficients of `B_{n+1}(x)` sum to `B'_{n+1}`. -/
lemma coeff_sum (n : ℕ) :
    ∑ k ∈ range (n + 2), (Polynomial.bernoulli (n + 1)).coeff k = bernoulli' (n + 1) := by
  have h := Polynomial.eval_eq_sum_range' (p := Polynomial.bernoulli (n + 1)) (n := n + 2)
    (by have := natDegree_le (n + 1); omega) (1 : ℚ)
  rw [Polynomial.bernoulli_eval_one] at h
  rw [h]
  simp

end OMA.A137777

open OMA.A137777 in
theorem OMA.solution : type_of% @OMA.S_oeis_a137777.main := by
  intro n
  unfold derivativeEntry
  rw [← Finset.mul_sum, coeff_sum]
  unfold targetSequence
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bernoulli'_one]
    norm_num [Nat.factorial]
  · rw [if_neg (by omega), if_neg (by omega), show n + 2 - 1 = n + 1 by omega,
      bernoulli_eq_bernoulli'_of_ne_one (by omega)]
    ring
