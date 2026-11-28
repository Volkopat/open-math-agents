import Mathlib

/-!
# Norton’s signed-sum description of OEIS A000531

Source: https://oeis.org/A000531
Credit: @tczyzycki

Following Norton’s example and Ayyer’s interpretation in Section 5 of
https://arxiv.org/abs/0902.2329, count pairs of a sign word and a positive odd
integer for which some strictly increasing tuple in `(0, 1)` gives the sum.
The tuple may depend on the pair. A positive odd sum is strictly below `2 * n`,
so `j : Fin n` indexes exactly the possible targets `2 * j + 1`.

The separate geometric uniqueness assertion in Norton’s comment was refuted
by Pinelis, Theorem 2, https://doi.org/10.1007/s00022-005-1752-8.
-/

namespace OMA.S_oeis_a000531

def AttainsOddSum (n : ℕ) (signs : Fin (2 * n) → Bool) (j : Fin n) : Prop :=
  ∃ a : Fin (2 * n) → ℝ,
    StrictMono a ∧ (∀ i, 0 < a i ∧ a i < 1) ∧
      (∑ i, if signs i then a i else -a i) = 2 * (j.val : ℝ) + 1

theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.card {p : (Fin (2 * n) → Bool) × Fin n // AttainsOddSum n p.1 p.2} =
      ((2 * n + 1) * (2 * n).choose n - 4 ^ n) / 2 := by
  sorry

end OMA.S_oeis_a000531
