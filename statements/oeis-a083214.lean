import Mathlib

/-!
# A083214: Numbers k for which 3 | p(k), where p(k) = A000041(k) is the k-th partition number.

Source: https://oeis.org/A083214
Credit: @gblacher2

Conjecture (formula section of A083214, Benoit Cloitre, Oct 06 2005): "a(n) = 3n + o(n)."

The sequence has offset 1 and lists, in increasing order, the numbers `k` with `3 ∣ p(k)`:
3, 7, 9, 10, 14, 16, ... Here `p(k)` is the number of partitions of `k` (A000041), so
`p(0) = 1` and `0` is not a term. "a(n) = 3n + o(n)" is read in the standard way, as `n → ∞`:
`a(n) - 3n = o(n)`.
-/

namespace OMA.S_oeis_a083214

/-- The partition number `p(k)` (A000041): the number of partitions of `k`. -/
def partitionNumber (k : ℕ) : ℕ := Fintype.card (Nat.Partition k)

/-- A083214(n) for `n ≥ 1`: the `n`-th number `k` (in increasing order) with `3 ∣ p(k)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun k => 3 ∣ partitionNumber k) (n - 1)

/-- Cloitre's conjecture: `a(n) = 3n + o(n)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ) - 3 * n) =o[Filter.atTop] (fun n : ℕ => (n : ℝ)) := by
  sorry

end OMA.S_oeis_a083214
