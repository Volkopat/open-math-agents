import Mathlib

/-!
# OEIS A202254

Number of zero-sum `-n..n` arrays of 4 elements with adjacent element differences also in `-n..n`.

Conjectured by Colin Barker (Mar 03 2018):
* for even `n ≥ 1`, `12 * a(n) = 22 * n^3 + 33 * n^2 + 26 * n + 12`,
* for odd `n ≥ 1`, `12 * a(n) = 22 * n^3 + 33 * n^2 + 26 * n + 3`.
-/

namespace OMA.S_oeis_a202254

/-- A 4-tuple `f : Fin 4 → ℤ` is valid for parameter `n` if its entries lie in `[-n, n]`,
its sum is `0`, and all three adjacent differences `f 1 - f 0`, `f 2 - f 1`, `f 3 - f 2` lie in `[-n, n]`. -/
def isValid (n : ℕ) (f : Fin 4 → ℤ) : Prop :=
  (∀ i : Fin 4, -(n : ℤ) ≤ f i ∧ f i ≤ n) ∧
  (f 0 + f 1 + f 2 + f 3 = 0) ∧
  (-(n : ℤ) ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ n) ∧
  (-(n : ℤ) ≤ f 2 - f 1 ∧ f 2 - f 1 ≤ n) ∧
  (-(n : ℤ) ≤ f 3 - f 2 ∧ f 3 - f 2 ≤ n)

/-- `a(n)` is the number of valid 4-element zero-sum arrays in `-n..n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {f : Fin 4 → ℤ // isValid n f}

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → 12 * a n = 22 * n ^ 3 + 33 * n ^ 2 + 26 * n + 12) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → 12 * a n = 22 * n ^ 3 + 33 * n ^ 2 + 26 * n + 3) := by
  sorry

end OMA.S_oeis_a202254
