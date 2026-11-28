import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OMA.S_oeis_a074216

/-- Sum of divisors `σ(m)`. -/
def sigma (m : ℕ) : ℕ :=
  ∑ d ∈ m.divisors, d

/-- Membership in OEIS A074216: positive squares `m` satisfying `σ(m) ≡ 0 (mod 3)`. -/
def IsInA074216 (m : ℕ) : Prop :=
  1 ≤ m ∧ (∃ r : ℕ, m = r ^ 2) ∧ 3 ∣ sigma m

/-- Membership in OEIS A072864: positive integers `r` such that the smallest `k > 1`
dividing `σ(k * r^2)` is equal to `3`. -/
def IsInA072864 (r : ℕ) : Prop :=
  1 ≤ r ∧ (∀ k : ℕ, 1 < k → (k ∣ sigma (k * r ^ 2)) → 3 ≤ k) ∧ 3 ∣ sigma (3 * r ^ 2)

/-- OEIS A074216 conjecture (R. J. Mathar, May 19 2020):
`a(n) = A072864(n)^2`, i.e., the elements of A074216 are precisely the squares of the
elements of A072864 (preserving order since `r ↦ r^2` is strictly increasing on `ℕ`). -/
theorem main :
    (∀ m : ℕ, IsInA074216 m ↔ ∃ r : ℕ, IsInA072864 r ∧ m = r ^ 2) ∧
    (∀ r : ℕ, 1 ≤ r → (IsInA074216 (r ^ 2) ↔ IsInA072864 r)) := by
  sorry

end OMA.S_oeis_a074216
