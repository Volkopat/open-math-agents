import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a397244

/-- Membership in OEIS A003714 (Fibbinary numbers): natural numbers whose binary representation
contains no two consecutive `1`-bits. -/
def isFibbinary (m : ℕ) : Prop :=
  ∀ i : ℕ, (m / 2 ^ i) % 4 ≠ 3

/-- Conjecture (OEIS A397244): If `A(x) = ∑ a(n) x^n ∈ ℤ[[x]]` satisfies `A(0) = 1`, `A'(0) = 1`,
and `(2 * n) * [x^n] A(x)^(2 * n) = (2 * n - 1) * [x^n] A(x)^(2 * n + 1)` for all `n > 1`,
then for all `n > 0`, `a(n)` is odd if and only if `n = 2 * m + 1` for some Fibbinary number `m`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      PowerSeries.coeff 1 A = 1 →
      (∀ n : ℕ, 1 < n →
        ((2 * n : ℕ) : ℤ) * PowerSeries.coeff n (A ^ (2 * n)) =
          ((2 * n - 1 : ℕ) : ℤ) * PowerSeries.coeff n (A ^ (2 * n + 1))) →
      ∀ n : ℕ, 0 < n → (Odd (PowerSeries.coeff n A) ↔ ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1) := by
  sorry

end OMA.S_oeis_a397244
