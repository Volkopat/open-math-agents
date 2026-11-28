import Mathlib.RingTheory.PowerSeries.Basic

namespace OMA.S_oeis_a338635

/-- Membership in OEIS A003714 (Fibbinary numbers): natural numbers whose binary representation
contains no two consecutive `1`-bits. -/
def isFibbinary (m : ℕ) : Prop :=
  ∀ i : ℕ, (m / 2 ^ i) % 4 ≠ 3

/-- Conjecture (OEIS A338635): Let `A(x) = ∑ a(n) x^n ∈ ℤ[[x]]` with `A(0) = 1` satisfy the
continued fraction relation
`1 = A(x) - x / (A(x) - 3*x / (A(x) - 6*x / (A(x) - 10*x / ...)))`
with triangular coefficients `T(k + 2) = (k + 2)*(k + 3)/2`, formalized as the existence of tail
series `R : ℕ → PowerSeries ℤ` with `A(x) - 1 = x * R(0)` and
`R(k) * (A(x) - (((k + 2) * (k + 3) / 2 : ℕ) : PowerSeries ℤ) * x * R(k + 1)) = 1` for all `k ≥ 0`.
Then for all `n > 0`, `a(n)` is odd if and only if `n = 2 * m + 1` for some Fibbinary number `m`. -/
theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 1 →
      (∃ R : ℕ → PowerSeries ℤ,
        A - 1 = PowerSeries.X * R 0 ∧
        ∀ k : ℕ, R k * (A - (((k + 2) * (k + 3) / 2 : ℕ) : PowerSeries ℤ) * PowerSeries.X * R (k + 1)) = 1) →
      ∀ n : ℕ, 0 < n → (Odd (PowerSeries.coeff n A) ↔ ∃ m : ℕ, isFibbinary m ∧ n = 2 * m + 1) := by
  sorry

end OMA.S_oeis_a338635
