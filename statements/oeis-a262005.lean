import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a262005

/-- Coefficient `c(n) = (1 / n!) * ∏_{k=1}^n (k^5 + 1) = (n + 1) * ∏_{k=1}^n (k^4 - k^3 + k^2 - k + 1)`
of the generating function inside the logarithm of OEIS A262005. -/
def coeffF (n : ℕ) : ℤ :=
  ((n + 1 : ℕ) : ℤ) * ∏ k ∈ Finset.range n,
    (((k + 1 : ℕ) : ℤ) ^ 4 - ((k + 1 : ℕ) : ℤ) ^ 3 + ((k + 1 : ℕ) : ℤ) ^ 2 - ((k + 1 : ℕ) : ℤ) + 1)

/-- Generating series `F(x) = ∑_{n ≥ 0} (∏_{k=1}^n (k^5 + 1) / n!) * x^n ∈ ℤ[[x]]`. -/
noncomputable def seriesF : PowerSeries ℤ :=
  PowerSeries.mk coeffF

/-- Formal operator `x * d/dx` on `ℤ[[x]]`, sending `∑ f_m x^m` to `∑ (m * f_m) x^m`. -/
noncomputable def xDeriv (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => (m : ℤ) * PowerSeries.coeff m F

/-- Defining L.g.f. relation of OEIS A262005:
`log(F(x)) = ∑_{n ≥ 1} a(n) * x^n / n`, equivalently `F(x) * A(x) = x * F'(x)`
where `A(x) = ∑_{n ≥ 1} a(n) * x^n` with `A(0) = 0`. -/
def IsA262005 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  seriesF * A = xDeriv seriesF

/-- Conjecture on OEIS A262005: `a(n) ≡ 2 (mod 60)` for all `n ≥ 1`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA262005 A →
      ∀ n : ℕ, 1 ≤ n → PowerSeries.coeff n A ≡ 2 [ZMOD 60] := by
  sorry

end OMA.S_oeis_a262005
