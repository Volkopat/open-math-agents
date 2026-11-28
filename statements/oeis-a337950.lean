import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.ModEq

namespace OMA.S_oeis_a337950

/-- Theta-like formal power series
`F(x) = ∑_{n=-∞}^{+∞} (-2)^n * (2*x)^(n^2) = 1 + ∑_{n ≥ 1} (-1)^n * 2^(n^2 - n) * (4^n + 1) * x^(n^2)`. -/
noncomputable def thetaF : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    if m = 0 then 1
    else if (Nat.sqrt m) ^ 2 = m then
      let n := Nat.sqrt m
      (-1 : ℤ) ^ n * (2 : ℤ) ^ (n ^ 2 - n) * ((4 : ℤ) ^ n + 1)
    else 0

/-- Formal operator `-x * d/dx` on `ℤ[[x]]`, sending `∑ f_m x^m` to `∑ (-m * f_m) x^m`. -/
noncomputable def negXDeriv (F : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun m => -(m : ℤ) * PowerSeries.coeff m F

/-- Defining L.g.f. relation of OEIS A337950:
`-log(thetaF(x)) = ∑_{m ≥ 1} a(m) * x^m / m`, equivalently `thetaF(x) * A(x) = -x * thetaF'(x)`
where `A(x) = ∑_{m ≥ 1} a(m) * x^m` with `A(0) = 0`. -/
def IsA337950 (A : PowerSeries ℤ) : Prop :=
  PowerSeries.coeff 0 A = 0 ∧
  thetaF * A = negXDeriv thetaF

/-- Conjecture on OEIS A337950: `a(4*n + k) ≡ 0 (mod 5)` for all `n ≥ 0` and `k ∈ {1, 2, 3}`. -/
theorem main :
    ∀ A : PowerSeries ℤ, IsA337950 A →
      ∀ n k : ℕ, k = 1 ∨ k = 2 ∨ k = 3 →
        PowerSeries.coeff (4 * n + k) A ≡ 0 [ZMOD 5] := by
  sorry

end OMA.S_oeis_a337950
