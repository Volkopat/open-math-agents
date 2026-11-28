import Mathlib

/-!
# Flajolet-Zeilberger conjecture on equiharmonic numbers

Source: https://math.stackexchange.com/questions/1250537/a-conjecture-about-equiharmonic-numbers-of-flajolet-via-doron-zeilberger
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Define the equiharmonic numbers by
`K_ν := ((6ν)! / Ω^(6ν)) ∑_{(n₁, n₂) ∈ ℤ² \ {(0,0)}} 1 / (n₁ e^(-2πi/3) + n₂ e^(2πi/3))^(6ν)`,
where `Ω := Γ(1/3)^3 / (2π)`.
Conjecture (Flajolet): The generating function `(7/36) ∑_{ν ≥ 1} K_ν z^(ν - 1)`
admits the Stieltjes continued fraction representation
`1 / (1 - d_1 z / (1 - d_2 z / ...))`, where
`d_n = (1/4) (3n)(3n+1)^2(3n+2)^2(3n+3)^2(3n+4) / ((6n+1)(6n+7))` for `n ≥ 1`.

Conventions:
- `d_1 = 10880/13` and `d_2 = 13810240/247` are taken exactly as displayed in the source (they
  are exceptional: the general formula would give `10800/13` and `3810240/247`); the general
  formula `d_n` is used for `n ≥ 3`.
- Equality of the formal power series with the Stieltjes continued fraction is
  expressed coefficientwise via the `(m + 1)`-st formal convergent, whose `z^m`
  coefficient stabilizes for all convergents of depth `> m`.
-/

namespace OMA.S_mse_1250537

noncomputable def omegaVal : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * (Complex.Gamma (1 / 3 : ℂ)) ^ 3

noncomputable def equiharmonic (ν : ℕ) : ℂ :=
  ((Nat.factorial (6 * ν) : ℂ) / omegaVal ^ (6 * ν)) *
    ∑' p : {q : ℤ × ℤ // q ≠ (0, 0)},
      (1 : ℂ) /
        ((p.1.1 : ℂ) * Complex.exp (-2 * Complex.I * (Real.pi : ℂ) / 3) +
          (p.1.2 : ℂ) * Complex.exp (2 * Complex.I * (Real.pi : ℂ) / 3)) ^ (6 * ν)

noncomputable def dCoeff (n : ℕ) : ℂ :=
  if n = 1 then (10880 / 13 : ℂ) else if n = 2 then (13810240 / 247 : ℂ) else
  (1 / 4 : ℂ) *
    ((3 * n : ℂ) * (3 * n + 1 : ℂ) ^ 2 * (3 * n + 2 : ℂ) ^ 2 *
      (3 * n + 3 : ℂ) ^ 2 * (3 * n + 4 : ℂ)) /
    ((6 * n + 1 : ℂ) * (6 * n + 7 : ℂ))

noncomputable def cfConvergentAux (start : ℕ) : ℕ → PowerSeries ℂ
  | 0 => 1
  | k + 1 =>
      (1 - PowerSeries.C (dCoeff start) * PowerSeries.X * cfConvergentAux (start + 1) k)⁻¹

noncomputable def cfConvergent (N : ℕ) : PowerSeries ℂ :=
  cfConvergentAux 1 N

theorem main :
    ∀ m : ℕ,
      PowerSeries.coeff m (cfConvergent (m + 1)) = (7 / 36 : ℂ) * equiharmonic (m + 1) := by
  sorry

end OMA.S_mse_1250537
