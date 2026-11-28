import Mathlib

namespace OMA.S_oeis_a193550

open PowerSeries BigOperators

/-- Formal power series inverse of `f ∈ ℚ[[X]]` with `coeff 0 f = 1`, defined recursively by
`g(0) = 1` and `g(n) = -∑_{k=1}^n [X^k] f * g(n - k)` for `n ≥ 1`. -/
noncomputable def invOneCoeffs (f : PowerSeries ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => -(∑ k : Fin (n + 1), PowerSeries.coeff (k.val + 1) f * invOneCoeffs f (n - k.val))
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- Formal inverse `1 / f` in `ℚ[[X]]` for `f` with `coeff 0 f = 1`. -/
noncomputable def invOne (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (invOneCoeffs f)

/-- Depth-`d` truncated tail `A_k(x) = 1 / Q(k)` of the odd-squares Stieltjes continued fraction
`Q(k) = 1 - (2k+1)^2 x / (1 - (2k+1)^2 x / Q(k+1))`, so
`A_k = (1 - (2k+1)^2 x A_{k+1}) / (1 - (2k+1)^2 x (1 + A_{k+1}))`. -/
noncomputable def cfTail : ℕ → ℕ → PowerSeries ℚ
  | 0, _ => 1
  | d + 1, k =>
      let w : ℚ := ((2 * k + 1 : ℕ) : ℚ) ^ 2
      let next := cfTail d (k + 1)
      (1 - PowerSeries.C w * PowerSeries.X * next) *
        invOne (1 - PowerSeries.C w * PowerSeries.X * (1 + next))

/-- The o.g.f. `A(x) = 1/(1 - x/(1 - x/(1 - 9x/(1 - 9x/(1 - 25x/...)))))` of OEIS A193550. -/
noncomputable def a193550 : PowerSeries ℚ :=
  PowerSeries.mk fun n => PowerSeries.coeff n (cfTail n 0)

/-- Conjecture on OEIS A193550 (Paul D. Hanna):
given the o.g.f. `A(x)`, `sqrt((A(x) - 1) / x)` is an integer power series
(i.e. there exists `S ∈ ℤ[[X]]` such that `X * S(X)^2 = A(X) - 1`). -/
theorem main :
    ∃ S : PowerSeries ℤ,
      PowerSeries.X * (S.map (Int.castRingHom ℚ)) ^ 2 = a193550 - 1 := by
  sorry

end OMA.S_oeis_a193550
