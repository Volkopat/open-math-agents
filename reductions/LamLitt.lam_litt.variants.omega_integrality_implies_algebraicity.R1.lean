import FormalConjectures.LittProblems.«1»
import Mathlib

-- Reduction LamLitt.lam_litt.variants.omega_integrality_implies_algebraicity.R1
-- Credit: @GiridhariPradeep

/-!
# Lam–Litt, ω-integrality implies bounded denominators: split by the order of the ODE

* `H1` (order zero, proved below as a test of the setup and also provable on its own):
  for `n = 0` the equation reads `f · q(z) = p(z)` with `q(0) ≠ 0`, so `f` is a rational
  power series, and its coefficients have bounded denominators without any use of `ω`.
* `H2` (open core): the case of order `n + 1 ≥ 1`.
-/

namespace OMA.R_LamLitt_lam_litt_variants_omega_integrality_implies_algebraicity_R1

open PowerSeries LamLitt

/-- Order zero: the solution is a rational power series, so it has bounded denominators. -/
def H1 : Prop :=
  ∀ (f : PowerSeries ℚ) (g : MvRatFunc (Fin 1) ℚ), IsSolutionOfAlgebraicODE 0 f g →
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N

/-- Order at least one, under the ω-integrality hypothesis (the open core). -/
def H2 : Prop :=
  ∀ (n : ℕ) (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 2)) ℚ),
    IsSolutionOfAlgebraicODE (n + 1) f g → ∀ ω : Nat.Primes → ℤ,
    omegaSuperlinear ω → omegaIntegral ω (PowerSeries.coeff · f) →
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N

theorem main : H1 → H2 →
    type_of% @LamLitt.lam_litt.variants.omega_integrality_implies_algebraicity := by
  intro h1 h2 n f g hODE ω hω
  cases n with
  | zero => exact h1 f g hODE
  | succ n => exact h2 n f g hODE ω hω.1 hω.2

end OMA.R_LamLitt_lam_litt_variants_omega_integrality_implies_algebraicity_R1
