import Mathlib

/-!
# Exact values of Landau's constants (Bloch's constant `B` and Landau's constant `L`)

Source: https://en.wikipedia.org/wiki/Landau's_constants
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem: determine the exact values of Landau's constants. The source records the conjectured
values (Ahlfors–Grunsky for `B`, Rademacher for `L`):
* `B = Γ(1/3) Γ(11/12) / ((√3 + 1)^{1/2} Γ(1/4))`,
* `L = Γ(1/3) Γ(5/6) / Γ(1/6)`.
`main` states both.

Definitions (as on the source page). Let `F` be the set of holomorphic `f` on the open unit
disk `𝔻` with `f'(0) = 1`.
* `b(f)`: supremum of radii `r` of open disks `D` such that some open `U ⊆ 𝔻` is mapped by `f`
  injectively onto `D` (schlicht disk); `B = inf_{f ∈ F} b(f)`.
* `l(f)`: supremum of radii of open disks contained in `f(𝔻)`; `L = inf_{f ∈ F} l(f)`.
Suprema and infima are taken in `ℝ≥0∞` (they are finite and positive).
-/

namespace OMA.S_wp_what_is_the_exact_value_of_landau_s_constants_including_bloch_s_constant

open Metric

/-- Holomorphic on the unit disk with `f'(0) = 1`. -/
def Normalized (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (ball 0 1) ∧ deriv f 0 = 1

/-- `b(f)`: largest schlicht disk in the image. -/
noncomputable def schlichtRadius (f : ℂ → ℂ) : ENNReal :=
  ⨆ (r : ℝ) (_ : ∃ (U : Set ℂ) (c : ℂ), IsOpen U ∧ U ⊆ ball 0 1 ∧ Set.InjOn f U ∧
      f '' U = ball c r), ENNReal.ofReal r

/-- `l(f)`: largest disk in the image. -/
noncomputable def landauRadius (f : ℂ → ℂ) : ENNReal :=
  ⨆ (r : ℝ) (_ : ∃ c : ℂ, ball c r ⊆ f '' ball 0 1), ENNReal.ofReal r

/-- Bloch's constant. -/
noncomputable def B : ENNReal := ⨅ (f : ℂ → ℂ) (_ : Normalized f), schlichtRadius f

/-- Landau's constant. -/
noncomputable def L : ENNReal := ⨅ (f : ℂ → ℂ) (_ : Normalized f), landauRadius f

/-- Conjectured values of `B` and `L`. -/
theorem main :
    B = ENNReal.ofReal (Real.Gamma (1 / 3) * Real.Gamma (11 / 12) /
      (Real.sqrt (Real.sqrt 3 + 1) * Real.Gamma (1 / 4))) ∧
    L = ENNReal.ofReal (Real.Gamma (1 / 3) * Real.Gamma (5 / 6) / Real.Gamma (1 / 6)) := by
  sorry

end OMA.S_wp_what_is_the_exact_value_of_landau_s_constants_including_bloch_s_constant
