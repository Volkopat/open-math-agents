import Mathlib

/-!
# Sweeping the nodal set of a Klein–Gordon wave across an obstacle with bounded energy

Source: https://mathoverflow.net/questions/495160/can-a-uniformly-bounded-klein-gordon-wave-sweep-its-nodal-set-across-a-rigid-obs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Fix a smooth bounded obstacle `Ω ⊆ ℝ³` and a smooth isotopy of closed embedded surfaces `Σ_t`,
`t ∈ [0, 1]`, starting outside `Ω` and ending inside. Question: is there a family of smooth
real solutions `φ_ε` of the Klein–Gordon equation with stress–energy tensor bounded on compact
sets uniformly in `ε`, with smooth nodal surfaces `N_ε(t)`, such that `N_ε(t) → Σ_t` in the
Hausdorff sense as `ε → 0`? `main` states the positive answer for every mass `m > 0`, obstacle
and isotopy; a proof of its negation answers no.

Conventions:
* Spacetime is `ℝ × ℝ³`; the equation is `∂ₜ²φ - Δφ + m²φ = 0`, with `Δ` the sum of the three
  second partial derivatives in the coordinate directions.
* For `m > 0` the components of `T_{μν}[φ]` are bounded on a set iff `φ` and its first
  derivatives are (`T₀₀ = ½(φₜ² + |∇φ|² + m²φ²)` and every component is quadratic in them), so
  the uniform bound is stated for `|φ_ε|` and `‖Dφ_ε‖`.
* "`N_ε(t)` is a smooth surface": `0` is a regular value of `φ_ε(t, ·)`.
* Obstacle: `Ω = {ρ < 0}` for a smooth `ρ` with nonzero derivative on `{ρ = 0}`, `Ω` bounded.
* Isotopy: `Σ_t = H(t, S)` with `S = {ψ = 0}` a nonempty compact regular level set of a smooth
  `ψ`, and `H` smooth with each `H(t, ·)` a diffeomorphism of `ℝ³`. Starting wholly outside:
  `Σ_0 ∩ closure Ω = ∅`; ending wholly inside: `Σ_1 ⊆ Ω`.
* Hausdorff convergence uses `Metric.hausdorffEDist`, for each `t ∈ [0, 1]`.
-/

namespace OMA.S_mo_495160

open Filter

/-- Euclidean space `ℝ³`. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The Klein–Gordon operator `∂ₜ²φ - Δφ + m²φ` applied to `Φ : ℝ × ℝ³ → ℝ`. -/
noncomputable def kg (m : ℝ) (Φ : ℝ × E3 → ℝ) (t : ℝ) (x : E3) : ℝ :=
  deriv (fun s => deriv (fun r => Φ (r, x)) s) t -
    (∑ i : Fin 3, deriv (fun s => deriv
      (fun r : ℝ => Φ (t, x + r • EuclideanSpace.single i (1 : ℝ))) s) 0)
    + m ^ 2 * Φ (t, x)

/-- Smooth diffeomorphism of `ℝ³`. -/
def IsDiffeo (h : E3 → E3) : Prop :=
  ∃ g : E3 → E3, ContDiff ℝ ⊤ h ∧ ContDiff ℝ ⊤ g ∧ Function.LeftInverse g h ∧
    Function.RightInverse g h

theorem main :
    ∀ (m : ℝ), 0 < m →
    ∀ (ρ : E3 → ℝ), ContDiff ℝ ⊤ ρ → (∀ x, ρ x = 0 → fderiv ℝ ρ x ≠ 0) →
      Bornology.IsBounded {x | ρ x < 0} →
    ∀ (ψ : E3 → ℝ), ContDiff ℝ ⊤ ψ → (∀ x, ψ x = 0 → fderiv ℝ ψ x ≠ 0) →
      IsCompact {x | ψ x = 0} → {x | ψ x = 0}.Nonempty →
    ∀ (H : ℝ × E3 → E3), ContDiff ℝ ⊤ H → (∀ t, IsDiffeo fun x => H (t, x)) →
      (fun x => H (0, x)) '' {x | ψ x = 0} ∩ closure {x | ρ x < 0} = ∅ →
      (fun x => H (1, x)) '' {x | ψ x = 0} ⊆ {x | ρ x < 0} →
    ∃ Φ : ℝ → ℝ × E3 → ℝ,
      (∀ ε > 0, ContDiff ℝ ⊤ (Φ ε) ∧ ∀ t x, kg m (Φ ε) t x = 0) ∧
      (∀ K : Set (ℝ × E3), IsCompact K → ∃ C : ℝ, ∀ ε > 0, ∀ p ∈ K,
        |Φ ε p| ≤ C ∧ ‖fderiv ℝ (Φ ε) p‖ ≤ C) ∧
      (∀ ε > 0, ∀ t x, Φ ε (t, x) = 0 → fderiv ℝ (fun y => Φ ε (t, y)) x ≠ 0) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        Tendsto (fun ε => Metric.hausdorffEDist {x | Φ ε (t, x) = 0}
          ((fun x => H (t, x)) '' {x | ψ x = 0})) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  sorry

end OMA.S_mo_495160
