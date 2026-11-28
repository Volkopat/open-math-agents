import Mathlib

/-!
# smooth families of analytic functions

Source: https://mathoverflow.net/questions/100119
Credit: @tczyzycki

Let `f : ℝ^m × ℝ^n → ℝ` be a smooth (`C^∞`) function in `(x, y)` such that for each fixed `x`,
the map `y ↦ f (x, y)` is globally analytic, i.e. its Taylor expansion around `y = 0` converges
to `f (x, y)` for all `y ∈ ℝ^n`. The question asks whether for each coordinate `i : Fin m` and
each fixed `x`, the partial derivative `y ↦ ∂f/∂x_i (x, y)` is also globally analytic around
`y = 0`. (The source also briefly asks the local variant where the Taylor series converges only
on an open neighborhood of `0`; here we state the primary global question.)
-/

namespace OMA.S_mo_100119

/-- A function `g : ℝ^n → ℝ` is globally analytic around `0` if it is represented on all of `ℝ^n`
by a power series centered at `0` (which necessarily equals its Taylor series at `0`). -/
def IsGloballyAnalyticAtZero {n : ℕ} (g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ p : FormalMultilinearSeries ℝ (Fin n → ℝ) ℝ,
    HasFPowerSeriesOnBall g p 0 ⊤

/-- The partial derivative of `f : ℝ^m × ℝ^n → ℝ` with respect to the `i`-th `x`-coordinate. -/
noncomputable def partialX {m n : ℕ} (f : (Fin m → ℝ) × (Fin n → ℝ) → ℝ)
    (i : Fin m) (x : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  fderiv ℝ f (x, y) (Pi.single i 1, 0)

theorem main :
    ∀ (m n : ℕ) (f : (Fin m → ℝ) × (Fin n → ℝ) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ x : Fin m → ℝ, IsGloballyAnalyticAtZero (fun y => f (x, y))) →
      ∀ (i : Fin m) (x : Fin m → ℝ),
        IsGloballyAnalyticAtZero (fun y => partialX f i x y) := by
  sorry

end OMA.S_mo_100119
