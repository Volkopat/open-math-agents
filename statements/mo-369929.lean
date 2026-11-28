import Mathlib

/-!
# Are the maxima of a quasinorm on a compact set attained at extreme points?

Source: https://mathoverflow.net/questions/369929
Credit: @koolkao

Question (Aryeh Kontorovich, MathOverflow 369929, 2020; CC BY-SA 4.0). A positive-homogeneous
function `‖·‖` on a vector space is a quasinorm if `‖x + y‖ ≤ K (‖x‖ + ‖y‖)` for some `K ≥ 1`.
What is known about maximizing a quasinorm (or, more generally, a continuous `f` with
`f(x/2 + y/2) ≤ (K/2) (f x + f y)`) over a compact set, say in a finite-dimensional space? Are
the maxima necessarily achieved at extreme points?

We state the second question for quasinorms on `ℝᵈ`: `main` states that for every quasinorm and
every nonempty compact set `C`, some extreme point of `C` is a maximum point of the quasinorm on
`C`. A disproof is a quasinorm and a compact set for which no extreme point is a maximum point.

Translation choices:
* the space is `Fin d → ℝ` for some `d`;
* a quasinorm is a function `q` that is nonnegative, vanishes only at `0`, is positive-homogeneous
  (`q (t • x) = t * q x` for `t ≥ 0`), satisfies the quasi-triangle inequality with some
  constant `K ≥ 1`, and is continuous (continuity is assumed for `f` in the question; every extra
  hypothesis only weakens `main`);
* extreme points are `Set.extremePoints ℝ C`;
* "the maxima are achieved at extreme points" is read in the weak form "some maximum point is an
  extreme point" (a quasinorm is continuous here, so it has maximum points on `C`).
-/

namespace OMA.S_mo_369929

/-- `q` is a (continuous) quasinorm on `ℝᵈ`. -/
def IsQuasinorm {d : ℕ} (q : (Fin d → ℝ) → ℝ) : Prop :=
  Continuous q ∧ (∀ x, 0 ≤ q x) ∧ (∀ x, q x = 0 → x = 0) ∧
    (∀ (t : ℝ) (x : Fin d → ℝ), 0 ≤ t → q (t • x) = t * q x) ∧
    ∃ K : ℝ, 1 ≤ K ∧ ∀ x y, q (x + y) ≤ K * (q x + q y)

/-- A quasinorm attains its maximum over a nonempty compact set at an extreme point. -/
theorem main :
    ∀ (d : ℕ) (q : (Fin d → ℝ) → ℝ), IsQuasinorm q → ∀ C : Set (Fin d → ℝ), IsCompact C →
      C.Nonempty → ∃ e ∈ C.extremePoints ℝ, ∀ y ∈ C, q y ≤ q e := by
  sorry

end OMA.S_mo_369929
