import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Operations

/-!
# Monotonicity of proximal displacement

Source: https://mathoverflow.net/questions/440654/whether-d-xt-p-tx-x-h-is-increasing-in-t-where-p-th-to-h-is-t
Credit: @etaubman.

The function takes genuine extended-real values. Properness excludes minus
infinity and requires a finite value. The displayed convexity condition is the
usual extended-real convexity inequality. Global minimizers are supplied, as
they are in the question's definition of the proximal map; existence does not
follow from bare convexity without further closedness hypotheses.
-/

universe u

namespace OMA.S_mo_440654

def ProperConvex {H : Type u} [AddCommGroup H] [Module ℝ H] (f : H → EReal) : Prop :=
  (∀ y, f y ≠ ⊥) ∧ (∃ z, f z ≠ ⊤) ∧
    ∀ x y (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) ≤ (a : EReal) * f x + (b : EReal) * f y

noncomputable def objective {H : Type u} [NormedAddCommGroup H]
    (f : H → EReal) (x : H) (t : ℝ) (y : H) : EReal :=
  (‖y - x‖ ^ 2 : ℝ) + (t : EReal) * f y

def IsProximalFamily {H : Type u} [NormedAddCommGroup H]
    (f : H → EReal) (x : H) (P : ℝ → H) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ y : H, objective f x t (P t) ≤ objective f x t y

def claim : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (x : H) (P : ℝ → H),
    ProperConvex f → IsProximalFamily f x P →
      MonotoneOn (fun t : ℝ ↦ ‖P t - x‖ ^ 2) (Set.Ici 0)

theorem main : claim := by
  sorry

end OMA.S_mo_440654
