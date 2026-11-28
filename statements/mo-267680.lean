import Mathlib

/-!
# Pointwise sequential compactness of uniformly bounded Schur-convex functions

Source: Sung-En Chiu, https://mathoverflow.net/questions/267680 (CC BY-SA 3.0).
Credit: @connoranderson.

The question does not specify a topology. We use pointwise convergence, the
product topology on real-valued functions. Majorization is in the standard
Hardy-Littlewood-Pólya form using doubly stochastic matrices. The family is
compact in all dimensions, but for every positive uniform bound it is
sequentially compact exactly when there are at most two coordinates.
-/

namespace OMA.S_mo_267680
open Matrix

abbrev Δ (n : ℕ) := stdSimplex ℝ (Fin n)

def Maj {n : ℕ} (x y : Δ n) : Prop :=
  ∃ A ∈ doublyStochastic ℝ (Fin n), A *ᵥ y.val = x.val

def family (n : ℕ) (C : ℝ) : Set (Δ n → ℝ) :=
  {f | (∀ x, |f x| ≤ C) ∧ ∀ x y, Maj x y → f x ≤ f y}

theorem main : ∀ (n : ℕ) (C : ℝ), IsCompact (family n C) ∧
    (0<C → (IsSeqCompact (family n C) ↔ n≤2)) := by
  sorry

end OMA.S_mo_267680
