import Mathlib

/-!
# Norms of closest points on subspaces

Source: Whatsumitzu, https://mathoverflow.net/questions/471674 (CC BY-SA).
M. A. Smith studied the metric projection bound and uniform nonsquareness
in 1981 (doi:10.1016/0021-9045(81)90092-7). See also J. Desbiens (1990),
doi:10.1017/S000497270002863X. The formulation here permits choosing among
all closest points and gives an isometric square criterion. Credit: @connoranderson.
-/
namespace OMA.S_mo_471674
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def best (V : Submodule ℝ E) (x v : E) : Prop := v∈V ∧ ∀ w∈V, ‖x-v‖ ≤ ‖x-w‖
def someBound (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ℝ) : Prop :=
  ∀ (V : Submodule ℝ E) (x : E), ∃ v, best V x v ∧ ‖v‖ ≤ C*‖x‖
def everyBound (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (C : ℝ) : Prop :=
  ∀ (V : Submodule ℝ E) (x v : E), best V x v → ‖v‖ ≤ C*‖x‖
def orth (r v : E) : Prop := ∀ t : ℝ, ‖r‖ ≤ ‖r+t•v‖
def hasSquare (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∃ x y : E, ∀ a b : ℝ, ‖a•x+b•y‖=|a|+|b|

theorem main : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
    (∀ C : ℝ, someBound E C ↔ everyBound E C) ∧
    (someBound E 1 ↔ ∀ r v : E, orth r v → orth v r) ∧
    someBound E 2 ∧ ((∀ C : ℝ, C<2 → ¬ someBound E C) ↔ hasSquare E) := by
  sorry
end OMA.S_mo_471674
