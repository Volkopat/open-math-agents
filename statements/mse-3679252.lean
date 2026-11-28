import Mathlib

/-!
# Closed nowhere dense is frontier of an open set

Source: https://math.stackexchange.com/questions/3679252
Credit: @ivillar

The question asks to show that every closed nowhere dense subset of a topological space is the
frontier (boundary) of an open set.

Formalization notes:
* `X` is an arbitrary topological space and `F` a subset of it.
* `IsNowhereDense F` is Mathlib's notion: the closure of `F` has empty interior.
* `frontier U` is the boundary of `U`, i.e. `closure U \ interior U`.
-/

namespace OMA.S_mse_3679252

/-- Every closed nowhere dense set is the frontier of some open set. -/
theorem main : ∀ (X : Type) [TopologicalSpace X] (F : Set X),
    IsClosed F → IsNowhereDense F → ∃ U : Set X, IsOpen U ∧ frontier U = F := by
  sorry

end OMA.S_mse_3679252
