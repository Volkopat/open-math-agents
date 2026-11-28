import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Set.Card
import Mathlib.ModelTheory.Semantics
import Mathlib.Topology.Instances.Real.Lemmas

open FirstOrder Filter
open scoped Topology

namespace OMA.S_mo_43900

inductive GroupFunction : ℕ → Type
  | identity : GroupFunction 0
  | inverse : GroupFunction 1
  | product : GroupFunction 2

abbrev groupLanguage : Language := ⟨GroupFunction, fun _ => Empty⟩

abbrev groupInterpretation (G : Type) [Group G] : groupLanguage.Structure G where
  funMap := fun {_} symbol =>
    match symbol with
    | .identity => fun _ => 1
    | .inverse => fun tuple => (tuple 0)⁻¹
    | .product => fun tuple => tuple 0 * tuple 1
  RelMap := fun {_} symbol => nomatch symbol

/-- A first-order definable set in an exhausted group can have no density
along the chosen ascending chain of finite subgroups. -/
theorem main :
    ∃ (G : Type) (group : Group G),
      letI := group
      letI := groupInterpretation G
      ∃ (levels : ℕ → Subgroup G) (arity : ℕ)
        (formula : groupLanguage.Formula (Fin arity)),
        Monotone levels ∧
        (∀ i, Finite ↥(levels i)) ∧
        (∀ g : G, ∃ i, g ∈ levels i) ∧
        ∀ limit : ℝ, ¬ Tendsto
          (fun i : ℕ =>
            ({tuple : Fin arity → ↥(levels i) |
              formula.Realize (fun j => (tuple j : G))}.ncard : ℝ) /
              (Nat.card (Fin arity → ↥(levels i)) : ℝ))
          atTop (𝓝 limit) := by
  sorry

end OMA.S_mo_43900
