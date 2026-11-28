import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.GroupTheory.Perm.Basic

namespace OMA.S_mo_61361

/-- The level and set of points identify an infinite orbit of the
stabilizer of an initial segment. -/
def orbitNodes (G : Subgroup (Equiv.Perm ℕ)) : Set (ℕ × Set ℕ) :=
  {node | node.2.Infinite ∧
    ∃ x : ℕ, node.2 = {y | ∃ g ∈ G, (∀ i : ℕ, i < node.1 → g i = i) ∧ g x = y}}

/-- Can every rooted tree on finite sequences of natural numbers be
realized by the successive infinite orbits of a transitive group? -/
theorem main :
    ∀ T : Set (List ℕ), [] ∈ T →
      (∀ u v : List ℕ, u <+: v → v ∈ T → u ∈ T) →
      ∃ (G : Subgroup (Equiv.Perm ℕ)) (f : T ≃ orbitNodes G),
        (∀ x y : ℕ, ∃ g ∈ G, g x = y) ∧
        (∀ u : T, (f u).val.1 = u.val.length) ∧
        ∀ u v : T, u.val <+: v.val ↔ (f u).val.1 ≤ (f v).val.1 ∧
          (f v).val.2 ⊆ (f u).val.2 := by
  sorry

end OMA.S_mo_61361
