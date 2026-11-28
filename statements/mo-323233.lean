import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OMA.S_mo_323233

/-- In an irreducible finite-rank Coxeter system, the centralizer of
each Coxeter element is the cyclic subgroup it generates. -/
theorem main :
    ∀ (ι : Type*) [Finite ι] [Nonempty ι] (W : Type*) [Group W]
      (M : CoxeterMatrix ι) (S : CoxeterSystem M W),
      (∀ A : Set ι, A.Nonempty → A ≠ Set.univ →
        ∃ i ∈ A, ∃ j ∉ A, M i j ≠ 2) →
      ∀ word : List ι, word.Nodup → (∀ i : ι, i ∈ word) →
        Subgroup.centralizer ({S.wordProd word} : Set W) =
          Subgroup.zpowers (S.wordProd word) := by
  sorry

end OMA.S_mo_323233
