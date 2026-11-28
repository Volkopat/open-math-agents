import OMAStatements.S_mo_16670
import Mathlib

open OMA.S_mo_16670 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_16670.main) := fun h => by
  have P (n : ℕ) : probabilityPerron (0 : NatMatrix (n + 1)) 0 (Pi.single 0 1) :=
    ⟨fun i => by by_cases i = 0 <;> simp [*], by simp, by simp; rfl, fun z hz => by simp_all⟩
  have G (n : ℕ) : generatedGroup (Pi.single 0 1 : Fin (n + 1) → ℝ) = AddSubgroup.closure {1} :=
    le_antisymm ((AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => by by_cases i = 0 <;> simp [*]))
      ((AddSubgroup.closure_le _).2 (Set.singleton_subset_iff.2 (AddSubgroup.subset_closure ⟨0, by simp⟩)))
  exact Set.infinite_range_of_injective (f := fun n => (⟨n + 1, 0⟩ : Σ k, NatMatrix k)) (fun n m e => by simpa using congrArg Sigma.fst e)
    ((h 1 0 0 _ (P 0)).subset (Set.range_subset_iff.2 fun n => ⟨_, P n, (G n).trans (G 0).symm⟩))
