import OMAStatements.S_mo_364520
import Mathlib

-- Retains @caa1982’s uniform-matroid counterexample from PR #27465.
-- Counts its three-element circuits using the standard finite-subset formula.

open OMA.S_mo_364520

/-- The uniform matroid `U_{2,4}` on `Fin 4`. -/
noncomputable def mo364520_U : Matroid (Fin 4) :=
  (IndepMatroid.ofFinite (E := Set.univ) Set.finite_univ (fun I => I.ncard ≤ 2)
    (by simp)
    (fun I J hJ hIJ => le_trans (Set.ncard_le_ncard hIJ) hJ)
    (fun I J hI hJ hlt => by
      have hne : ¬ J ⊆ I := fun h => absurd (Set.ncard_le_ncard h) (not_le.mpr hlt)
      obtain ⟨e, heJ, heI⟩ := Set.not_subset.mp hne
      refine ⟨e, heJ, heI, ?_⟩
      have := Set.ncard_insert_le e I
      omega)
    (fun I _ => Set.subset_univ I)).matroid

lemma mo364520_indep (I : Set (Fin 4)) : mo364520_U.Indep I ↔ I.ncard ≤ 2 := by
  simp [mo364520_U]

lemma mo364520_E : mo364520_U.E = Set.univ := rfl

lemma mo364520_circuit (C : Set (Fin 4)) : mo364520_U.IsCircuit C ↔ C.ncard = 3 := by
  rw [Matroid.isCircuit_iff_forall_ssubset]
  constructor
  · rintro ⟨hd, hs⟩
    have h1 : ¬ C.ncard ≤ 2 := by
      intro h; exact hd.not_indep ((mo364520_indep C).mpr h)
    by_contra h3
    have h4 : 4 ≤ C.ncard := by omega
    obtain ⟨e, he⟩ : C.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    have hlt : C \ {e} ⊂ C := Set.sdiff_singleton_ssubset.mpr he
    have hi := (mo364520_indep _).mp (hs hlt)
    have := Set.ncard_sdiff_singleton_of_mem he
    omega
  · intro h
    refine ⟨⟨fun hi => by rw [mo364520_indep] at hi; omega, Set.subset_univ C⟩, ?_⟩
    intro I hI
    rw [mo364520_indep]
    have := Set.ncard_lt_ncard hI
    omega

lemma mo364520_base : mo364520_U.IsBase {0, 1} := by
  rw [Matroid.isBase_iff_maximal_indep]
  refine ⟨(mo364520_indep _).mpr (by rw [Set.ncard_pair (by decide)]), ?_⟩
  intro J hJ hsub
  rw [mo364520_indep] at hJ
  have h2 : ({0, 1} : Set (Fin 4)).ncard = 2 := Set.ncard_pair (by decide)
  have := Set.eq_of_subset_of_ncard_le hsub (by omega)
  rw [this]

lemma mo364520_count : {C : Set (Fin 4) | C.ncard = 3}.ncard = 4 := by
  simpa using Set.ncard_powerset_ncard (Set.finite_univ : (Set.univ : Set (Fin 4)).Finite) 3

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_364520.main) := by
  intro hmain
  have hcirc : {C | mo364520_U.IsCircuit C ∧ C.ncard = 3} = {C : Set (Fin 4) | C.ncard = 3} := by
    ext C
    simp only [Set.mem_setOf_eq, mo364520_circuit]
    tauto
  have := hmain (Fin 4) mo364520_U 2 3 (Set.toFinite _)
    ⟨{0, 1}, mo364520_base, Set.ncard_pair (by decide)⟩ (by decide)
    ⟨{0, 1, 2}, (mo364520_circuit _).mpr (by
        rw [Set.ncard_eq_toFinset_card']; decide), by
        rw [Set.ncard_eq_toFinset_card']; decide⟩
    (fun C hC => by rw [(mo364520_circuit C).mp hC])
  rw [hcirc, mo364520_count, mo364520_E, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this
  omega
