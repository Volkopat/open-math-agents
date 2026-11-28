import OMAStatements.S_opg_atomicity_of_the_poset_of_multifuncoids_0
import Mathlib

/-!
Counterexample to atomisticity for multifuncoids on natural-number-indexed
families of subsets of Bool. The condition that false occurs at arbitrarily
large coordinates is unchanged by any one-coordinate update.
-/

namespace OMA.PortonMultifuncoid

open Set
open OMA.S_opg_atomicity_of_the_poset_of_multifuncoids_0 (IsMultifuncoid IsMFAtom val)

private def frequentFalse (L : ℕ → Set Bool) : Prop :=
  ∀ n : ℕ, ∃ j ≥ n, false ∈ L j

private theorem frequentFalse_update (L : ℕ → Set Bool) (i : ℕ) (X : Set Bool) :
    frequentFalse (Function.update L i X) ↔ frequentFalse L := by
  constructor
  · intro h n
    obtain ⟨j, hj, hj'⟩ := h (max n (i+1))
    have hne : j ≠ i := by have := (le_max_right n (i+1)).trans hj; omega
    exact ⟨j, (le_max_left n (i+1)).trans hj,
      by simpa only [Function.update_of_ne hne] using hj'⟩
  · intro h n
    obtain ⟨j, hj, hj'⟩ := h (max n (i+1))
    have hne : j ≠ i := by have := (le_max_right n (i+1)).trans hj; omega
    exact ⟨j, (le_max_left n (i+1)).trans hj,
      by simpa only [Function.update_of_ne hne] using hj'⟩

private def restricted (a : Set (ℕ → Set Bool)) : Set (ℕ → Set Bool) :=
  {L | L ∈ a ∧ frequentFalse L}

private theorem restricted_multifuncoid {a : Set (ℕ → Set Bool)}
    (ha : IsMultifuncoid a) : IsMultifuncoid (restricted a) := by
  refine ⟨?_, ?_⟩
  · intro L M hLM hL
    refine ⟨ha.1 hLM hL.1, fun n => ?_⟩
    obtain ⟨j, hj, hj'⟩ := hL.2 n
    exact ⟨j, hj, hLM j hj'⟩
  · intro i L
    refine ⟨fun h => (ha.2 i L).1 h.1, ?_⟩
    intro X Y
    have h := (ha.2 i L).2 X Y
    change Function.update L i (X ∪ Y) ∈ a ↔
      Function.update L i X ∈ a ∨ Function.update L i Y ∈ a at h
    change (Function.update L i (X ∪ Y) ∈ a ∧ frequentFalse (Function.update L i (X ∪ Y))) ↔
      (Function.update L i X ∈ a ∧ frequentFalse (Function.update L i X)) ∨
      (Function.update L i Y ∈ a ∧ frequentFalse (Function.update L i Y))
    simp only [frequentFalse_update, h]
    tauto

private def nonemptyTuples : Set (ℕ → Set Bool) := {L | ∀ i, (L i).Nonempty}

private theorem nonempty_multifuncoid : IsMultifuncoid nonemptyTuples := by
  refine ⟨?_, ?_⟩
  · intro L M hLM hL j
    exact (hL j).mono (hLM j)
  · intro i L
    have hval (X : Set Bool) : X ∈ val nonemptyTuples i L ↔
        X.Nonempty ∧ ∀ j, j ≠ i → (L j).Nonempty := by
      change (∀ j, (Function.update L i X j).Nonempty) ↔
        X.Nonempty ∧ ∀ j, j ≠ i → (L j).Nonempty
      constructor
      · intro h
        exact ⟨by simpa using h i, fun j hj => by simpa [Function.update_of_ne hj] using h j⟩
      · rintro ⟨hX,hL⟩ j
        by_cases h : j = i
        · subst j
          simpa using hX
        · simpa [Function.update_of_ne h] using hL j h
    refine ⟨by simp [hval], fun X Y => ?_⟩
    simp only [hval, Set.union_nonempty]
    tauto

private theorem any_atom_frequent {a : Set (ℕ → Set Bool)} (ha : IsMFAtom a) :
    ∀ L ∈ a, frequentFalse L := by
  have htop : (fun _ : ℕ => (Set.univ : Set Bool)) ∈ a := by
    obtain ⟨L,hL⟩ := Set.nonempty_iff_ne_empty.mpr ha.2.1
    exact ha.1.1 (show L ≤ fun _ => Set.univ from fun _ => Set.subset_univ _) hL
  have hne : restricted a ≠ ∅ := by
    apply Set.nonempty_iff_ne_empty.mp
    exact ⟨_, htop, fun n => ⟨n,le_rfl,Set.mem_univ _⟩⟩
  have heq : restricted a = a :=
    (ha.2.2 (restricted a) (restricted_multifuncoid ha.1) (fun _ h => h.1)).resolve_left hne
  intro L h
  have hr : L ∈ restricted a := heq.symm ▸ h
  exact hr.2

end OMA.PortonMultifuncoid

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_atomicity_of_the_poset_of_multifuncoids_0.main) := by
  intro h
  have h0 := OMA.PortonMultifuncoid.nonempty_multifuncoid
  have hg := OMA.PortonMultifuncoid.restricted_multifuncoid h0
  have hsub := (h Bool ℕ).2 _ h0 _ hg (by
    intro a ha haf L hL
    exact ⟨haf hL, OMA.PortonMultifuncoid.any_atom_frequent ha L hL⟩)
  have hc := hsub (show (fun _ : ℕ => ({true} : Set Bool)) ∈
      OMA.PortonMultifuncoid.nonemptyTuples from fun _ => ⟨true, by simp⟩)
  obtain ⟨j, _, hj⟩ := hc.2 0
  simp at hj
