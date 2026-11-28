import OMAStatements.S_mo_264107
import Mathlib

-- Problem: mo-264107 Moebius function via coatoms (crosscut)
-- Upstream: formal-conjectures statements/mo-264107.lean:0 (declaration OMA.S_mo_264107.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_mo_264107 in
theorem OMA.solution : type_of% @OMA.S_mo_264107.main := by
  intro L _ _ _ μ hμtop hμ
  classical
  have hmemSU : ∀ a b : L, b ∈ strictUpper a ↔ a < b := by
    intro a b
    unfold strictUpper
    simp
  have hmemC : ∀ c : L, c ∈ (coatoms : Finset L) ↔ IsCoatom c := by
    intro c
    unfold coatoms
    simp
  have hν : ∀ a : L, coatomSum a =
      ∑ S ∈ (coatoms : Finset L).powerset, if S.inf id = a then (-1 : ℤ) ^ S.card else 0 := by
    intro a
    unfold coatomSum
    apply Finset.sum_congr rfl
    intro S _
    congr
  have K : ∀ a : L, ∑ b ∈ Finset.univ.filter (fun b => a ≤ b), coatomSum b
      = if a = ⊤ then 1 else 0 := by
    intro a
    simp only [hν]
    rw [Finset.sum_comm]
    have h1 : ∀ S ∈ (coatoms : Finset L).powerset,
        (∑ b ∈ Finset.univ.filter (fun b => a ≤ b),
          if S.inf id = b then (-1 : ℤ) ^ S.card else 0)
        = if S ⊆ (coatoms : Finset L).filter (fun c => a ≤ c) then (-1 : ℤ) ^ S.card else 0 := by
      intro S hS
      rw [Finset.sum_ite_eq]
      have h : S.inf id ∈ Finset.univ.filter (fun b => a ≤ b)
          ↔ S ⊆ (coatoms : Finset L).filter (fun c => a ≤ c) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.le_inf_iff, id]
        constructor
        · intro h c hc
          exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mp hS hc, h c hc⟩
        · intro h c hc
          exact (Finset.mem_filter.mp (h hc)).2
      simp only [h]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    have h2 : (coatoms : Finset L).powerset.filter
        (fun S => S ⊆ (coatoms : Finset L).filter (fun c => a ≤ c))
        = ((coatoms : Finset L).filter (fun c => a ≤ c)).powerset := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩
    rw [h2, Finset.sum_powerset_neg_one_pow_card]
    have h3 : (coatoms : Finset L).filter (fun c => a ≤ c) = ∅ ↔ a = ⊤ := by
      constructor
      · intro h
        rcases eq_top_or_exists_le_coatom a with h' | ⟨c, hc, hac⟩
        · exact h'
        · exfalso
          have hc' : c ∈ (coatoms : Finset L).filter (fun c => a ≤ c) :=
            Finset.mem_filter.mpr ⟨(hmemC c).mpr hc, hac⟩
          rw [h] at hc'
          exact Finset.notMem_empty _ hc'
      · intro h
        subst h
        apply Finset.filter_eq_empty_iff.mpr
        intro c hc htop
        exact ((hmemC c).mp hc).1 (top_le_iff.mp htop)
    simp only [h3]
  intro a
  refine WellFoundedGT.induction (motive := fun a => μ a = coatomSum a) a ?_
  intro a ih
  by_cases ha : a = ⊤
  · subst ha
    rw [hμtop]
    have k := K ⊤
    have e : Finset.univ.filter (fun b => (⊤ : L) ≤ b) = {⊤} := by
      ext b
      simp [top_le_iff]
    rw [e, Finset.sum_singleton, if_pos rfl] at k
    exact k.symm
  · have k := K a
    rw [if_neg ha] at k
    have e : Finset.univ.filter (fun b => a ≤ b) = insert a (strictUpper a) := by
      ext b
      simp [hmemSU, le_iff_eq_or_lt, eq_comm]
    have hna : a ∉ strictUpper a := by simp [hmemSU]
    rw [e, Finset.sum_insert hna] at k
    rw [hμ a ha]
    have h4 : ∑ b ∈ strictUpper a, μ b = ∑ b ∈ strictUpper a, coatomSum b :=
      Finset.sum_congr rfl (fun b hb => ih b ((hmemSU a b).mp hb))
    rw [h4]
    linarith
