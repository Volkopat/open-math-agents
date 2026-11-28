import OMAReductions.R_opg_black_and_white_cycle_conjecture_R1

-- Step opg-black-and-white-cycle-conjecture.R1.H1: hypothesis H1 of reduction opg-black-and-white-cycle-conjecture.R1
-- Credit: @lettucrisp

open OMA.S_opg_black_and_white_cycle_conjecture

namespace OMA.P_opg_black_and_white_cycle_conjecture_R1_H1

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

private lemma zmod2_natCast_eq_zero_iff (n : ℕ) : (n : ZMod 2) = 0 ↔ Even n := by
  rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]

private lemma zmod2_intCast_eq_zero_iff (x : ℤ) : (x : ZMod 2) = 0 ↔ Even x := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, even_iff_two_dvd]
  norm_cast

private lemma ite_eq_comm {α β : Type*} [DecidableEq α] (a b : α) (x y : β) :
    (if a = b then x else y) = if b = a then x else y := by
  by_cases h : a = b
  · subst h; simp
  · have h' : b ≠ a := Ne.symm h
    simp [h, h']

private lemma degIn_eq_sum {V E : Type*} [DecidableEq V]
    (src tgt : E → V) (C : Finset E) (v : V) :
    degIn src tgt C v =
      ∑ e ∈ C, ((if src e = v then 1 else 0) + (if tgt e = v then 1 else 0)) := by
  simp only [degIn, Finset.sum_add_distrib, Finset.card_filter]

private lemma degIn_disjoint_union {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) {A B : Finset E} (h : Disjoint A B) (v : V) :
    degIn src tgt (A ∪ B) v = degIn src tgt A v + degIn src tgt B v := by
  simp [degIn_eq_sum, Finset.sum_union h]

private lemma degIn_insert_of_notMem {V E : Type*} [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) {C : Finset E} {e : E} (he : e ∉ C) (v : V) :
    degIn src tgt (insert e C) v =
      degIn src tgt C v + ((if src e = v then 1 else 0) + (if tgt e = v then 1 else 0)) := by
  rw [degIn_eq_sum, Finset.sum_insert he, ← degIn_eq_sum, add_comm]

private lemma degIn_singleton {V E : Type*} [DecidableEq V]
    (src tgt : E → V) (e : E) (v : V) :
    degIn src tgt {e} v = (if src e = v then 1 else 0) + (if tgt e = v then 1 else 0) := by
  simp [degIn_eq_sum]

private def flowDiv {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (g : E → ℤ) (v : V) : ℤ :=
  (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), g e) -
    (∑ e ∈ Finset.univ.filter (fun e => src e = v), g e)

private lemma isConservative_iff_flowDiv {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (g : E → ℤ) :
    IsConservative src tgt g ↔ ∀ v, flowDiv src tgt g v = 0 := by
  simp [IsConservative, flowDiv, sub_eq_zero]

private lemma flowDiv_eq_sum {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (g : E → ℤ) (v : V) :
    flowDiv src tgt g v =
      ∑ e : E, ((if tgt e = v then g e else 0) - (if src e = v then g e else 0)) := by
  simp [flowDiv, Finset.sum_sub_distrib, Finset.sum_filter]

private lemma flowDiv_update_of_zero {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (g : E → ℤ) {e₀ : E} (h0 : g e₀ = 0) (c : ℤ) (v : V) :
    flowDiv src tgt (Function.update g e₀ c) v =
      flowDiv src tgt g v + ((if tgt e₀ = v then c else 0) - (if src e₀ = v then c else 0)) := by
  rw [flowDiv_eq_sum, flowDiv_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
  have hrest :
      ∑ x ∈ Finset.univ.erase e₀,
        ((if tgt x = v then Function.update g e₀ c x else 0) -
          (if src x = v then Function.update g e₀ c x else 0)) =
      ∑ x ∈ Finset.univ.erase e₀,
        ((if tgt x = v then g x else 0) - (if src x = v then g x else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hrest, Function.update_self, h0]
  simp only [ite_self, sub_self, zero_add]
  ring

private lemma sum_degIn_zmod2 {V E : Type*} [DecidableEq V]
    (src tgt : E → V) (B : Finset E) (S : Finset V) :
    (∑ v ∈ S, (degIn src tgt B v : ZMod 2)) =
      ((B.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card : ZMod 2) := by
  have h1 : ∀ v : V, (degIn src tgt B v : ZMod 2) =
      ∑ e ∈ B, ((if src e = v then (1 : ZMod 2) else 0) + (if tgt e = v then 1 else 0)) := by
    intro v
    rw [degIn_eq_sum]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro e _
    split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_comm]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl ?_
  intro e _
  rw [Finset.sum_add_distrib]
  have hs : (∑ v ∈ S, if src e = v then (1 : ZMod 2) else 0) = if src e ∈ S then 1 else 0 := by
    by_cases h : src e ∈ S
    · rw [if_pos h, Finset.sum_eq_single (src e)]
      · simp
      · intro v _ hv; simp [Ne.symm hv]
      · intro h'; exact (h' h).elim
    · rw [if_neg h, Finset.sum_eq_zero]
      intro v hv
      have hne : src e ≠ v := fun heq => h (heq ▸ hv)
      simp [hne]
  have ht : (∑ v ∈ S, if tgt e = v then (1 : ZMod 2) else 0) = if tgt e ∈ S then 1 else 0 := by
    by_cases h : tgt e ∈ S
    · rw [if_pos h, Finset.sum_eq_single (tgt e)]
      · simp
      · intro v _ hv; simp [Ne.symm hv]
      · intro h'; exact (h' h).elim
    · rw [if_neg h, Finset.sum_eq_zero]
      intro v hv
      have hne : tgt e ≠ v := fun heq => h (heq ▸ hv)
      simp [hne]
  rw [hs, ht]
  by_cases h1 : src e ∈ S <;> by_cases h2 : tgt e ∈ S <;> simp [h1, h2]
  exact zmod2_add_self 1

private lemma extend_to_closed {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (A : Finset E) (hA : ∀ v, Even (degIn src tgt A v)) :
    ∀ n : ℕ, ∀ (C : Finset E) (g : E → ℤ) (s u : V),
      (A \ C).card ≤ n →
      C ⊆ A →
      C.Nonempty →
      (∀ e ∈ C, g e = 1 ∨ g e = -1) →
      (∀ e ∉ C, g e = 0) →
      (∀ v, flowDiv src tgt g v = (if v = u then 1 else 0) - (if v = s then 1 else 0)) →
      (∀ v, (degIn src tgt C v : ZMod 2) =
        (if v = u then (1 : ZMod 2) else 0) + (if v = s then 1 else 0)) →
      ∃ C' : Finset E, ∃ g' : E → ℤ,
        C' ⊆ A ∧ C'.Nonempty ∧
        (∀ v, Even (degIn src tgt C' v)) ∧
        (∀ e ∈ C', g' e = 1 ∨ g' e = -1) ∧
        (∀ e ∉ C', g' e = 0) ∧
        IsConservative src tgt g' := by
  intro n
  induction n with
  | zero =>
    intro C g s u hcard hCA hCne hg_unit hg_zero hdiv hdeg
    have hAC_empty : A \ C = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    have hCA_eq : C = A := Finset.Subset.antisymm hCA (Finset.sdiff_eq_empty_iff_subset.mp hAC_empty)
    have hus : u = s := by
      by_contra hne
      have h1 : (degIn src tgt C u : ZMod 2) = 1 := by
        rw [hdeg u, if_pos rfl, if_neg hne, add_zero]
      have h0 : (degIn src tgt C u : ZMod 2) = 0 := by
        rw [hCA_eq, zmod2_natCast_eq_zero_iff]
        exact hA u
      rw [h0] at h1
      exact zero_ne_one h1
    refine ⟨C, g, hCA, hCne, ?_, hg_unit, hg_zero, ?_⟩
    · intro v
      rw [← zmod2_natCast_eq_zero_iff, hdeg v, hus]
      exact zmod2_add_self _
    · rw [isConservative_iff_flowDiv]
      intro v
      rw [hdiv v, hus, sub_self]
  | succ n ih =>
    intro C g s u hcard hCA hCne hg_unit hg_zero hdiv hdeg
    by_cases hus : u = s
    · refine ⟨C, g, hCA, hCne, ?_, hg_unit, hg_zero, ?_⟩
      · intro v
        rw [← zmod2_natCast_eq_zero_iff, hdeg v, hus]
        exact zmod2_add_self _
      · rw [isConservative_iff_flowDiv]
        intro v
        rw [hdiv v, hus, sub_self]
    · have hA_split : degIn src tgt A u = degIn src tgt C u + degIn src tgt (A \ C) u := by
        rw [← degIn_disjoint_union src tgt disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hCA]
      have hdiff_ne : degIn src tgt (A \ C) u ≠ 0 := by
        intro h0
        have hAu : (degIn src tgt A u : ZMod 2) = 0 := (zmod2_natCast_eq_zero_iff _).mpr (hA u)
        have hCu : (degIn src tgt C u : ZMod 2) = 1 := by
          rw [hdeg u, if_pos rfl, if_neg hus, add_zero]
        have hsum : (degIn src tgt A u : ZMod 2) = (degIn src tgt C u : ZMod 2) := by
          rw [hA_split, h0, add_zero]
        rw [hAu, hCu] at hsum
        exact zero_ne_one hsum
      have hex : ∃ e ∈ A \ C, src e = u ∨ tgt e = u := by
        by_contra hnone
        push Not at hnone
        apply hdiff_ne
        rw [degIn_eq_sum]
        refine Finset.sum_eq_zero ?_
        intro e he
        obtain ⟨hs, ht⟩ := hnone e he
        simp [hs, ht]
      obtain ⟨e, he_sdiff, he_inc⟩ := hex
      have heA : e ∈ A := (Finset.mem_sdiff.mp he_sdiff).1
      have heC : e ∉ C := (Finset.mem_sdiff.mp he_sdiff).2
      let C' : Finset E := insert e C
      have hC'A : C' ⊆ A := Finset.insert_subset heA hCA
      have hC'ne : C'.Nonempty := ⟨e, Finset.mem_insert_self e C⟩
      have hcard' : (A \ C').card ≤ n := by
        have hsub : A \ C' = (A \ C).erase e := by
          ext x; simp [C', and_left_comm]
        rw [hsub, Finset.card_erase_of_mem he_sdiff]
        omega
      rcases he_inc with hsrc | htgt
      · let g' := Function.update g e 1
        refine ih C' g' s (tgt e) hcard' hC'A hC'ne ?_ ?_ ?_ ?_
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxC
          · left; simp [g']
          · have hne : x ≠ e := fun h => heC (h ▸ hxC)
            simpa [g', hne] using hg_unit x hxC
        · intro x hx
          have hne : x ≠ e := fun h => hx (h ▸ Finset.mem_insert_self e C)
          have hxC : x ∉ C := fun h => hx (Finset.mem_insert_of_mem h)
          simpa [g', hne] using hg_zero x hxC
        · intro v
          rw [flowDiv_update_of_zero src tgt g (hg_zero e heC) 1 v, hdiv v, hsrc,
            ite_eq_comm (tgt e) v, ite_eq_comm u v]
          ring
        · intro v
          rw [degIn_insert_of_notMem src tgt heC v]
          push_cast
          rw [hdeg v, hsrc, ite_eq_comm u v, ite_eq_comm (tgt e) v]
          calc
            ((if v = u then (1 : ZMod 2) else 0) + (if v = s then 1 else 0)) +
                ((if v = u then 1 else 0) + (if v = tgt e then 1 else 0))
              = ((if v = u then (1 : ZMod 2) else 0) + (if v = u then 1 else 0)) +
                  ((if v = tgt e then 1 else 0) + (if v = s then 1 else 0)) := by ring
            _ = (if v = tgt e then 1 else 0) + (if v = s then 1 else 0) := by
                  rw [zmod2_add_self, zero_add]
      · let g' := Function.update g e (-1)
        refine ih C' g' s (src e) hcard' hC'A hC'ne ?_ ?_ ?_ ?_
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hxC
          · right; simp [g']
          · have hne : x ≠ e := fun h => heC (h ▸ hxC)
            simpa [g', hne] using hg_unit x hxC
        · intro x hx
          have hne : x ≠ e := fun h => hx (h ▸ Finset.mem_insert_self e C)
          have hxC : x ∉ C := fun h => hx (Finset.mem_insert_of_mem h)
          simpa [g', hne] using hg_zero x hxC
        · intro v
          rw [flowDiv_update_of_zero src tgt g (hg_zero e heC) (-1) v, hdiv v, htgt,
            ite_eq_comm u v, ite_eq_comm (src e) v]
          have hm1 : (if v = u then (-1 : ℤ) else 0) = -(if v = u then 1 else 0) := by
            split_ifs <;> rfl
          have hm2 : (if v = src e then (-1 : ℤ) else 0) = -(if v = src e then 1 else 0) := by
            split_ifs <;> rfl
          rw [hm1, hm2]
          ring
        · intro v
          rw [degIn_insert_of_notMem src tgt heC v]
          push_cast
          rw [hdeg v, htgt, ite_eq_comm (src e) v, ite_eq_comm u v]
          calc
            ((if v = u then (1 : ZMod 2) else 0) + (if v = s then 1 else 0)) +
                ((if v = src e then 1 else 0) + (if v = u then 1 else 0))
              = ((if v = u then (1 : ZMod 2) else 0) + (if v = u then 1 else 0)) +
                  ((if v = src e then 1 else 0) + (if v = s then 1 else 0)) := by ring
            _ = (if v = src e then 1 else 0) + (if v = s then 1 else 0) := by
                  rw [zmod2_add_self, zero_add]

private lemma exists_unit_flow_of_even {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) :
    ∀ n : ℕ, ∀ A : Finset E, A.card ≤ n → (∀ v, Even (degIn src tgt A v)) →
      ∃ g : E → ℤ, (∀ e ∈ A, g e = 1 ∨ g e = -1) ∧ (∀ e ∉ A, g e = 0) ∧
        IsConservative src tgt g := by
  intro n
  induction n with
  | zero =>
    intro A hcard _
    have hA : A = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro e he; simp [hA] at he
    · intro _ _; rfl
    · simp [IsConservative]
  | succ n ih =>
    intro A hcard hA
    by_cases hAne : A.Nonempty
    · obtain ⟨e₀, he₀⟩ := hAne
      let C₀ : Finset E := {e₀}
      let g₀ : E → ℤ := Function.update (fun _ => 0) e₀ 1
      have hdiv0 : ∀ v, flowDiv src tgt g₀ v =
          (if v = tgt e₀ then 1 else 0) - (if v = src e₀ then 1 else 0) := by
        intro v
        have hzero : flowDiv src tgt (fun _ => 0) v = 0 := by simp [flowDiv]
        rw [flowDiv_update_of_zero src tgt (fun _ => 0) rfl 1 v, hzero, zero_add,
          ite_eq_comm (tgt e₀) v, ite_eq_comm (src e₀) v]
      have hdeg0 : ∀ v, (degIn src tgt C₀ v : ZMod 2) =
          (if v = tgt e₀ then (1 : ZMod 2) else 0) + (if v = src e₀ then 1 else 0) := by
        intro v
        rw [degIn_singleton]
        push_cast
        rw [ite_eq_comm (src e₀) v, ite_eq_comm (tgt e₀) v]
        ring
      obtain ⟨C, g₁, hCA, hCne, hCeven, hg1_unit, hg1_zero, hg1_cons⟩ :=
        extend_to_closed src tgt A hA (A \ C₀).card C₀ g₀ (src e₀) (tgt e₀) le_rfl
          (Finset.singleton_subset_iff.mpr he₀) ⟨e₀, Finset.mem_singleton_self e₀⟩
          (by intro e he; left; simp [C₀] at he; simp [g₀, he])
          (by intro e he; simp [C₀] at he; simp [g₀, he])
          hdiv0 hdeg0
      have hcard_rem : (A \ C).card ≤ n := by
        have hpos : 0 < C.card := Finset.card_pos.mpr hCne
        have hsub : (A \ C).card = A.card - C.card := by rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hCA]
        omega
      have hrem_even : ∀ v, Even (degIn src tgt (A \ C) v) := by
        intro v
        rw [← zmod2_natCast_eq_zero_iff]
        have hsp : degIn src tgt A v = degIn src tgt C v + degIn src tgt (A \ C) v := by
          rw [← degIn_disjoint_union src tgt disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hCA]
        have hAv : (degIn src tgt A v : ZMod 2) = 0 := (zmod2_natCast_eq_zero_iff _).mpr (hA v)
        have hCv : (degIn src tgt C v : ZMod 2) = 0 := (zmod2_natCast_eq_zero_iff _).mpr (hCeven v)
        have hcast : (degIn src tgt A v : ZMod 2) =
            (degIn src tgt C v : ZMod 2) + (degIn src tgt (A \ C) v : ZMod 2) := by
          rw [hsp]; push_cast; rfl
        rw [hAv, hCv, zero_add] at hcast
        exact hcast.symm
      obtain ⟨g₂, hg2_unit, hg2_zero, hg2_cons⟩ := ih (A \ C) hcard_rem hrem_even
      refine ⟨fun e => g₁ e + g₂ e, ?_, ?_, ?_⟩
      · intro e heA
        dsimp only
        by_cases heC : e ∈ C
        · have heRem : e ∉ A \ C := by simp [heC]
          rw [hg2_zero e heRem, add_zero]
          exact hg1_unit e heC
        · have heRem : e ∈ A \ C := Finset.mem_sdiff.mpr ⟨heA, heC⟩
          rw [hg1_zero e heC, zero_add]
          exact hg2_unit e heRem
      · intro e heA
        dsimp only
        have heC : e ∉ C := fun h => heA (hCA h)
        have heRem : e ∉ A \ C := fun h => heA (Finset.mem_sdiff.mp h).1
        rw [hg1_zero e heC, hg2_zero e heRem, add_zero]
      · rw [isConservative_iff_flowDiv] at hg1_cons hg2_cons ⊢
        intro v
        have hadd : flowDiv src tgt (fun e => g₁ e + g₂ e) v =
            flowDiv src tgt g₁ v + flowDiv src tgt g₂ v := by
          simp [flowDiv, Finset.sum_add_distrib]
          ring
        rw [hadd, hg1_cons v, hg2_cons v, add_zero]
    · have hA_empty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
      refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · intro e he; simp [hA_empty] at he
      · intro _ _; rfl
      · simp [IsConservative]

private lemma odd_support_even_deg {V E : Type*} [Fintype E] [DecidableEq V]
    (src tgt : E → V) (f : E → ℤ) (hf : IsConservative src tgt f) :
    ∀ v, Even (degIn src tgt (Finset.univ.filter fun e => Odd (f e)) v) := by
  intro v
  rw [← zmod2_natCast_eq_zero_iff]
  have hcons : flowDiv src tgt f v = 0 := (isConservative_iff_flowDiv src tgt f).mp hf v
  have hmod : ((flowDiv src tgt f v : ℤ) : ZMod 2) = 0 := by rw [hcons]; simp
  rw [flowDiv_eq_sum] at hmod
  push_cast at hmod
  rw [degIn_eq_sum]
  push_cast
  rw [Finset.sum_filter]
  refine Eq.trans ?_ hmod
  refine Finset.sum_congr rfl ?_
  intro e _
  have hfe : (f e : ZMod 2) = if Odd (f e) then 1 else 0 := by
    by_cases ho : Odd (f e)
    · rw [if_pos ho]
      rcases zmod2_eq_zero_or_one (f e : ZMod 2) with h0 | h1
      · exfalso
        have hev : Even (f e) := (zmod2_intCast_eq_zero_iff _).mp h0
        exact (Int.not_even_iff_odd.mpr ho) hev
      · exact h1
    · rw [if_neg ho]
      exact (zmod2_intCast_eq_zero_iff _).mpr (Int.not_odd_iff_even.mp ho)
  by_cases ho : Odd (f e) <;> by_cases hs : src e = v <;> by_cases ht : tgt e = v <;>
    simp [ho, hs, ht, hfe]
  exact zmod2_add_self 1

private lemma toggle_edge_deg {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) {A C : Finset E} (hCA : C ⊆ A) {e : E} (he : e ∈ A) :
    let C' := if e ∈ C then C.erase e else insert e C
    C' ⊆ A ∧ ∀ v,
      (degIn src tgt (Aᶜ ∪ C') v : ZMod 2) =
        (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) +
          (if v = src e then 1 else 0) + (if v = tgt e then 1 else 0) := by
  intro C'
  have hC'A : C' ⊆ A := by
    dsimp [C']
    split_ifs
    · exact (Finset.erase_subset e C).trans hCA
    · exact Finset.insert_subset he hCA
  refine ⟨hC'A, ?_⟩
  intro v
  have hdC : Disjoint Aᶜ C := disjoint_compl_left.mono_right hCA
  have hdC' : Disjoint Aᶜ C' := disjoint_compl_left.mono_right hC'A
  rw [degIn_disjoint_union src tgt hdC', degIn_disjoint_union src tgt hdC]
  push_cast
  have hcs : (if src e = v then (1 : ZMod 2) else 0) = if v = src e then 1 else 0 :=
    ite_eq_comm (src e) v 1 0
  have hct : (if tgt e = v then (1 : ZMod 2) else 0) = if v = tgt e then 1 else 0 :=
    ite_eq_comm (tgt e) v 1 0
  by_cases heC : e ∈ C
  · simp only [C', if_pos heC]
    have hins : insert e (C.erase e) = C := Finset.insert_erase heC
    have hdeg := degIn_insert_of_notMem src tgt (Finset.notMem_erase e C) v
    rw [hins] at hdeg
    have hcast : (degIn src tgt C v : ZMod 2) =
        (degIn src tgt (C.erase e) v : ZMod 2) +
          ((if v = src e then (1 : ZMod 2) else 0) + (if v = tgt e then 1 else 0)) := by
      rw [hdeg]; push_cast; rw [hcs, hct]
    calc
      (degIn src tgt Aᶜ v : ZMod 2) + (degIn src tgt (C.erase e) v : ZMod 2)
        = (degIn src tgt Aᶜ v : ZMod 2) + (degIn src tgt (C.erase e) v : ZMod 2) +
            (((if v = src e then (1 : ZMod 2) else 0) + (if v = src e then 1 else 0)) +
             ((if v = tgt e then (1 : ZMod 2) else 0) + (if v = tgt e then 1 else 0))) := by
              rw [zmod2_add_self, zmod2_add_self, add_zero, add_zero]
      _ = (degIn src tgt Aᶜ v : ZMod 2) + (degIn src tgt C v : ZMod 2) +
            (if v = src e then 1 else 0) + (if v = tgt e then 1 else 0) := by
              rw [hcast]; ring
  · simp only [C', if_neg heC]
    rw [degIn_insert_of_notMem src tgt heC v]
    push_cast
    rw [hcs, hct]
    ring

private lemma toggle_path_deg {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (A : Finset E) {u w : V}
    (hreach : Relation.ReflTransGen
      (fun a b => ∃ e ∈ A, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) u w) :
    ∀ C : Finset E, C ⊆ A → ∃ C' : Finset E, C' ⊆ A ∧ ∀ v,
      (degIn src tgt (Aᶜ ∪ C') v : ZMod 2) =
        (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) +
          (if v = u then 1 else 0) + (if v = w then 1 else 0) := by
  induction hreach with
  | refl =>
    intro C hCA
    refine ⟨C, hCA, ?_⟩
    intro v
    rw [add_assoc, zmod2_add_self, add_zero]
  | @tail b c _ hbc ih =>
    intro C hCA
    obtain ⟨C₁, hC₁A, hdeg₁⟩ := ih C hCA
    obtain ⟨e, heA, hdir⟩ := hbc
    obtain ⟨hC₂A, hdeg₂⟩ := toggle_edge_deg src tgt hC₁A heA
    refine ⟨if e ∈ C₁ then C₁.erase e else insert e C₁, hC₂A, ?_⟩
    intro v
    rw [hdeg₂ v, hdeg₁ v]
    rcases hdir with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · calc
        (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
            (if v = src e then 1 else 0) + (if v = src e then 1 else 0) +
            (if v = tgt e then 1 else 0)
          = (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
              ((if v = src e then (1 : ZMod 2) else 0) + (if v = src e then 1 else 0)) +
              (if v = tgt e then 1 else 0) := by ring
        _ = (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
              (if v = tgt e then 1 else 0) := by rw [zmod2_add_self, add_zero]
    · calc
        (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
            (if v = tgt e then 1 else 0) + (if v = src e then 1 else 0) +
            (if v = tgt e then 1 else 0)
          = (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
              ((if v = tgt e then (1 : ZMod 2) else 0) + (if v = tgt e then 1 else 0)) +
              (if v = src e then 1 else 0) := by ring
        _ = (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) + (if v = u then 1 else 0) +
              (if v = src e then 1 else 0) := by rw [zmod2_add_self, add_zero]

private lemma exists_even_superset {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (src tgt : E → V) (A : Finset E)
    (hcut : ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
      Even ((Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card)) :
    ∀ n : ℕ, ∀ C : Finset E, C ⊆ A →
      (Finset.univ.filter fun v : V => (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) ≠ 0).card ≤ n →
      ∃ B : Finset E, (∀ v, Even (degIn src tgt B v)) ∧ ∀ e, e ∈ A ∨ e ∈ B := by
  classical
  intro n
  induction n with
  | zero =>
    intro C _ hcard
    have hempty : (Finset.univ.filter fun v : V => (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) ≠ 0) = ∅ :=
      Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    refine ⟨Aᶜ ∪ C, ?_, ?_⟩
    · intro v
      rw [← zmod2_natCast_eq_zero_iff]
      by_contra hne
      have hv : v ∈ Finset.univ.filter (fun v : V => (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) ≠ 0) := by
        simp [hne]
      rw [hempty] at hv
      exact Finset.notMem_empty v hv
    · intro e
      by_cases he : e ∈ A
      · exact Or.inl he
      · exact Or.inr (Finset.mem_union_left C (Finset.mem_compl.mpr he))
  | succ n ih =>
    intro C hCA hcard
    let oddSet := Finset.univ.filter (fun v : V => (degIn src tgt (Aᶜ ∪ C) v : ZMod 2) ≠ 0)
    have hcard_odd : oddSet.card ≤ n + 1 := hcard
    by_cases hne : oddSet.Nonempty
    · obtain ⟨u, hu⟩ := hne
      have hu_odd : (degIn src tgt (Aᶜ ∪ C) u : ZMod 2) = 1 := by
        have h := (Finset.mem_filter.mp hu).2
        rcases zmod2_eq_zero_or_one (degIn src tgt (Aᶜ ∪ C) u : ZMod 2) with h0 | h1
        · exact (h h0).elim
        · exact h1
      let rel : V → V → Prop := fun a b =>
        ∃ e ∈ A, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)
      let S : Finset V := Finset.univ.filter (fun v => Relation.ReflTransGen rel u v)
      have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ u, Relation.ReflTransGen.refl⟩
      have hSclosed : ∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S := by
        intro e heA
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h
          exact h.tail ⟨e, heA, Or.inl ⟨rfl, rfl⟩⟩
        · intro h
          exact h.tail ⟨e, heA, Or.inr ⟨rfl, rfl⟩⟩
      have hfilter_eq :
          ((Aᶜ ∪ C).filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) =
            (Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
        intro hcross
        by_cases heA : e ∈ A
        · exfalso
          have hiff := hSclosed e heA
          by_cases h1 : src e ∈ S
          · have h2 : tgt e ∈ S := hiff.mp h1
            simp [h1, h2] at hcross
          · have h2 : tgt e ∉ S := fun ht => h1 (hiff.mpr ht)
            simp [h1, h2] at hcross
        · exact Finset.mem_union_left C (Finset.mem_compl.mpr heA)
      have hsum0 : (∑ v ∈ S, (degIn src tgt (Aᶜ ∪ C) v : ZMod 2)) = 0 := by
        rw [sum_degIn_zmod2, hfilter_eq, zmod2_natCast_eq_zero_iff]
        exact hcut S hSclosed
      have hex_w : ∃ w ∈ S.erase u, (degIn src tgt (Aᶜ ∪ C) w : ZMod 2) ≠ 0 := by
        by_contra hnone
        push Not at hnone
        have hsum1 : (∑ v ∈ S, (degIn src tgt (Aᶜ ∪ C) v : ZMod 2)) = 1 := by
          rw [← Finset.add_sum_erase _ _ huS, hu_odd, Finset.sum_eq_zero hnone, add_zero]
        rw [hsum0] at hsum1
        exact zero_ne_one hsum1
      obtain ⟨w, hw_erase, hw_ne0⟩ := hex_w
      have hwu : w ≠ u := (Finset.mem_erase.mp hw_erase).1
      have hwS : w ∈ S := (Finset.mem_erase.mp hw_erase).2
      have hreach : Relation.ReflTransGen rel u w := (Finset.mem_filter.mp hwS).2
      have hw_odd : (degIn src tgt (Aᶜ ∪ C) w : ZMod 2) = 1 := by
        rcases zmod2_eq_zero_or_one (degIn src tgt (Aᶜ ∪ C) w : ZMod 2) with h0 | h1
        · exact (hw_ne0 h0).elim
        · exact h1
      obtain ⟨C', hC'A, hdeg'⟩ := toggle_path_deg src tgt A hreach C hCA
      let oddSet' := Finset.univ.filter (fun v : V => (degIn src tgt (Aᶜ ∪ C') v : ZMod 2) ≠ 0)
      have hsub : oddSet' ⊆ oddSet.erase u := by
        intro v hv
        have hv' := (Finset.mem_filter.mp hv).2
        have hvu : v ≠ u := by
          intro heq
          rw [heq] at hv'
          apply hv'
          rw [hdeg' u, hu_odd, if_pos rfl, if_neg hwu.symm, add_zero]
          exact zmod2_add_self 1
        refine Finset.mem_erase.mpr ⟨hvu, Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩⟩
        by_cases hvw : v = w
        · rw [hvw] at hv'
          exfalso
          apply hv'
          rw [hdeg' w, hw_odd, if_neg hwu, if_pos rfl, add_zero]
          exact zmod2_add_self 1
        · simpa [hdeg' v, hvu, hvw] using hv'
      have hcard' : oddSet'.card ≤ n := by
        have h1 : oddSet'.card ≤ (oddSet.erase u).card := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hu] at h1
        have hpos : 0 < oddSet.card := Finset.card_pos.mpr ⟨u, hu⟩
        omega
      exact ih C' hC'A hcard'
    · have hempty : oddSet = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      refine ⟨Aᶜ ∪ C, ?_, ?_⟩
      · intro v
        rw [← zmod2_natCast_eq_zero_iff]
        by_contra h0
        have hv : v ∈ oddSet := Finset.mem_filter.mpr ⟨Finset.mem_univ v, h0⟩
        rw [hempty] at hv
        exact Finset.notMem_empty v hv
      · intro e
        by_cases he : e ∈ A
        · exact Or.inl he
        · exact Or.inr (Finset.mem_union_left C (Finset.mem_compl.mpr he))

private lemma hasNZ4Flow_iff_cut_parity {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (src tgt : E → V) :
    HasNZ4Flow src tgt ↔
      ∃ A : Finset E, (∀ v, Even (degIn src tgt A v)) ∧
        ∀ S : Finset V, (∀ e ∈ A, src e ∈ S ↔ tgt e ∈ S) →
          Even ((Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)).card) := by
  classical
  constructor
  · rintro ⟨f, hf_bnd, hf_cons⟩
    let A : Finset E := Finset.univ.filter (fun e => Odd (f e))
    have hA_even : ∀ v, Even (degIn src tgt A v) := odd_support_even_deg src tgt f hf_cons
    obtain ⟨g, hg_unit, hg_zero, hg_cons⟩ :=
      exists_unit_flow_of_even src tgt A.card A le_rfl hA_even
    let h : E → ℤ := fun e => (f e - g e) / 2
    have h2 : ∀ e, 2 * h e = f e - g e := by
      intro e
      have hev : Even (f e - g e) := by
        by_cases heA : e ∈ A
        · have hfo : Odd (f e) := (Finset.mem_filter.mp heA).2
          have hgo : Odd (g e) := by
            rcases hg_unit e heA with h1 | hm1
            · rw [h1]; exact ⟨0, by norm_num⟩
            · rw [hm1]; exact ⟨-1, by norm_num⟩
          exact hfo.sub_odd hgo
        · have hfe : Even (f e) := Int.not_odd_iff_even.mp (by simpa [A] using heA)
          rw [hg_zero e heA, sub_zero]
          exact hfe
      obtain ⟨k, hk⟩ := hev
      dsimp [h]
      omega
    have hh_cons : IsConservative src tgt h := by
      rw [isConservative_iff_flowDiv] at hf_cons hg_cons ⊢
      intro v
      have h2div : 2 * flowDiv src tgt h v = flowDiv src tgt f v - flowDiv src tgt g v := by
        simp only [flowDiv, mul_sub, Finset.mul_sum]
        have hsum_t : ∑ e ∈ Finset.univ.filter (fun e => tgt e = v), 2 * h e =
            (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), f e) -
            (∑ e ∈ Finset.univ.filter (fun e => tgt e = v), g e) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun e _ => h2 e
        have hsum_s : ∑ e ∈ Finset.univ.filter (fun e => src e = v), 2 * h e =
            (∑ e ∈ Finset.univ.filter (fun e => src e = v), f e) -
            (∑ e ∈ Finset.univ.filter (fun e => src e = v), g e) := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun e _ => h2 e
        rw [hsum_t, hsum_s]
        ring
      rw [hf_cons v, hg_cons v, sub_self] at h2div
      omega
    let B : Finset E := Finset.univ.filter (fun e => Odd (h e))
    have hB_even : ∀ v, Even (degIn src tgt B v) := odd_support_even_deg src tgt h hh_cons
    have hAB : ∀ e, e ∉ A → e ∈ B := by
      intro e heA
      have hfe : Even (f e) := Int.not_odd_iff_even.mp (by simpa [A] using heA)
      have hbnd := hf_bnd e
      have hg0 : g e = 0 := hg_zero e heA
      have h2e := h2 e
      rw [hg0, sub_zero] at h2e
      have hhe : h e = 1 ∨ h e = -1 := by
        obtain ⟨k, hk⟩ := hfe
        have h1 : |f e| = 2 := by
          have := hbnd.1; have := hbnd.2
          rcases abs_cases (f e) with ⟨hpos, _⟩ | ⟨hneg, _⟩ <;> omega
        rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.mp h1 with hf2 | hfm2 <;> omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_⟩
      rcases hhe with h1 | hm1
      · rw [h1]; exact ⟨0, by norm_num⟩
      · rw [hm1]; exact ⟨-1, by norm_num⟩
    refine ⟨A, hA_even, ?_⟩
    intro S hSclosed
    rw [← zmod2_natCast_eq_zero_iff]
    have hfilter_eq :
        (Finset.univ.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) =
          (B.filter fun e => decide (src e ∈ S) != decide (tgt e ∈ S)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_and_self]
      intro hcross
      apply hAB e
      intro heA
      have hiff := hSclosed e heA
      by_cases h1 : src e ∈ S
      · have h2 := hiff.mp h1; simp [h1, h2] at hcross
      · have h2 : tgt e ∉ S := fun ht => h1 (hiff.mpr ht); simp [h1, h2] at hcross
    rw [hfilter_eq, ← sum_degIn_zmod2]
    refine Finset.sum_eq_zero ?_
    intro v _
    exact (zmod2_natCast_eq_zero_iff _).mpr (hB_even v)
  · rintro ⟨A, hA_even, hA_cut⟩
    obtain ⟨B, hB_even, hAB⟩ :=
      exists_even_superset src tgt A hA_cut (Fintype.card V) ∅ (Finset.empty_subset A)
        (Finset.card_le_univ _)
    obtain ⟨g₁, hg1_unit, hg1_zero, hg1_cons⟩ :=
      exists_unit_flow_of_even src tgt A.card A le_rfl hA_even
    obtain ⟨g₂, hg2_unit, hg2_zero, hg2_cons⟩ :=
      exists_unit_flow_of_even src tgt B.card B le_rfl hB_even
    refine ⟨fun e => g₁ e + 2 * g₂ e, ?_, ?_⟩
    · intro e
      by_cases heA : e ∈ A <;> by_cases heB : e ∈ B
      · rcases hg1_unit e heA with h1 | h1 <;> rcases hg2_unit e heB with h2 | h2 <;>
          simp [h1, h2]
      · rcases hg1_unit e heA with h1 | h1 <;> simp [h1, hg2_zero e heB]
      · rcases hg2_unit e heB with h2 | h2 <;> simp [hg1_zero e heA, h2]
      · exfalso
        rcases hAB e with h | h
        · exact heA h
        · exact heB h
    · rw [isConservative_iff_flowDiv] at hg1_cons hg2_cons ⊢
      intro v
      have hlin : flowDiv src tgt (fun e => g₁ e + 2 * g₂ e) v =
          flowDiv src tgt g₁ v + 2 * flowDiv src tgt g₂ v := by
        simp only [flowDiv, Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [hlin, hg1_cons v, hg2_cons v]
      ring

end OMA.P_opg_black_and_white_cycle_conjecture_R1_H1

theorem OMA.solution : OMA.R_opg_black_and_white_cycle_conjecture_R1.H1 := by
  intro V E _ _ _ _ src tgt hole
  cases hole with
  | none =>
    simpa [Finset.subset_univ] using
      OMA.P_opg_black_and_white_cycle_conjecture_R1_H1.hasNZ4Flow_iff_cut_parity src tgt
  | some e₀ =>
    dsimp only [IsWhite]
    rw [OMA.P_opg_black_and_white_cycle_conjecture_R1_H1.hasNZ4Flow_iff_cut_parity]
    let emb : {d : E // d ≠ e₀} ↪ E := ⟨Subtype.val, Subtype.val_injective⟩
    have hdeg_map : ∀ (A' : Finset {d : E // d ≠ e₀}) (v : V),
        degIn (fun d : {d : E // d ≠ e₀} => src d.1) (fun d => tgt d.1) A' v =
          degIn src tgt (A'.map emb) v := by
      intro A' v
      simp only [degIn, Finset.filter_map, Finset.card_map, emb, Function.Embedding.coeFn_mk]
      rfl
    have hcut_eq : ∀ S : Finset V,
        (Finset.univ.filter fun d : {d : E // d ≠ e₀} =>
          decide (src d.1 ∈ S) != decide (tgt d.1 ∈ S)).card =
        ((Finset.univ.erase e₀).filter fun e : E =>
          decide (src e ∈ S) != decide (tgt e ∈ S)).card := by
      intro S
      rw [← Finset.card_map emb]
      congr 1
      ext e
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, and_true, emb, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨d, hd⟩, hcross, rfl⟩
        exact ⟨hd, hcross⟩
      · rintro ⟨hd, hcross⟩
        exact ⟨⟨e, hd⟩, hcross, rfl⟩
    constructor
    · rintro ⟨A', hA'_even, hA'_cut⟩
      refine ⟨A'.map emb, ?_, ?_, ?_⟩
      · intro e he
        rcases Finset.mem_map.mp he with ⟨⟨d, hd⟩, _, rfl⟩
        exact Finset.mem_erase.mpr ⟨hd, Finset.mem_univ d⟩
      · intro v
        rw [← hdeg_map A' v]
        exact hA'_even v
      · intro S hS
        rw [← hcut_eq S]
        apply hA'_cut S
        intro d hd
        exact hS d.1 (Finset.mem_map.mpr ⟨d, hd, rfl⟩)
    · rintro ⟨A, hA_sub, hA_even, hA_cut⟩
      let A' : Finset {d : E // d ≠ e₀} := Finset.univ.filter (fun d => d.1 ∈ A)
      have hmap : A'.map emb = A := by
        ext e
        simp only [A', Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          emb, Function.Embedding.coeFn_mk]
        constructor
        · rintro ⟨d, hd, rfl⟩; exact hd
        · intro heA
          have hne : e ≠ e₀ := (Finset.mem_erase.mp (hA_sub heA)).1
          exact ⟨⟨e, hne⟩, heA, rfl⟩
      refine ⟨A', ?_, ?_⟩
      · intro v
        rw [hdeg_map A' v, hmap]
        exact hA_even v
      · intro S hS
        rw [hcut_eq S]
        apply hA_cut S
        intro e heA
        have hne : e ≠ e₀ := (Finset.mem_erase.mp (hA_sub heA)).1
        exact hS ⟨e, hne⟩ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, heA⟩)
