import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-! The points on heavy rows give 61 columns. The remaining points must partition
the uncovered pairs of light rows into 50 cliques of order eight. -/
-- Credit: @VestigeClub
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2

open Finset
open scoped Classical

private lemma filtered_map_card {α β : Type*} (f : α ↪ β) (u : Finset α)
    (P : β → Prop) [DecidablePred P] :
    ((u.map f).filter P).card = (u.filter fun p => P (f p)).card := by
  classical
  rw [Finset.filter_map, Finset.card_map]
  congr 1

private lemma split_filter_count {α : Type*} [Fintype α] [DecidableEq α] (u : Finset α)
    (P : α → Prop) [DecidablePred P] :
    (u.filter P).card + (uᶜ.filter P).card = (univ.filter P).card := by
  classical
  have disj : Disjoint (u.filter P) (uᶜ.filter P) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hy).1) (Finset.mem_filter.mp hx).1
  rw [← Finset.card_union_of_disjoint disj, ← Finset.filter_union]
  simp

def H1 : Prop :=
  ∀ E : Fin 8 → Fin 111 → Bool,
    let d (p : Fin 111) := (univ.filter fun a => E a p = true).card
    (∀ a, (univ.filter fun p => E a p = true).card = 11) →
    (∀ a b, a ≠ b → ∃! p, E a p = true ∧ E b p = true) →
    (∀ p, d p ≤ 3) → (univ.filter fun p => d p = 3).card = 1 →
    (univ.filter fun p => ∃ a, E a p = true).card = 61

def H2 : Prop :=
  let R := Fin 8 ⊕ Fin 72
  let a (x : Finset R) := (univ.filter fun i : Fin 8 => Sum.inl i ∈ x).card
  let b (x : Finset R) := (univ.filter fun i : Fin 72 => Sum.inr i ∈ x).card
  ¬ ∃ (v s c : Finset (Finset R)),
    v.card = 61 ∧ s ⊆ v ∧ s.card = 16 ∧ c.card = 50 ∧
    (∀ x ∈ s, a x = 2 ∧ b x = 9) ∧
    (∀ x ∈ v, x ∉ s → 0 < a x ∧ a x ≤ 3 ∧ 2 * a x + b x = 8) ∧
    (v.filter fun x => a x = 3).card = 1 ∧
    (∀ i : Fin 8, (s.filter fun x => Sum.inl i ∈ x).card = 4) ∧
    (∀ i : Fin 72, (s.filter fun x => Sum.inr i ∈ x).card = 2) ∧
    (∀ k ∈ c, a k = 0 ∧ b k = 8) ∧
    (∀ r : R, (v.filter fun x => r ∈ x).card + (c.filter fun k => r ∈ k).card = 11) ∧
    (∀ r t : R, r ≠ t → (v.filter fun x => r ∈ x ∧ t ∈ x).card +
      (c.filter fun k => r ∈ k ∧ t ∈ k).card = 1)

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1.H1 := by
  classical
  rintro hCount hNo ⟨M, S, hS, hRows, hHeavy, hLight, hInside, hOutside,
    hMeet, hLinear, hMax, hSingle⟩
  let P := Fin 111
  let R := Fin 8 ⊕ Fin 72
  let A (p : P) := univ.filter fun i : Fin 8 => M (.inl i) p = true
  let B (p : P) := univ.filter fun i : Fin 72 => M (.inr i) p = true
  let F (p : P) := univ.filter fun r : R => M r p = true
  let U : Finset P := univ.filter fun p => ∃ a : Fin 8, M (.inl a) p = true
  have memU (p : P) : p ∈ U ↔ (A p).Nonempty := by simp [U, A, Finset.Nonempty]
  have maxDegree (p : P) : (A p).card ≤ 3 := by
    by_cases hp : p ∈ S
    · have h : (A p).card = 2 := (hInside p hp).1
      omega
    · exact hMax p hp
  have triple : (univ.filter fun p => (A p).card = 3).card = 1 := by
    convert hSingle using 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨fun hp => ?_, h⟩
      have h' : (A p).card = 2 := (hInside p hp).1
      omega
    · exact And.right
  have countU : U.card = 61 := hCount (fun a p => M (.inl a) p)
    (fun a => hRows (.inl a)) (fun _ _ h => hMeet _ _ (fun e => h (Sum.inl.inj e))) maxDegree triple
  have sU : S ⊆ U := by
    intro p hp
    apply (memU p).2
    apply Finset.card_pos.mp
    have h : (A p).card = 2 := (hInside p hp).1
    omega
  have cardB (p : P) : 1 < (B p).card := by
    by_cases hp : p ∈ S
    · have h : (B p).card = 9 := (hInside p hp).2
      omega
    · have h : 2 * (A p).card + (B p).card = 8 := hOutside p hp
      have := maxDegree p
      omega
  have injective : Function.Injective F := by
    intro p q same
    by_contra hpq
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (cardB p)
    have onBoth (k : Fin 72) (hk : k ∈ B p) : M (.inr k) p = true ∧ M (.inr k) q = true := by
      have hp : M (.inr k) p = true := (Finset.mem_filter.mp hk).2
      have hf : Sum.inr k ∈ F p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
      rw [same] at hf
      exact ⟨hp, (Finset.mem_filter.mp hf).2⟩
    have e := hLinear p q hpq (.inr i) (.inr j)
      (onBoth i hi).1 (onBoth i hi).2 (onBoth j hj).1 (onBoth j hj).2
    exact hij (Sum.inr.inj e)
  let f : P ↪ Finset R := ⟨F, injective⟩
  have on (p : P) (r : R) : r ∈ f p ↔ M r p = true := by simp [f, F]
  have ac (p : P) : (univ.filter fun i : Fin 8 => Sum.inl i ∈ f p) = A p := by
    ext i
    simp [A, on]
  have bc (p : P) : (univ.filter fun i : Fin 72 => Sum.inr i ∈ f p) = B p := by
    ext i
    simp [B, on]
  apply hNo
  refine ⟨U.map f, S.map f, Uᶜ.map f, by simpa using countU,
    Finset.map_subset_map.mpr sU, by simpa using hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Finset.card_compl, countU, P]
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
    simp only [ac, bc]
    exact hInside p hp
  · intro x hx hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hx
    have hpS : p ∉ S := fun h => hs (Finset.mem_map_of_mem f h)
    simp only [ac, bc]
    exact ⟨Finset.card_pos.mpr ((memU p).1 hp), maxDegree p, hOutside p hpS⟩
  · rw [filtered_map_card]
    simp_rw [ac]
    convert triple using 2
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    exact (memU p).2 (Finset.card_pos.mp (by omega))
  · intro i
    simpa only [filtered_map_card, on] using hHeavy i
  · intro i
    simpa only [filtered_map_card, on] using hLight i
  · intro k hk
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hk
    simp only [ac, bc]
    have outside : p ∉ U := Finset.mem_compl.mp hp
    have empty : A p = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun h => outside ((memU p).2 h))
    have h : 2 * (A p).card + (B p).card = 8 := hOutside p (fun h => outside (sU h))
    simpa [empty] using h
  · intro r
    simpa only [filtered_map_card, on, split_filter_count] using hRows r
  · intro r t hrt
    simp only [filtered_map_card, on, split_filter_count]
    obtain ⟨p, hp, hOnly⟩ := hMeet r t hrt
    apply Finset.card_eq_one.mpr
    refine ⟨p, ?_⟩
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨hOnly q, fun h => h ▸ hp⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2
