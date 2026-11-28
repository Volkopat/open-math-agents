import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-! Split the concurrent exterior intersections at a point on four of the first eight lines. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H3.R1.H2.R1.H2.R1.lean by @avivorly (PR #2249) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H3.R1.H2.R1.H2.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1_H2_R1

open Finset

def H1 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    (∃ p ∉ S, 3 ≤ A M p) ∧ (∀ p ∉ S, A M p ≤ 3)

def H2 : Prop :=
  let A (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 8 => M (.inl l) p = true).card
  let B (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (p : Fin 111) :=
    (Finset.univ.filter fun l : Fin 72 => M (.inr l) p = true).card
  ¬ ∃ (M : Fin 8 ⊕ Fin 72 → Fin 111 → Bool) (S : Finset (Fin 111)),
    S.card = 16 ∧
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ l : Fin 8, (S.filter fun p => M (.inl l) p = true).card = 4) ∧
    (∀ l : Fin 72, (S.filter fun p => M (.inr l) p = true).card = 2) ∧
    (∀ p ∈ S, A M p = 2 ∧ B M p = 9) ∧
    (∀ p ∉ S, 2 * A M p + B M p = 8) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∀ l m, M l p = true → M l q = true →
      M m p = true → M m q = true → l = m) ∧
    ∃ p ∉ S,
      let C := Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true
      C.card = 4 ∧ ∀ a b : Fin 8, a ≠ b →
        ((∃ q ∉ S, M (.inl a) q = true ∧ M (.inl b) q = true) ↔ (a ∈ C ↔ b ∈ C))

lemma second_row (A : Fin 8 → Fin 111 → Bool) (p : Fin 111)
    (rows : (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (on_a : A a p = true) : ∃! b, b ≠ a ∧ A b p = true := by
  let here : Finset (Fin 8) := Finset.univ.filter fun r => A r p = true
  have contains_a : a ∈ here := Finset.mem_filter.mpr ⟨Finset.mem_univ _,on_a⟩
  have residual : (here.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem contains_a]
    exact Nat.sub_eq_of_eq_add rows
  obtain ⟨b, represented⟩ := Finset.card_eq_one.mp residual
  have iff_mem (r : Fin 8) : r ∈ here.erase a ↔ r ≠ a ∧ A r p = true := by
    simp [here, Finset.mem_erase, Finset.mem_filter]
  have hb : b ∈ here.erase a := by rw [represented]; exact Finset.mem_singleton_self b
  refine ⟨b,(iff_mem b).mp hb,fun r hr => ?_⟩
  have h := (iff_mem r).mpr hr
  rw [represented] at h
  exact Finset.mem_singleton.mp h

lemma cardinal_inner (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (insideNeighbors : Fin 8 → Finset (Fin 8))
    (inside_mem : ∀ a b, b ∈ insideNeighbors a ↔ b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true)
    (share : ∀ a b, a ≠ b → ∃! p, (A a p = true ∧ A b p = true))
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (a : Fin 8) (line_four : (S.filter fun p => A a p = true).card = 4) :
    (insideNeighbors a).card = 4 := by
  classical
  let on_line := S.filter fun p => A a p = true
  have second (p : Fin 111) (hp : p ∈ on_line) : ∃! b, b ≠ a ∧ A b p = true := by
    obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
    exact second_row A p (degree_two p inS) a onA
  let other (p : Fin 111) (hp : p ∈ on_line) := Classical.choose (second p hp)
  have other_good (p : Fin 111) (hp : p ∈ on_line) :
      (other p hp ≠ a ∧ A (other p hp) p = true) ∧
      ∀ b, b ≠ a ∧ A b p = true → b = other p hp := Classical.choose_spec (second p hp)
  have bij : on_line.card = (insideNeighbors a).card := by
    apply Finset.card_bij other
    · intro p hp
      obtain ⟨inS, onA⟩ := Finset.mem_filter.mp hp
      obtain ⟨different, onB⟩ := (other_good p hp).1
      exact (inside_mem a _).mpr ⟨different,p,inS,onA,onB⟩
    · intro p hp q hq eq
      obtain ⟨_, _, unique⟩ := share a (other p hp) ((other_good p hp).1.1.symm)
      have one : A a p = true ∧ A (other p hp) p = true :=
        ⟨(Finset.mem_filter.mp hp).2,(other_good p hp).1.2⟩
      have two : A a q = true ∧ A (other p hp) q = true :=
        ⟨(Finset.mem_filter.mp hq).2,eq.symm ▸ (other_good q hq).1.2⟩
      exact (unique p one).trans (unique q two).symm
    · intro b hb
      obtain ⟨different,p,inS,onA,onB⟩ := (inside_mem a b).mp hb
      have hp : p ∈ on_line := Finset.mem_filter.mpr ⟨inS,onA⟩
      exact ⟨p,hp,((other_good p hp).2 b ⟨different,onB⟩).symm⟩
  exact bij.symm.trans line_four

theorem exterior_cubic (A : Fin 8 → Fin 111 → Bool) (S : Finset (Fin 111))
    (insideNeighbors : Fin 8 → Finset (Fin 8))
    (inside_mem : ∀ a b, b ∈ insideNeighbors a ↔ b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true)
    (outsideNeighbors : Fin 8 → Finset (Fin 8))
    (outside_mem : ∀ a b, b ∈ outsideNeighbors a ↔ b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
    (share : ∀ a b, a ≠ b → ∃! p, (A a p = true ∧ A b p = true))
    (degree_two : ∀ p ∈ S, (Finset.univ.filter fun l => A l p = true).card = 2)
    (line_four : ∀ a, (S.filter fun p => A a p = true).card = 4)
    (a : Fin 8) : (outsideNeighbors a).card = 3 := by
  classical
  have inner_four := cardinal_inner A S insideNeighbors inside_mem share degree_two a (line_four a)
  have separated : Disjoint (insideNeighbors a) (outsideNeighbors a) := by
    rw [Finset.disjoint_left]
    intro b hb hc
    obtain ⟨different,p,inside,hp⟩ := (inside_mem a b).mp hb
    obtain ⟨_,q,outside,hq⟩ := (outside_mem a b).mp hc
    obtain ⟨_, _, unique⟩ := share a b different.symm
    have same := (unique p hp).trans (unique q hq).symm
    exact outside (same ▸ inside)
  have total : insideNeighbors a ∪ outsideNeighbors a = Finset.univ.erase a := by
    ext b
    simp only [Finset.mem_union, inside_mem, outside_mem, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨different,_⟩ | ⟨different,_⟩) <;> exact different
    · intro different
      obtain ⟨p,on_rows,_⟩ := share a b different.symm
      by_cases inside : p ∈ S
      · exact Or.inl ⟨different,p,inside,on_rows⟩
      · exact Or.inr ⟨different,p,inside,on_rows⟩
  have count := Finset.card_union_of_disjoint separated
  rw [total, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin, inner_four] at count
  omega



theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1.H2 := by
  intro noTriangles noTetrahedrons
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1.H2
  dsimp only
  rintro ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,dense⟩
  classical
  by_cases wide : ∃ p ∉ S, (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card = 4
  · obtain ⟨p,hp,four⟩ := wide
    let A (a : Fin 8) (p : Fin 111) := M (.inl a) p
    let insideNeighbors (a : Fin 8) : Finset (Fin 8) :=
      Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∈ S, A a p = true ∧ A b p = true
    let outsideNeighbors (a : Fin 8) : Finset (Fin 8) :=
      Finset.univ.filter fun b => b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true
    have inside_mem (a b : Fin 8) : b ∈ insideNeighbors a ↔ b ≠ a ∧
        ∃ p ∈ S, A a p = true ∧ A b p = true := by simp [insideNeighbors]
    have outside_mem (a b : Fin 8) : b ∈ outsideNeighbors a ↔ b ≠ a ∧
        ∃ p ∉ S, A a p = true ∧ A b p = true := by simp [outsideNeighbors]
    have A_pairs (a b : Fin 8) (different : a ≠ b) : ∃! p, A a p = true ∧ A b p = true :=
      rowPairs (.inl a) (.inl b) (fun eq => different (Sum.inl.inj eq))
    have cubic := exterior_cubic A S insideNeighbors inside_mem outsideNeighbors outside_mem A_pairs
      (fun p hp => (insideDegrees p hp).1) Asizes
    let C : Finset (Fin 8) := Finset.univ.filter fun a => A a p = true
    let D : Finset (Fin 8) := Finset.univ \ C
    have sizeC : C.card = 4 := four
    have sizeD : D.card = 4 := by
      change (Finset.univ \ C).card = 4
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ C), Finset.card_univ,
        Fintype.card_fin, sizeC]
    have exteriorSymm (a b : Fin 8) : b ∈ outsideNeighbors a ↔ a ∈ outsideNeighbors b := by
      rw [outside_mem, outside_mem]
      constructor <;> rintro ⟨different,r,hr,on_a,on_b⟩
      · exact ⟨different.symm,r,hr,on_b,on_a⟩
      · exact ⟨different.symm,r,hr,on_b,on_a⟩
    have within (a : Fin 8) (ha : a ∈ C) : outsideNeighbors a = C.erase a := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro b hb
        obtain ⟨diff,inC⟩ := Finset.mem_erase.mp hb
        exact (outside_mem a b).mpr ⟨diff,p,hp,(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp inC).2⟩
      · rw [cubic, Finset.card_erase_of_mem ha, sizeC]
    have apart (a : Fin 8) (ha : a ∉ C) : outsideNeighbors a = D.erase a := by
      have memberD : a ∈ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,ha⟩
      apply Finset.eq_of_subset_of_card_le
      · intro b hb
        refine Finset.mem_erase.mpr ⟨((outside_mem a b).mp hb).1,?_⟩
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
        intro b_in
        have reverse := (exteriorSymm a b).mp hb
        rw [within b b_in] at reverse
        exact ha (Finset.mem_of_mem_erase reverse)
      · rw [cubic, Finset.card_erase_of_mem memberD, sizeD]
    have blocks (a b : Fin 8) (different : a ≠ b) :
        (∃ q ∉ S, M (.inl a) q = true ∧ M (.inl b) q = true) ↔
          (a ∈ C ↔ b ∈ C) := by
      have relation : b ∈ outsideNeighbors a ↔ (∃ q ∉ S, A a q = true ∧ A b q = true) := by
        exact (outside_mem a b).trans ⟨And.right, fun hit => ⟨different.symm,hit⟩⟩
      rw [← relation]
      by_cases ha : a ∈ C
      · rw [within a ha]
        simp [Finset.mem_erase,different.symm,ha]
      · rw [apart a ha]
        simp [D,Finset.mem_erase,different.symm,ha]
    exact noTetrahedrons ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,
      p,hp,four,blocks⟩
  · apply noTriangles
    refine ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,dense,?_⟩
    intro p hp
    change (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card ≤ 3
    have point_bound := outsideDegrees p hp
    have not_four : (Finset.univ.filter fun a : Fin 8 => M (.inl a) p = true).card ≠ 4 :=
      fun hit => wide ⟨p,hp,hit⟩
    omega

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1_H2_R1
