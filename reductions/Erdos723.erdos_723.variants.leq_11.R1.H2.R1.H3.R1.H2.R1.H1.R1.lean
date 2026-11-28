import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Basic

/-! Restrict the exterior intersection graph of the eight four-secants to six representatives. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H3.R1.H2.R1.H1.R1.lean by @avivorly (PR #2184) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H3.R1.H2.R1.H1.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1_H1_R1

open Finset

def H1 : Prop :=
  ∀ G : Fin 8 → Fin 8 → Bool,
    (∀ a b, G a b = G b a) →
    (∀ a, G a a = false) →
    (∀ a, (Finset.univ.filter fun b => G a b = true).card = 3) →
    ∃ e : Equiv.Perm (Fin 8),
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      let word := (pairs.zipIdx.map fun ((a,b),i) => if G (e a) (e b) then 2^i else 0).foldr Nat.lor 0
      word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187] : List Nat)

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
    (∀ p ∉ S, A M p ≤ 2) ∧
    ∃ e : Equiv.Perm (Fin 8),
      let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, M (.inl a) p = true ∧ M (.inl b) p = true)
      let pairs : List (Fin 8 × Fin 8) := [(0,1), (0,2), (0,3), (0,4), (0,5), (0,6), (0,7), (1,2), (1,3), (1,4), (1,5), (1,6), (1,7), (2,3), (2,4), (2,5), (2,6), (2,7), (3,4), (3,5), (3,6), (3,7), (4,5), (4,6), (4,7), (5,6), (5,7), (6,7)]
      let word := (pairs.zipIdx.map fun ((a,b),i) => if G (e a) (e b) then 2^i else 0).foldr Nat.lor 0
      word ∈ ([0x1da9807, 0x2e69807, 0x3569807, 0x35a5807, 0x3da1087, 0xfc02187] : List Nat)

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


theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1.H1 := by
  intro classify impossible
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1.H1
  dsimp only
  rintro ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,sparse⟩
  classical
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
  let G (a b : Fin 8) := decide (b ≠ a ∧ ∃ p ∉ S, A a p = true ∧ A b p = true)
  have symm (a b : Fin 8) : G a b = G b a := by
    apply Bool.eq_iff_iff.mpr
    simp only [G, decide_eq_true_eq]
    constructor <;> rintro ⟨different,p,hp,on_a,on_b⟩
    · exact ⟨different.symm,p,hp,on_b,on_a⟩
    · exact ⟨different.symm,p,hp,on_b,on_a⟩
  have loopfree (a : Fin 8) : G a a = false := by simp [G]
  have degree (a : Fin 8) : (Finset.univ.filter fun b => G a b = true).card = 3 := by
    have same : (Finset.univ.filter fun b => G a b = true) = outsideNeighbors a := by
      ext b
      simp [G, outside_mem]
    rw [same, cubic]
  obtain ⟨e,found⟩ := classify G symm loopfree degree
  exact impossible ⟨M,S,cardS,rowSizes,Asizes,Bsizes,insideDegrees,outsideDegrees,rowPairs,columnPairs,
    sparse,e,found⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H3_R1_H2_R1_H1_R1
