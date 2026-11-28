import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

/-! Split the possible incidence layouts by the number of triple supports. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H2.R1.lean by @avivorly (PR #3100) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4.R1.H2.R1.H2.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H2_R1

open Finset
open scoped BigOperators

def H1 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 1 ∧ 9 ≤ x ∧ x ≤ 12

def H2 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 2 ∧ 7 ≤ x ∧ x ≤ 9 ∧ (x ≠ 7 ∨ ¬ (∃ p q : Fin 19, (C p).card = 3 ∧ (C q).card = 3 ∧ C p ∪ C q = Finset.univ))

def H3 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    (y = 3 ∧ 5 ≤ x ∧ x ≤ 6) ∨ (y = 4 ∧ x = 3)

def H4 : Prop :=
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let A (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (M : R → P → Bool) (p : P) :=
    (Finset.univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  ¬ ∃ M : R → P → Bool,
    (∀ l, (Finset.univ.filter fun p => M l p = true).card = 11) ∧
    (∀ p, (Finset.univ.filter fun l => M l p = true).card = 11) ∧
    (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
    (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
    (∀ a : Fin 6, (Finset.univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
    (∀ b : Fin 37, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
    (∀ c : Fin 68, (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
    (∀ p : Fin 19, B M (.inl p) + 2*A M (.inl p) = 9) ∧
    (∀ p : Fin 92, B M (.inr p) + 2*A M (.inr p) = 4) ∧
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 2 ∧ x = 7 ∧ ∃ p q : Fin 19, (C p).card = 3 ∧ (C q).card = 3 ∧ C p ∪ C q = Finset.univ

theorem triple_pair_balance (F : Finset (Finset (Fin 6)))
    (sizes : ∀ C ∈ F, 2 ≤ C.card ∧ C.card ≤ 3)
    (overlap : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → (C ∩ D).card ≤ 1)
    (benefit : 11 ≤ ∑ C ∈ F, (C.card - 1)) :
    let P := (F.filter fun C => C.card = 2).card
    let T := (F.filter fun C => C.card = 3).card
    11 ≤ P + 2*T ∧ P + 3*T ≤ 15 ∧ T ≤ 4 := by
  let choosePair (C : Finset (Fin 6)) := C.powersetCard 2
  have different_sets : (F : Set (Finset (Fin 6))).PairwiseDisjoint choosePair := by
    intro C hc D hd different
    change Disjoint (choosePair C) (choosePair D)
    rw [Finset.disjoint_left]
    intro p left right
    obtain ⟨onC,two⟩ := Finset.mem_powersetCard.mp left
    obtain ⟨onD,_⟩ := Finset.mem_powersetCard.mp right
    have small := overlap C (Finset.mem_coe.mp hc) D (Finset.mem_coe.mp hd) different
    have contained := Finset.card_le_card (Finset.subset_inter onC onD)
    omega
  have inside_univ : F.biUnion choosePair ⊆ (Finset.univ : Finset (Fin 6)).powersetCard 2 := by
    intro p hp
    obtain ⟨C,_,on⟩ := Finset.mem_biUnion.mp hp
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,(Finset.mem_powersetCard.mp on).2⟩
  have all_count : ((Finset.univ : Finset (Fin 6)).powersetCard 2).card = 15 := by
    rw [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
    decide
  have budget := Finset.card_le_card inside_univ
  rw [all_count,Finset.card_biUnion different_sets] at budget
  have benefit_c (C : Finset (Fin 6)) (hc : C ∈ F) :
      C.card-1 = (if C.card = 2 then 1 else 0) + (if C.card = 3 then 2 else 0) := by
    have limits := sizes C hc
    split_ifs <;> omega
  have cost_c (C : Finset (Fin 6)) (hc : C ∈ F) :
      (choosePair C).card = (if C.card = 2 then 1 else 0) + (if C.card = 3 then 3 else 0) := by
    change (C.powersetCard 2).card = _
    rw [Finset.card_powersetCard]
    have limits := sizes C hc
    have cases : C.card = 2 ∨ C.card = 3 := by omega
    rcases cases with two | three
    · rw [two]
      decide
    · rw [three]
      decide
  let P := (F.filter fun C => C.card = 2).card
  let T := (F.filter fun C => C.card = 3).card
  have benefit_count : (∑ C ∈ F, (C.card - 1)) = P + 2*T := by
    calc
      _ = ∑ C ∈ F, ((if C.card = 2 then 1 else 0) + (if C.card = 3 then 2 else 0)) :=
        Finset.sum_congr rfl benefit_c
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter]
        simp [P,T,Nat.mul_comm]
  have cost_count : (∑ C ∈ F, (choosePair C).card) = P + 3*T := by
    calc
      _ = ∑ C ∈ F, ((if C.card = 2 then 1 else 0) + (if C.card = 3 then 3 else 0)) :=
        Finset.sum_congr rfl cost_c
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.sum_filter,← Finset.sum_filter]
        simp [P,T,Nat.mul_comm]
  rw [benefit_count] at benefit
  rw [cost_count] at budget
  exact ⟨benefit,budget,by omega⟩

lemma layout_total (A : Fin 6 → Fin 19 → Bool) (C : Fin 19 → Finset (Fin 6))
    (column_form : ∀ p, C p = Finset.univ.filter fun a => A a p = true)
    (sizes : ∀ a, (Finset.univ.filter fun p => A a p = true).card = 5) :
    (∑ p : Fin 19, (C p).card) = 30 := by
  calc
    _ = ∑ p : Fin 19, ∑ a : Fin 6, if A a p = true then (1 : Nat) else 0 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [← Finset.sum_filter, column_form p]
      simp
    _ = ∑ a : Fin 6, ∑ p : Fin 19, if A a p = true then (1 : Nat) else 0 := Finset.sum_comm
    _ = ∑ _a : Fin 6, (5 : Nat) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_filter]
      simpa using sizes a
    _ = _ := by simp

lemma layout_counts (C : Fin 19 → Finset (Fin 6)) (total : (∑ p : Fin 19, (C p).card) = 30)
    (overlap : ∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) :
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    (Finset.univ.filter fun p => 0 < (C p).card).card + ∑ T ∈ F, (T.card - 1) = 30 := by
  let shared := Finset.univ.filter fun p => 2 ≤ (C p).card
  let used := Finset.univ.filter fun p => 0 < (C p).card
  have using_columns : (shared : Set (Fin 19)).InjOn C := by
    intro p hp q hq same
    by_contra different
    have small := overlap p q different
    rw [same,Finset.inter_self] at small
    have many := (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
    omega
  have split (p : Fin 19) : (C p).card =
      (if 0 < (C p).card then 1 else 0) +
      (if 2 ≤ (C p).card then (C p).card - 1 else 0) := by
    split_ifs <;> omega
  have sum_split : (∑ p : Fin 19, (C p).card) =
      used.card + ∑ p ∈ shared, ((C p).card - 1) := by
    calc
      _ = ∑ p : Fin 19, ((if 0 < (C p).card then 1 else 0) +
          (if 2 ≤ (C p).card then (C p).card - 1 else 0)) :=
        Finset.sum_congr rfl (fun p _ => split p)
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
        simp [used,shared]
  change used.card + ∑ T ∈ shared.image C, (T.card - 1) = 30
  rw [Finset.sum_image using_columns]
  exact sum_split.symm.trans total


theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H2 := by
  intro case1 case2 case3 case4
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H2
  dsimp only
  rintro ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,someTriple⟩
  classical
  let A (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => A a p = true
  let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
  have at_most (p : Fin 19) : (C p).card ≤ 3 := bound p
  have sizes (T : Finset (Fin 6)) (ht : T ∈ F) : 2 ≤ T.card ∧ T.card ≤ 3 := by
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(Finset.mem_filter.mp hp).2,at_most p⟩
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have on_both (x : Fin 6) (hx : x ∈ C p ∩ C q) : A x p = true ∧ A x q = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hx
      exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hq).2⟩
    obtain ⟨_,_,same⟩ := colPairs (.inl p) (.inl q) (fun e => different (Sum.inl.inj e))
    exact Sum.inl.inj ((same (.inl a) (on_both a ha)).trans (same (.inl b) (on_both b hb)).symm)
  have separate (T : Finset (Fin 6)) (ht : T ∈ F) (V : Finset (Fin 6)) (hv : V ∈ F)
      (different : T ≠ V) : (T ∩ V).card ≤ 1 := by
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hv
    exact overlap p q (fun same => different (congrArg C same))
  let used := Finset.univ.filter fun p => 0 < (C p).card
  have countAll : used.card + ∑ T ∈ F, (T.card - 1) = 30 :=
    layout_counts C (layout_total A C (fun _ => rfl) aSizes) overlap
  have used_at_most : used.card ≤ 19 :=
    (Finset.card_le_card (Finset.subset_univ used)).trans_eq (Fintype.card_fin _)
  have benefit : 11 ≤ ∑ T ∈ F, (T.card - 1) := by omega
  let x := (F.filter fun T => T.card = 2).card
  let y := (F.filter fun T => T.card = 3).card
  obtain ⟨p,triple⟩ := someTriple
  have c3 : (C p).card = 3 := triple
  have memF : C p ∈ F :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
  have positive : 0 < y := Finset.card_pos.mpr ⟨C p,Finset.mem_filter.mpr ⟨memF,c3⟩⟩
  have census : 11 ≤ x + 2*y ∧ x + 3*y ≤ 15 ∧ y ≤ 4 :=
    triple_pair_balance F sizes separate benefit
  rcases census with ⟨low,high,cap⟩
  have which : y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 := by omega
  rcases which with one | two | three | four
  · exact case1 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
      one,by change 9 ≤ x; omega,by change x ≤ 12; omega⟩
  · have lo : 7 ≤ x := by omega
    have hi : x ≤ 9 := by omega
    by_cases exactCount : x = 7
    · by_cases h : ∃ p q : Fin 19, (C p).card = 3 ∧ (C q).card = 3 ∧ C p ∪ C q = Finset.univ
      · exact case4 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
          two,exactCount,h⟩
      · exact case2 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
          two,lo,hi,Or.inr h⟩
    · exact case2 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
        two,lo,hi,Or.inl exactCount⟩
  · exact case3 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
      Or.inl ⟨three,by change 5 ≤ x; omega,by change x ≤ 6; omega⟩⟩
  · exact case3 ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,bound,
      Or.inr ⟨four,by change x = 3; omega⟩⟩

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H2_R1
