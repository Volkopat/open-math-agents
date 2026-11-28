import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Choose.Basic

/-! A four-point support leaves at most one triple support among the six heavy rows. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.H3.R1.lean by @avivorly (PR #3065) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4.R1.H2.R1.H3.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H3_R1

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
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let Pairs := F.filter fun T => T.card = 2
    ∃ U ∈ F, U.card = 4 ∧
      (∀ T ∈ F, T.card ≠ 3) ∧ Pairs.card = 8 ∧ (Finset.univ \ U) ∈ Pairs

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
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let Pairs := F.filter fun T => T.card = 2
    ∃ U ∈ F, U.card = 4 ∧
      let E := (Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2
      (∀ T ∈ F, T.card ≠ 3) ∧ (E \ Pairs).card ≤ 1 ∧
      (Pairs.card ≠ 8 ∨ (Finset.univ \ U) ∉ Pairs)

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
    let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
    let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
    let Pairs := F.filter fun T => T.card = 2
    ∃ U ∈ F, U.card = 4 ∧
      let E := (Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2
      ∃ T ∈ F, T.card = 3 ∧ (Finset.univ \ U) ⊆ T ∧ Pairs = E \ T.powersetCard 2

lemma pair_fits (F : Finset (Finset (Fin 6)))
    (overlap : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → (C ∩ D).card ≤ 1)
    (C D : Finset (Fin 6)) (hc : C ∈ F) (hd : D ∈ F) (two : C.card = 2)
    (large : 3 ≤ D.card) : C ∈ (Finset.univ : Finset (Fin 6)).powersetCard 2 \
      D.powersetCard 2 := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,two⟩,?_⟩
  intro covered
  have different : C ≠ D := fun same => by rw [← same,two] at large; omega
  have limit := overlap C hc D hd different
  have fits := (Finset.mem_powersetCard.mp covered).1
  have le := Finset.card_le_card (Finset.subset_inter (Finset.Subset.rfl : C ⊆ C) fits)
  omega

theorem four_clique_shapes (F : Finset (Finset (Fin 6)))
    (sizes : ∀ C ∈ F, 2 ≤ C.card ∧ C.card ≤ 4)
    (overlap : ∀ C ∈ F, ∀ D ∈ F, C ≠ D → (C ∩ D).card ≤ 1)
    (benefit : 11 ≤ ∑ C ∈ F, (C.card - 1))
    (U : Finset (Fin 6)) (hu : U ∈ F) (four : U.card = 4) :
    let P := F.filter fun C => C.card = 2
    let E := (Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2
    (∀ C ∈ F, C.card = 4 → C = U) ∧ P ⊆ E ∧
      (((∀ C ∈ F, C.card ≠ 3) ∧ (E \ P).card ≤ 1) ∨
        ∃ T ∈ F, T.card = 3 ∧ (Finset.univ \ U) ⊆ T ∧ P = E \ T.powersetCard 2) := by
  let P := F.filter fun C => C.card = 2
  let E := (Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2
  have bound_union (C : Finset (Fin 6)) : (C ∪ U).card ≤ 6 :=
    (Finset.card_le_card (Finset.subset_univ (C ∪ U))).trans_eq (Fintype.card_fin 6)
  have large_unique (C : Finset (Fin 6)) (hc : C ∈ F) (c4 : C.card = 4) : C = U := by
    by_contra different
    have using_pairs := overlap C hc U hu different
    have count := Finset.card_union_add_card_inter C U
    have bound := bound_union C
    omega
  have pair_subset : P ⊆ E := by
    intro C hc
    obtain ⟨hc,two⟩ := Finset.mem_filter.mp hc
    exact pair_fits F overlap C U hc hu two (by omega)
  have countEdges : E.card = 9 := by
    change ((Finset.univ : Finset (Fin 6)).powersetCard 2 \ U.powersetCard 2).card = 9
    rw [Finset.card_sdiff_of_subset (Finset.powersetCard_mono (Finset.subset_univ U)),
      Finset.card_powersetCard,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin,four]
    decide
  have sumPairs : (∑ C ∈ P, (C.card - 1)) = P.card := by
    calc
      _ = ∑ _C ∈ P, 1 := by
        apply Finset.sum_congr rfl
        intro C hc
        rw [(Finset.mem_filter.mp hc).2]
      _ = _ := by simp
  refine ⟨large_unique,pair_subset,?_⟩
  by_cases hasTriple : ∃ T ∈ F, T.card = 3
  · obtain ⟨T,ht,three⟩ := hasTriple
    have outer_two : (Finset.univ \ U).card = 2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),Finset.card_univ,Fintype.card_fin,four]
    have covers_outer (C : Finset (Fin 6)) (hc : C ∈ F) (c3 : C.card = 3) :
        Finset.univ \ U ⊆ C := by
      have different : C ≠ U := fun same => by rw [same, four] at c3; omega
      have small := overlap C hc U hu different
      have cOuter : (C \ U).card = 2 := by
        rw [Finset.card_sdiff, Finset.inter_comm]
        have bound := bound_union C
        have count := Finset.card_union_add_card_inter C U
        omega
      have incl : C \ U ⊆ Finset.univ \ U := by
        intro v hv
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(Finset.mem_sdiff.mp hv).2⟩
      have same := Finset.eq_of_subset_of_card_le incl (by rw [outer_two,cOuter])
      rw [← same]
      exact Finset.sdiff_subset
    have triple_unique (C : Finset (Fin 6)) (hc : C ∈ F) (c3 : C.card = 3) : C = T := by
      by_contra different
      have small := overlap C hc T ht different
      have large := Finset.card_le_card
        (Finset.subset_inter (covers_outer C hc c3) (covers_outer T ht three))
      omega
    have notU : T ≠ U := fun same => by rw [same,four] at three; omega
    have left : T ∈ F.erase U := Finset.mem_erase.mpr ⟨notU,ht⟩
    have residue : (F.erase U).erase T = P := by
      ext C
      simp only [P, Finset.mem_erase, Finset.mem_filter]
      constructor
      · rintro ⟨neT,neU,hc⟩
        refine ⟨hc,?_⟩
        have ⟨lo,hi⟩ := sizes C hc
        have n3 : C.card ≠ 3 := fun eq => neT (triple_unique C hc eq)
        have n4 : C.card ≠ 4 := fun eq => neU (large_unique C hc eq)
        omega
      · rintro ⟨hc,two⟩
        refine ⟨?_,?_,hc⟩
        · intro eq
          rw [eq,three] at two
          omega
        · intro eq
          rw [eq,four] at two
          omega
    have sumU := Finset.sum_erase_add F (fun C => C.card - 1) hu
    have sumT := Finset.sum_erase_add (F.erase U) (fun C => C.card - 1) left
    rw [four] at sumU
    rw [residue,sumPairs,three] at sumT
    have pairLarge : 6 ≤ P.card := by omega
    have edgeT : T.powersetCard 2 ⊆ E := by
      intro C hc
      obtain ⟨fits,two⟩ := Finset.mem_powersetCard.mp hc
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,two⟩,?_⟩
      intro inU
      have fitsU := (Finset.mem_powersetCard.mp inU).1
      have large := Finset.card_le_card (Finset.subset_inter fits fitsU)
      have small := overlap T ht U hu notU
      omega
    have remainder : (E \ T.powersetCard 2).card = 6 := by
      rw [Finset.card_sdiff_of_subset edgeT,countEdges,Finset.card_powersetCard,three]
      decide
    have all : P ⊆ E \ T.powersetCard 2 := by
      intro C hc
      obtain ⟨inF,two⟩ := Finset.mem_filter.mp hc
      have apart := (Finset.mem_sdiff.mp (pair_fits F overlap C T inF ht two three.ge)).2
      exact Finset.mem_sdiff.mpr ⟨pair_subset hc,apart⟩
    have larger : (E \ T.powersetCard 2).card ≤ P.card := by rwa [remainder]
    exact Or.inr ⟨T,ht,three,covers_outer T ht three,Finset.eq_of_subset_of_card_le all larger⟩
  · have none (C : Finset (Fin 6)) (hc : C ∈ F) : C.card ≠ 3 :=
      fun three => hasTriple ⟨C,hc,three⟩
    have residue : F.erase U = P := by
      ext C
      simp only [P,Finset.mem_erase,Finset.mem_filter]
      constructor
      · rintro ⟨ne,hc⟩
        refine ⟨hc,?_⟩
        have ⟨lo,hi⟩ := sizes C hc
        have n3 := none C hc
        have n4 : C.card ≠ 4 := fun eq => ne (large_unique C hc eq)
        omega
      · rintro ⟨hc,two⟩
        refine ⟨?_,hc⟩
        intro eq
        rw [eq,four] at two
        omega
    have sumU := Finset.sum_erase_add F (fun C => C.card - 1) hu
    rw [residue,sumPairs,four] at sumU
    have diff : (E \ P).card = E.card - P.card := Finset.card_sdiff_of_subset pair_subset
    refine Or.inl ⟨none,?_⟩
    change (E \ P).card ≤ 1
    omega

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

theorem main : H1 → H2 → H3 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H3 := by
  intro complementary noTriple hasTriple
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1.H3
  dsimp only
  rintro ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,fourPoint⟩
  classical
  let A (a : Fin 6) (p : Fin 19) := M (.inl a) (.inl p)
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => A a p = true
  let F := (Finset.univ.filter fun p => 2 ≤ (C p).card).image C
  have at_most (p : Fin 19) : (C p).card ≤ 4 := by
    have seen := inside p
    change _ + 2 * (C p).card = 9 at seen
    omega
  have sizes (T : Finset (Fin 6)) (ht : T ∈ F) : 2 ≤ T.card ∧ T.card ≤ 4 := by
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
  obtain ⟨p,four⟩ := fourPoint
  have count : (C p).card = 4 := four
  have found : C p ∈ F :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
  obtain ⟨_,_,cases⟩ := four_clique_shapes F sizes separate benefit (C p) found count
  rcases cases with ⟨none,missing⟩ | ⟨T,hT,three,outer,pairs⟩
  · let Pairs := F.filter fun T => T.card = 2
    by_cases eight : Pairs.card = 8
    · by_cases good : Finset.univ \ C p ∈ Pairs
      · exact complementary ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,
          C p,found,count,none,eight,good⟩
      · exact noTriple ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,
          C p,found,count,none,missing,Or.inr good⟩
    · exact noTriple ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,
        C p,found,count,none,missing,Or.inl eight⟩
  · exact hasTriple ⟨M,rowSizes,colSizes,rowPairs,colPairs,aSizes,bSizes,cSizes,inside,outside,
      C p,found,count,T,hT,three,outer,pairs⟩


end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1_H3_R1
