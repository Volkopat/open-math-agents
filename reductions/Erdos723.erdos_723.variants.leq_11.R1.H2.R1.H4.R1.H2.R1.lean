import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-! Index the primitive weight-nineteen incidence matrix by its three row classes and two point classes. -/
-- Credit: @LordMike
-- Port of reductions/Erdos723.erdos_723.variants.leq_11.R1.H2.R2.H4.R1.H2.R1.lean by @avivorly (PR #2474) onto the identical hypothesis statement Erdos723.erdos_723.variants.leq_11.R1.H2.R1.H4.R1.H2.
namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1

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
    ∀ p : Fin 19, A M (.inl p) ≤ 2

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
    (∀ p : Fin 19, A M (.inl p) ≤ 3) ∧ ∃ p : Fin 19, A M (.inl p) = 3

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
    ∃ p : Fin 19, A M (.inl p) = 4

open Finset

lemma sum_elim_injective {X Y Z : Type} (x : X → Z) (y : Y → Z)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (separate : ∀ a b, x a ≠ y b) : Function.Injective (Sum.elim x y) := by
  intro a b same
  cases a with
  | inl u =>
    cases b with
    | inl v => exact congrArg Sum.inl (hx same)
    | inr v => exact False.elim (separate u v same)
  | inr u =>
    cases b with
    | inl v => exact False.elim (separate v u same.symm)
    | inr v => exact congrArg Sum.inr (hy same)

lemma chosen_value_injective {n : Nat} (S : Finset (Fin 111)) (e : Fin n ≃ ↥S) :
    Function.Injective (fun x => (e x).val) :=
  fun _ _ same => e.injective (Subtype.ext same)

lemma cardinal_filter_equiv {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (Q : Y → Prop) [DecidablePred Q] :
    (Finset.univ.filter (fun x => Q (e x))).card = (Finset.univ.filter Q).card := by
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ eq
    exact e.injective eq
  · intro y hy
    refine ⟨e.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,e.apply_symm_apply y⟩
    simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hy).2

lemma cardinal_filter_subset {n : Nat} (S : Finset (Fin 111)) (e : Fin n ≃ ↥S)
    (Q : Fin 111 → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun x => Q (e x).val).card = (S.filter Q).card := by
  apply Finset.card_bij (fun x _ => (e x).val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(e x).property,(Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ eq
    exact chosen_value_injective S e eq
  · intro y hy
    obtain ⟨inS,good⟩ := Finset.mem_filter.mp hy
    refine ⟨e.symm ⟨y,inS⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
    · simpa only [Equiv.apply_symm_apply] using good
    · exact congrArg Subtype.val (e.apply_symm_apply ⟨y,inS⟩)

lemma pull_unique {X Y : Type} (e : X ≃ Y) (Q : Y → Prop) (found : ∃! y, Q y) :
    ∃! x, Q (e x) := by
  obtain ⟨y,on_y,unique⟩ := found
  refine ⟨e.symm y, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using on_y
  · intro x yes
    exact e.injective ((unique (e x) yes).trans (e.apply_symm_apply y).symm)

set_option maxHeartbeats 4000000 in
theorem main : H1 → H2 → H3 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1.H2 := by
  intro noPairs noTriples noQuads I rowSizes colSizes rowPairs colPairs
  dsimp only
  rintro ⟨S, sizeS, allowed, ⟨ones,threes,fives⟩, profile⟩
  classical
  let R := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
  let P := Fin 19 ⊕ Fin 92
  let k (l : Fin 111) := (S.filter fun p => I l p = true).card
  let A : Finset (Fin 111) := Finset.univ.filter fun l => k l = 5
  let B : Finset (Fin 111) := Finset.univ.filter fun l => k l = 3
  let C : Finset (Fin 111) := Finset.univ.filter fun l => k l = 1
  let T := Finset.univ \ S
  have sizeT : T.card = 92 := by
    change (Finset.univ \ S).card = 92
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ,
      Fintype.card_fin,sizeS]
  let a : Fin 6 ≃ ↥A := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using fives)).symm
  let b : Fin 37 ≃ ↥B := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using threes)).symm
  let c : Fin 68 ≃ ↥C := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using ones)).symm
  let s : Fin 19 ≃ ↥S := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using sizeS)).symm
  let t : Fin 92 ≃ ↥T := (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using sizeT)).symm
  let rows : R → Fin 111 :=
    Sum.elim (fun j => (a j).val) (Sum.elim (fun j => (b j).val) (fun j => (c j).val))
  let cols : P → Fin 111 := Sum.elim (fun j => (s j).val) (fun j => (t j).val)
  have Arow (j : Fin 6) : k (a j).val = 5 := (Finset.mem_filter.mp (a j).property).2
  have Brow (j : Fin 37) : k (b j).val = 3 := (Finset.mem_filter.mp (b j).property).2
  have Crow (j : Fin 68) : k (c j).val = 1 := (Finset.mem_filter.mp (c j).property).2
  have rows_injective : Function.Injective rows := by
    apply sum_elim_injective
    · exact chosen_value_injective A a
    · apply sum_elim_injective (fun j => (b j).val) (fun j => (c j).val)
        (chosen_value_injective B b) (chosen_value_injective C c)
      intro x y same
      have eq := congrArg k same
      rw [Brow,Crow] at eq
      contradiction
    · intro x y
      cases y with
      | inl y =>
        intro same
        have eq : k (a x).val = k (b y).val := congrArg k same
        rw [Arow,Brow] at eq
        contradiction
      | inr y =>
        intro same
        have eq : k (a x).val = k (c y).val := congrArg k same
        rw [Arow,Crow] at eq
        contradiction
  have cols_injective : Function.Injective cols := by
    apply sum_elim_injective (fun j => (s j).val) (fun j => (t j).val)
      (chosen_value_injective S s) (chosen_value_injective T t)
    intro j h eq
    exact (Finset.mem_sdiff.mp (t h).property).2 (eq ▸ (s j).property)
  let rowEquiv : R ≃ Fin 111 :=
    Equiv.ofBijective rows ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨rows_injective,by simp [R, Fintype.card_sum]⟩)
  let colEquiv : P ≃ Fin 111 :=
    Equiv.ofBijective cols ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨cols_injective,by simp [P, Fintype.card_sum]⟩)
  let M (l : R) (p : P) := I (rows l) (cols p)
  have row_sizes (l : R) : (Finset.univ.filter fun p => M l p = true).card = 11 :=
    (cardinal_filter_equiv colEquiv (fun p => I (rows l) p = true)).trans (rowSizes (rows l))
  have col_sizes (p : P) : (Finset.univ.filter fun l => M l p = true).card = 11 :=
    (cardinal_filter_equiv rowEquiv (fun l => I l (cols p) = true)).trans (colSizes (cols p))
  have row_pairs (l m : R) (different : l ≠ m) : ∃! p, M l p = true ∧ M m p = true :=
    pull_unique colEquiv _ (rowPairs _ _ (fun eq => different (rows_injective eq)))
  have col_pairs (p q : P) (different : p ≠ q) : ∃! l, M l p = true ∧ M l q = true :=
    pull_unique rowEquiv _ (colPairs _ _ (fun eq => different (cols_injective eq)))
  have rowA (l : Fin 6) : (Finset.univ.filter fun p : Fin 19 => M (.inl l) (.inl p) = true).card = 5 :=
    (cardinal_filter_subset S s (fun p => I (a l).val p = true)).trans (Arow l)
  have rowB (l : Fin 37) : (Finset.univ.filter fun p : Fin 19 => M (.inr (.inl l)) (.inl p) = true).card = 3 :=
    (cardinal_filter_subset S s (fun p => I (b l).val p = true)).trans (Brow l)
  have rowC (l : Fin 68) : (Finset.univ.filter fun p : Fin 19 => M (.inr (.inr l)) (.inl p) = true).card = 1 :=
    (cardinal_filter_subset S s (fun p => I (c l).val p = true)).trans (Crow l)
  let ac (p : P) := (Finset.univ.filter fun l : Fin 6 => M (.inl l) p = true).card
  let bc (p : P) := (Finset.univ.filter fun l : Fin 37 => M (.inr (.inl l)) p = true).card
  have same_rows (j : Nat) (p : P) :
      (Finset.univ.filter (fun l => k l = j)).filter (fun l => I l (cols p) = true) =
        Finset.univ.filter (fun l => k l = j ∧ I l (cols p) = true) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have ac_eq (p : P) : ac p = (Finset.univ.filter (fun l => k l = 5 ∧ I l (cols p) = true)).card := by
    calc
      ac p = (A.filter (fun l => I l (cols p) = true)).card :=
        cardinal_filter_subset A a (fun l => I l (cols p) = true)
      _ = _ := congrArg Finset.card (same_rows 5 p)
  have bc_eq (p : P) : bc p = (Finset.univ.filter (fun l => k l = 3 ∧ I l (cols p) = true)).card := by
    calc
      bc p = (B.filter (fun l => I l (cols p) = true)).card :=
        cardinal_filter_subset B b (fun l => I l (cols p) = true)
      _ = _ := congrArg Finset.card (same_rows 3 p)
  have inside (p : Fin 19) : bc (.inl p) + 2*ac (.inl p) = 9 := by
    have read := profile (cols (.inl p))
    change _ = (if cols (.inl p) ∈ S then 9 else 4) at read
    have on_support : cols (.inl p) ∈ S := (s p).property
    rw [if_pos on_support] at read
    rw [ac_eq,bc_eq]
    exact read
  have outside (p : Fin 92) : bc (.inr p) + 2*ac (.inr p) = 4 := by
    have read := profile (cols (.inr p))
    change _ = (if cols (.inr p) ∈ S then 9 else 4) at read
    have off_support : cols (.inr p) ∉ S := (Finset.mem_sdiff.mp (t p).property).2
    rw [if_neg off_support] at read
    rw [ac_eq,bc_eq]
    exact read
  by_cases quad : ∃ p : Fin 19, ac (.inl p) = 4
  · exact noQuads ⟨M,row_sizes,col_sizes,row_pairs,col_pairs,rowA,rowB,rowC,inside,outside,quad⟩
  by_cases triple : ∃ p : Fin 19, ac (.inl p) = 3
  · apply noTriples
    refine ⟨M,row_sizes,col_sizes,row_pairs,col_pairs,rowA,rowB,rowC,inside,outside,?_,triple⟩
    intro p
    change ac (.inl p) ≤ 3
    have points := inside p
    have no_quad : ac (.inl p) ≠ 4 := fun same => quad ⟨p,same⟩
    omega
  apply noPairs
  refine ⟨M,row_sizes,col_sizes,row_pairs,col_pairs,rowA,rowB,rowC,inside,outside,?_⟩
  intro p
  change ac (.inl p) ≤ 2
  have points := inside p
  have no_quad : ac (.inl p) ≠ 4 := fun same => quad ⟨p,same⟩
  have no_triple : ac (.inl p) ≠ 3 := fun same => triple ⟨p,same⟩
  omega

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R1_H4_R1_H2_R1
