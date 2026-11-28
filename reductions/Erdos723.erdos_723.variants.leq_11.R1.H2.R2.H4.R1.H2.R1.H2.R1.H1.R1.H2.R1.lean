import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic

/-! Normalize the remaining one-triple arrangements of the six five-secants. -/

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1

open Finset
open scoped BigOperators

private abbrev Rows := Fin 6 ⊕ (Fin 37 ⊕ Fin 68)
private abbrev Points := Fin 19 ⊕ Fin 92

private def layout (i : Fin 18) (p : Fin 19) : Finset (Fin 6) :=
  ((([[[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [3, 4, 5], [0], [1], [2], [3], [4], [5], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 5], [3, 4, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [2, 5], [3, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [0, 5], [2, 3, 5], [1], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [1, 5], [2, 3, 5], [0], [1], [2], [3], [4], [4], [5], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [0, 5], [3, 5], [1, 4, 5], [1], [2], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [1, 5], [2, 5], [3, 4, 5], [0], [1], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [1, 5], [2, 3, 5], [4, 5], [0], [1], [2], [3], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 3, 4], [2, 5], [3, 5], [4, 5], [0], [1], [1], [2], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [0, 3], [1, 2, 3], [1, 4], [2, 4], [3, 4], [1, 5], [2, 5], [3, 5], [0], [0], [1], [2], [3], [4], [4], [5], [5]],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [3, 4, 5], [1], [2], [3], [4], [5], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [0, 5], [2, 5], [3, 4, 5], [1], [2], [3], [4], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [2, 5], [3, 5], [1], [2], [3], [4], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [2, 5], [3, 5], [4, 5], [0], [1], [2], [3], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [2, 4], [3, 4], [1, 5], [2, 3, 5], [4, 5], [0], [1], [2], [3], [4], [5], [5], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [1, 5], [3, 4, 5], [2], [3], [4], [5], [5], [], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [0, 4], [1, 4], [2, 3, 4], [0, 5], [2, 5], [3, 5], [4, 5], [1], [2], [3], [4], [5], [], []],
   [[0, 1], [0, 2], [1, 2], [0, 3], [1, 3], [2, 3], [0, 4], [1, 4], [2, 4], [0, 5], [1, 5], [2, 5], [3, 4, 5], [3], [4], [5], [], [], []]] : List (List (List (Fin 6))))[i.val]!)[p.val]!).toFinset

private def column (M : Rows → Points → Bool) (p : Fin 19) : Finset (Fin 6) :=
  univ.filter fun a => M (.inl a) (.inl p) = true

private def Valid (M : Rows → Points → Bool) : Prop :=
  let A (p : Points) := (univ.filter fun a : Fin 6 => M (.inl a) p = true).card
  let B (p : Points) := (univ.filter fun b : Fin 37 => M (.inr (.inl b)) p = true).card
  (∀ l, (univ.filter fun p => M l p = true).card = 11) ∧
  (∀ p, (univ.filter fun l => M l p = true).card = 11) ∧
  (∀ l m, l ≠ m → ∃! p, M l p = true ∧ M m p = true) ∧
  (∀ p q, p ≠ q → ∃! l, M l p = true ∧ M l q = true) ∧
  (∀ a : Fin 6, (univ.filter fun p : Fin 19 => M (.inl a) (.inl p) = true).card = 5) ∧
  (∀ b : Fin 37, (univ.filter fun p : Fin 19 => M (.inr (.inl b)) (.inl p) = true).card = 3) ∧
  (∀ c : Fin 68, (univ.filter fun p : Fin 19 => M (.inr (.inr c)) (.inl p) = true).card = 1) ∧
  (∀ p : Fin 19, B (.inl p) + 2 * A (.inl p) = 9) ∧
  (∀ p : Fin 92, B (.inr p) + 2 * A (.inr p) = 4)

private def Excludes (lo hi : Nat) : Prop :=
  ∀ i : Fin 18, lo ≤ i.val → i.val < hi →
    ¬ ∃ M : Rows → Points → Bool, Valid M ∧ ∀ p : Fin 19, column M p = layout i p

def H1 : Prop :=
  ∀ (C : Fin 19 → Finset (Fin 6)),
    (∀ p q, p ≠ q → (C p ∩ C q).card ≤ 1) →
    (∀ a, (univ.filter fun p => a ∈ C p).card = 5) →
    (∀ p, (C p).card ≤ 3) →
    let F := (univ.filter fun p => 2 ≤ (C p).card).image C
    let x := (F.filter fun T => T.card = 2).card
    let y := (F.filter fun T => T.card = 3).card
    y = 1 → 9 ≤ x → x ≤ 12 →
    let patterns : List (List Nat) := [[3,5,6,9,10,12,17,18,33,34,52], [3,5,6,9,10,12,17,18,33,52], [3,5,6,9,10,17,18,28,33,34], [3,5,6,9,10,17,18,28,33,36], [3,5,6,9,10,17,18,33,36,56], [3,5,6,9,10,20,24,36,40,49]]
    (¬ ∃ e : Equiv.Perm (Fin 6), ∃ j : Fin 6,
      (F.image fun X => ∑ a ∈ X.map e.toEmbedding, (2 : Nat)^a.val) = (patterns[j.val]!).toFinset) →
    ∃ (i : Fin 18) (e : Equiv.Perm (Fin 6)) (π : Equiv.Perm (Fin 19)),
      ∀ p, (C (π p)).map e.toEmbedding = layout i p

def H2 : Prop := Excludes 0 10

def H3 : Prop := Excludes 10 15

def H4 : Prop := Excludes 15 18

lemma card_filter_relabel {X Y : Type} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (P : Y → Prop) [DecidablePred P] :
    (Finset.univ.filter fun x => P (e x)).card = (Finset.univ.filter P).card := by
  have mapped := Finset.filter_map (s := Finset.univ) (p := P) (f := e.toEmbedding)
  rw [Finset.map_univ_equiv] at mapped
  rw [mapped, Finset.card_map]
  rfl


lemma unique_relabel {X Y : Type} (e : X ≃ Y) (P : Y → Prop)
    (h : ∃! y, P y) : ∃! x, P (e x) := by
  obtain ⟨y,yes,only⟩ := h
  refine ⟨e.symm y,?_ ,?_⟩
  · simpa only [Equiv.apply_symm_apply] using yes
  · intro x hx
    apply e.injective
    simpa only [Equiv.apply_symm_apply] using only (e x) hx

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1.H2 := by
  intro normalize pairsNine pairsTen pairsLarge
  unfold OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1.H2
  dsimp only
  rintro ⟨M, rowSizes, colSizes, rowPairs, colPairs, aSizes, bSizes, cSizes, inside, outside,
    maxSupport, triple, lower, upper, residual⟩
  classical
  let C (p : Fin 19) := Finset.univ.filter fun a : Fin 6 => M (.inl a) (.inl p) = true
  have rows (a : Fin 6) : (Finset.univ.filter fun p => a ∈ C p).card = 5 := by
    simpa only [C,Finset.mem_filter,Finset.mem_univ,true_and] using aSizes a
  have bound (p : Fin 19) : (C p).card ≤ 3 := by
    exact maxSupport p
  have overlap (p q : Fin 19) (different : p ≠ q) : (C p ∩ C q).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have both (x : Fin 6) (hx : x ∈ C p ∩ C q) :
        M (.inl x) (.inl p) = true ∧ M (.inl x) (.inl q) = true := by
      obtain ⟨hp,hq⟩ := Finset.mem_inter.mp hx
      exact ⟨(Finset.mem_filter.mp hp).2,(Finset.mem_filter.mp hq).2⟩
    obtain ⟨_,_,unique⟩ := colPairs (.inl p) (.inl q) (fun eq => different (Sum.inl.inj eq))
    exact Sum.inl.inj ((unique (.inl a) (both a ha)).trans (unique (.inl b) (both b hb)).symm)
  obtain ⟨i,e,π,matched⟩ := normalize C overlap rows bound triple lower upper residual
  let r := Equiv.sumCongr e.symm (Equiv.refl (Fin 37 ⊕ Fin 68))
  let c := Equiv.sumCongr π (Equiv.refl (Fin 92))
  let N (l : Fin 6 ⊕ (Fin 37 ⊕ Fin 68)) (p : Fin 19 ⊕ Fin 92) := M (r l) (c p)
  have witness : ∃ M : Rows → Points → Bool, Valid M ∧
      ∀ p : Fin 19, column M p = layout i p := by
    refine ⟨N, ?_, ?_⟩
    · refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
      · intro l
        exact (card_filter_relabel c (fun p => M (r l) p = true)).trans (rowSizes (r l))
      · intro p
        exact (card_filter_relabel r (fun l => M l (c p) = true)).trans (colSizes (c p))
      · intro l m ne
        exact unique_relabel c _ (rowPairs (r l) (r m) (fun eq => ne (r.injective eq)))
      · intro p q ne
        exact unique_relabel r _ (colPairs (c p) (c q) (fun eq => ne (c.injective eq)))
      · intro a
        exact (card_filter_relabel π (fun p => M (.inl (e.symm a)) (.inl p) = true)).trans (aSizes (e.symm a))
      · intro b
        exact (card_filter_relabel π (fun p => M (.inr (.inl b)) (.inl p) = true)).trans (bSizes b)
      · intro d
        exact (card_filter_relabel π (fun p => M (.inr (.inr d)) (.inl p) = true)).trans (cSizes d)
      · intro p
        change _ + 2 * (Finset.univ.filter fun a : Fin 6 => M (.inl (e.symm a)) (.inl (π p)) = true).card = 9
        rw [card_filter_relabel e.symm (fun a => M (.inl a) (.inl (π p)) = true)]
        exact inside (π p)
      · intro p
        change _ + 2 * (Finset.univ.filter fun a : Fin 6 => M (.inl (e.symm a)) (.inr p) = true).card = 4
        rw [card_filter_relabel e.symm (fun a => M (.inl a) (.inr p) = true)]
        exact outside p
    · intro p
      refine Eq.trans ?_ (matched p)
      ext a
      rw [Finset.mem_map_equiv]
      simp only [C,column,Finset.mem_filter,Finset.mem_univ,true_and] <;> rfl
  by_cases belowTen : i.val < 10
  · exact pairsNine i (by omega) belowTen witness
  by_cases belowFifteen : i.val < 15
  · exact pairsTen i (by omega) belowFifteen witness
  exact pairsLarge i (by omega) i.isLt witness

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1
