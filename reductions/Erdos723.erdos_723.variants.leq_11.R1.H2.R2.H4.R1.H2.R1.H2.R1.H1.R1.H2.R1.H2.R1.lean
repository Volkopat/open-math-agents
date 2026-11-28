import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic

/-! Isolate the smallest of the nine-pair layouts and partition the other nine. -/

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1

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
  ¬ ∃ M : Rows → Points → Bool, Valid M ∧ ∀ p : Fin 19, column M p = layout 0 p

def H2 : Prop := Excludes 1 4
def H3 : Prop := Excludes 4 7
def H4 : Prop := Excludes 7 10

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1.H2 := by
  intro first low middle high
  change Excludes 0 10
  intro i _ belowTen witness
  by_cases zero : i.val = 0
  · have atZero : i = 0 := Fin.ext zero
    subst i
    exact first witness
  by_cases belowFour : i.val < 4
  · exact low i (by omega) belowFour witness
  by_cases belowSeven : i.val < 7
  · exact middle i (by omega) belowSeven witness
  exact high i (by omega) belowTen witness

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1_H2_R1
