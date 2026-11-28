import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1_H3_R1

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

private def excludesLayout (i : Fin 18) : Prop :=
  ¬ ∃ M : Rows → Points → Bool, Valid M ∧ ∀ p : Fin 19, column M p = layout i p

private def Excludes (lo hi : Nat) : Prop :=
  ∀ i : Fin 18, lo ≤ i.val → i.val < hi → excludesLayout i

def H1 : Prop := Excludes 10 12
def H2 : Prop := Excludes 12 14
def H3 : Prop := Excludes 14 15

theorem main : H1 → H2 → H3 →
    OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1.H3 := by
  intro h1 h2 h3
  change Excludes 10 15
  rintro i hi hlt w
  by_cases h12 : i.val < 12
  · exact h1 i hi h12 w
  · by_cases h14 : i.val < 14
    · exact h2 i (by omega) h14 w
    · exact h3 i (by omega) hlt w

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H4_R1_H2_R1_H2_R1_H1_R1_H2_R1_H3_R1
