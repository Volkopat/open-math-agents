import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin

namespace OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1

private def isPerfectMatching (L : Finset (Fin 111)) (M : Finset (Finset (Fin 111))) : Prop :=
  M.card = 3 ∧ (∀ e ∈ M, e ⊆ L ∧ e.card = 2) ∧
    ∀ l ∈ L, ∃! e, e ∈ M ∧ l ∈ e

private def isExteriorLabel (L : Finset (Fin 111)) (C : Finset (Finset (Finset (Fin 111)))) : Prop :=
  C.card = 2 ∧ (∀ M ∈ C, isPerfectMatching L M) ∧
    ∀ M ∈ C, ∀ N ∈ C, M ≠ N → Disjoint M N

private def HasStarCover : Prop :=
  ∃ L : Finset (Fin 111), L.card = 6 ∧
    ∃ stars : ↥(L.powersetCard 2) → Fin 6 → Finset (Finset (Finset (Finset (Fin 111)))),
      (∀ e i C, C ∈ stars e i → isExteriorLabel L C ∧ ∀ M ∈ C, e.val ∉ M) ∧
      (∀ e i M, isPerfectMatching L M → e.val ∉ M → ∃! C, C ∈ stars e i ∧ M ∈ C) ∧
      (∀ e C, isExteriorLabel L C → (∀ M ∈ C, e.val ∉ M) → ∃! i, C ∈ stars e i) ∧
      ∀ e f, e ≠ f → ∀ i j, (stars e i ∩ stars f j).card ≤ 1

def H1 : Prop :=
  ∀ incidence : Fin 111 → Fin 111 → Bool,
    (∀ l, (Finset.univ.filter fun p => incidence l p = true).card = 11) →
    (∀ p, (Finset.univ.filter fun l => incidence l p = true).card = 11) →
    (∀ l m, l ≠ m → ∃! p, incidence l p = true ∧ incidence m p = true) →
    (∀ p q, p ≠ q → ∃! l, incidence l p = true ∧ incidence l q = true) →
    ∀ S : Finset (Fin 111), S.card = 16 →
      (∀ l, 2 ∣ (S.filter fun p => incidence l p = true).card) →
      (∃ l, (S.filter fun p => incidence l p = true).card = 6) → HasStarCover

def H2 : Prop := ¬ HasStarCover

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1.H3 := by
  intro transfer excluded incidence rows columns rowPairs columnPairs
  dsimp only
  rintro ⟨marked, ⟨size, even, _, _⟩, one⟩
  let long := Finset.univ.filter fun l => (marked.filter fun p => incidence l p = true).card = 6
  have count : long.card = 1 := one
  obtain ⟨l, hl⟩ := Finset.card_pos.mp (show 0 < long.card by rw [count]; decide)
  exact excluded (transfer incidence rows columns rowPairs columnPairs marked size
    (fun r => (even r).1) ⟨l, (Finset.mem_filter.mp hl).2⟩)

end OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H3_R1
