import OMAReductions.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace CountHeavyPoints
open Finset
open scoped Classical

private lemma sum_indicator {α : Type*} [Fintype α] (test : α → Prop) [DecidablePred test] :
    (∑ a, if test a then 1 else 0) = (univ.filter test).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem count_sixty_one (E : Fin 8 → Fin 111 → Bool)
    (rows : ∀ a, (univ.filter fun p => E a p = true).card = 11)
    (meet : ∀ a b, a ≠ b → ∃! p, E a p = true ∧ E b p = true)
    (bound : ∀ p, (univ.filter fun a => E a p = true).card ≤ 3)
    (oneTriple : (univ.filter fun p => (univ.filter fun a => E a p = true).card = 3).card = 1) :
    (univ.filter fun p => ∃ a, E a p = true).card = 61 := by
  classical
  let d (p : Fin 111) := (univ.filter fun a => E a p = true).card
  let I (a : Fin 8) (p : Fin 111) : Nat := if E a p = true then 1 else 0
  have byPoint (p : Fin 111) : d p = ∑ a, I a p := (sum_indicator _).symm
  have byRow (a : Fin 8) : ∑ p, I a p = 11 := (sum_indicator _).trans (rows a)
  have firstMoment : ∑ p, d p = 88 := by
    simp_rw [byPoint]
    rw [Finset.sum_comm]
    simp [byRow]
  have byPair (a b : Fin 8) : ∑ p, I a p * I b p = if a = b then 11 else 1 := by
    have eqCount : ∑ p, I a p * I b p = (univ.filter fun p => E a p = true ∧ E b p = true).card := by
      rw [← sum_indicator]
      apply Finset.sum_congr rfl
      intro p _
      cases ha : E a p <;> cases hb : E b p <;> simp [I, ha, hb]
    rw [eqCount]
    by_cases hab : a = b
    · subst b
      simpa using rows a
    · rw [if_neg hab]
      obtain ⟨p, hp, only⟩ := meet a b hab
      apply Finset.card_eq_one.mpr
      refine ⟨p, ?_⟩
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨only q, fun h => h ▸ hp⟩
  have bySquare (p : Fin 111) : d p * d p = ∑ a, ∑ b, I a p * I b p := by
    rw [byPoint, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  have secondMoment : ∑ p, d p * d p = 144 := by
    simp_rw [bySquare]
    calc
      _ = ∑ a, ∑ b, ∑ p, I a p * I b p := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = 144 := by simp_rw [byPair]; decide
  have occupied (p : Fin 111) : (∃ a, E a p = true) ↔ 0 < d p := by
    simp [d, Finset.card_pos, Finset.Nonempty]
  have pointIdentity (p : Fin 111) :
      2 * (if 0 < d p then 1 else 0) + d p * d p =
      3 * d p + 2 * (if d p = 3 then 1 else 0) := by
    have h : d p ≤ 3 := bound p
    have : d p = 0 ∨ d p = 1 ∨ d p = 2 ∨ d p = 3 := by omega
    rcases this with h | h | h | h <;> simp [h]
  have identity := Finset.sum_congr (s₁ := (univ : Finset (Fin 111))) rfl (fun p _ => pointIdentity p)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at identity
  rw [firstMoment, secondMoment, sum_indicator, sum_indicator, oneTriple] at identity
  simp_rw [occupied]
  omega

end CountHeavyPoints

-- Credit: @VestigeClub
theorem OMA.solution : OMA.R_Erdos723_erdos_723_variants_leq_11_R1_H2_R2_H3_R1_H2_R1_H2_R1_H1_R1_H1_R2.H1 := CountHeavyPoints.count_sixty_one
