import OMAReductions.R_VizingConjecture_vizing_conjecture_R1
import Mathlib

-- Step VizingConjecture.vizing_conjecture.R1.H1: hypothesis H1 of reduction VizingConjecture.vizing_conjecture.R1
-- Credit: @ivillar

/-!
Vizing's inequality when one factor has domination number at most one: projecting a dominating
set of the product to a factor gives a dominating set of that factor.
-/
open SimpleGraph

namespace F2Viz

theorem snd_bound {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] (G : SimpleGraph α) (H : SimpleGraph β) :
    H.dominationNumber ≤ (G □ H).dominationNumber := by
  obtain ⟨D, hD, hcard⟩ := exists_isNDominatingSet_dominationNumber (G □ H)
  refine le_trans (dominationNumber_le_of_isDominating H (D.image Prod.snd) ?_) ?_
  · intro v
    obtain ⟨a⟩ := ‹Nonempty α›
    rcases hD (a, v) with h | ⟨⟨c, w⟩, hw, hadj⟩
    · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp h)))
    · rw [boxProd_adj] at hadj
      rcases hadj with ⟨-, hvw⟩ | ⟨hvw, -⟩
      · obtain rfl : v = w := hvw
        exact Or.inl (Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hw)))
      · exact Or.inr ⟨w, Finset.mem_coe.mpr (Finset.mem_image_of_mem Prod.snd (Finset.mem_coe.mp hw)),
          hvw⟩
  · exact hcard ▸ Finset.card_image_le

theorem nonempty_of_ne_zero {α : Type} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    (h : G.dominationNumber ≠ 0) : Nonempty α := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  have h0 := dominationNumber_le_of_isDominating G ∅ (fun v => isEmptyElim v)
  rw [Finset.card_empty] at h0
  exact h (Nat.le_zero.mp h0)

theorem small : ∀ {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (H : SimpleGraph β),
    G.dominationNumber ≤ 1 ∨ H.dominationNumber ≤ 1 →
    G.dominationNumber * H.dominationNumber ≤ (G □ H).dominationNumber := by
  intro α β _ _ _ _ G H h
  rcases h with h | h
  · rcases Nat.eq_zero_or_pos G.dominationNumber with h0 | hpos
    · rw [h0, zero_mul]
      exact Nat.zero_le _
    · have h1 : G.dominationNumber = 1 := by omega
      have hne : Nonempty α := nonempty_of_ne_zero G (by omega)
      rw [h1, one_mul]
      exact snd_bound G H
  · rcases Nat.eq_zero_or_pos H.dominationNumber with h0 | hpos
    · rw [h0, mul_zero]
      exact Nat.zero_le _
    · have h1 : H.dominationNumber = 1 := by omega
      have hne : Nonempty β := nonempty_of_ne_zero H (by omega)
      rw [h1, mul_one]
      exact dominationNumber_le_dominationNumber_boxProd G H

end F2Viz

theorem OMA.solution : OMA.R_VizingConjecture_vizing_conjecture_R1.H1 :=
  F2Viz.small
