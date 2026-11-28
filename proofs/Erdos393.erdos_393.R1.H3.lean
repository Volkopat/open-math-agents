import OMAReductions.R_Erdos393_erdos_393_R1

/-! For n at least 2 the set of admissible gaps is nonempty (n! = 1 * 2 * ... * n), so f n is
attained. Translating the factors of an attaining factorisation down by its least factor a gives
shifts in {0, ..., f n}; the shifts 0 and f n are distinct, so there are at least two. The
argument follows the lemma pattern of the merged reduction
Erdos393.erdos_393.variants.bui_pratt_zaharescu.R1 by @marcusbuffett. -/

namespace OMA.R_Erdos393_erdos_393_R1_H3

open Finset Erdos393
open scoped Nat

theorem shifts (n : ℕ) (hn : 2 ≤ n) :
    ∃ T ⊆ Finset.range (f n + 1), 2 ≤ T.card ∧ ∃ a : ℕ, ∏ i ∈ T, (a + i) = n ! := by
  have hne : {m : ℕ | 1 ≤ m ∧ ∃ a : ℕ, ∃ s ⊆ Finset.Icc a (a + m), a ∈ s ∧ a + m ∈ s ∧
      ∏ i ∈ s, i = n !}.Nonempty := by
    refine ⟨n - 1, by omega, 1, Finset.Ico 1 (n + 1), ?_, ?_, ?_, Finset.prod_Ico_id_eq_factorial n⟩
    · intro i hi
      have h := Finset.mem_Ico.mp hi
      exact Finset.mem_Icc.mpr ⟨h.1, by omega⟩
    · exact Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
    · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  obtain ⟨hm1, a, s, hs, ha, hb, hprod⟩ := Nat.sInf_mem hne
  change 1 ≤ f n at hm1
  change s ⊆ Finset.Icc a (a + f n) at hs
  change a + f n ∈ s at hb
  change ∏ i ∈ s, i = n ! at hprod
  have lea : ∀ i ∈ s, a ≤ i := fun i hi => (Finset.mem_Icc.mp (hs hi)).1
  have inj : Set.InjOn (fun i : ℕ => i - a) ↑s := by
    intro i hi j hj e
    have := lea i hi
    have := lea j hj
    simp only at e
    omega
  refine ⟨s.image (fun i => i - a), ?_, ?_, a, ?_⟩
  · intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    have := (Finset.mem_Icc.mp (hs hj)).2
    exact Finset.mem_range.mpr (by omega)
  · rw [Finset.card_image_of_injOn inj]
    exact Finset.one_lt_card.mpr ⟨a, ha, a + f n, hb, by omega⟩
  · rw [Finset.prod_image inj]
    exact (Finset.prod_congr rfl fun i hi => by have := lea i hi; omega).trans hprod

end OMA.R_Erdos393_erdos_393_R1_H3

theorem OMA.solution : OMA.R_Erdos393_erdos_393_R1.H3 :=
  OMA.R_Erdos393_erdos_393_R1_H3.shifts
