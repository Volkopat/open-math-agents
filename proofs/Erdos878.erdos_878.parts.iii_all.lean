import FormalConjectures.ErdosProblems.«878»

open Erdos878 Finset

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @Erdos878.erdos_878.parts.iii_all := by
  intro h
  let A : Finset ℕ := {125, 128, 189}
  have bound : 442 ≤ F 210 := by
    refine le_trans (by decide) (Finset.le_sup (b := A) ?_)
    simp only [mem_filter, mem_powerset]
    refine ⟨by decide, by decide, ?_, ?_⟩
    · change ∀ a ∈ A, ∀ b ∈ A, a ≠ b → a.Coprime b
      decide
    · have hd : ∀ a ∈ A, a ∣ 210 ^ 7 := by decide
      exact fun a ha p hp hpa => hp.dvd_of_dvd_pow (hpa.trans (hd a ha))
  have small : maxUpTo f 210 = 383 := by decide +kernel
  rw [h] at small
  exact (show F 210 ≤ maxUpTo F 210 from le_sup (mem_range.mpr (by decide))).not_gt (by omega)
