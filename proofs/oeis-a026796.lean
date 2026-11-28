import OMAStatements.S_oeis_a026796
import Mathlib

-- Shorter disproof of OEIS A026796 (a 4 = 0 but b 0 is positive). This version: @tylerpixel

open OMA.S_oeis_a026796 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a026796.main) := fun h => by
  have : Nonempty (Balanced 0) := ⟨⟨⟨0, by simp, by simp⟩, by simp⟩⟩
  have e : a 4 = 0 := Fintype.card_eq_zero_iff.2 ⟨fun ⟨p, h3, hall⟩ => by
    obtain ⟨r, hr⟩ := Multiset.exists_cons_of_mem h3
    have hs := p.parts_sum
    rw [hr, Multiset.sum_cons] at hs
    rcases Multiset.empty_or_exists_mem r with h0 | ⟨x, hx⟩
    · simp [h0] at hs
    · have := hall x (hr ▸ Multiset.mem_cons_of_mem hx)
      have := Multiset.le_sum_of_mem hx
      omega⟩
  exact Fintype.card_ne_zero ((h 0).symm.trans e)
