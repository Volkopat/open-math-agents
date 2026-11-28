import OMAReductions.R_oeis_a005479_R1
import Mathlib

/-! The three listed terms 7 = L 4, 47 = L 8 and 2207 = L 16 are prime Lucas numbers ending in 7
whose indices are not prime. -/

namespace OMA.Step_oeis_a005479_R1_H1

open OMA.S_oeis_a005479

theorem lucas_four : lucas 4 = 7 := by decide

theorem lucas_eight : lucas 8 = 47 := by decide

theorem lucas_sixteen : lucas 16 = 2207 := by decide

theorem prime_2207 : Nat.Prime 2207 := by norm_num

end OMA.Step_oeis_a005479_R1_H1

open OMA.S_oeis_a005479 OMA.Step_oeis_a005479_R1_H1 in
theorem OMA.solution : OMA.R_oeis_a005479_R1.H1 := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨⟨4, lucas_four⟩, by norm_num, by norm_num⟩
    · exact ⟨⟨8, lucas_eight⟩, by norm_num, by norm_num⟩
    · exact ⟨⟨16, lucas_sixteen⟩, prime_2207, by norm_num⟩
  · intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨4, by norm_num, by norm_num, lucas_four, by norm_num⟩
    · exact ⟨8, by norm_num, by norm_num, lucas_eight, by norm_num⟩
    · exact ⟨16, by norm_num, by norm_num, lucas_sixteen, prime_2207⟩
