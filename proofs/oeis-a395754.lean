import OMAStatements.S_oeis_a395754
import Mathlib

namespace OddRadicalCandidates

open Finset UniqueFactorizationMonoid OMA.S_oeis_a395754

private theorem candidates_empty (m : ℕ) (hm : Odd m) : candidates m = ∅ := by
  classical
  apply not_nonempty_iff_eq_empty.mp
  rintro ⟨k, hk⟩
  obtain ⟨_, hpos, hk₁, hk₂⟩ := mem_filter.mp hk
  have htwo : Irreducible (2 : ℕ) := (Nat.prime_iff.mp Nat.prime_two).irreducible
  have hdvd : 2 ∣ m := by
    by_cases he : 2 ∣ k
    · exact ((dvd_radical_iff_of_irreducible htwo hpos.ne').mpr he).trans hk₁
    · have he' : 2 ∣ k + 1 := by omega
      exact ((dvd_radical_iff_of_irreducible htwo (Nat.succ_ne_zero k)).mpr he').trans hk₂
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hdvd)

end OddRadicalCandidates

open OMA.S_oeis_a395754 in
theorem OMA.solution : type_of% @OMA.S_oeis_a395754.main := by
  intro n _ h
  unfold a
  rw [OddRadicalCandidates.candidates_empty _ h]
  rfl