import OMAStatements.S_oeis_a122834
import Mathlib

/-!
# A122834: under the new Mersenne conjecture, the two numbers are prime together

Let `p` be an odd prime of the special form.  If `2 ^ p - 1` is prime, the first clause of the
conjecture makes `(2 ^ p + 1) / 3` prime.  If `(2 ^ p + 1) / 3` is prime, the second clause makes
`2 ^ p - 1` prime.  So either both are prime or neither is; and both exceed `1` because
`2 ^ p ≥ 8`.
-/

open OMA.S_oeis_a122834 in
theorem OMA.solution : type_of% @OMA.S_oeis_a122834.main := by
  intro hconj p hp hodd hform
  obtain ⟨h1, h2, -⟩ := hconj p hodd
  have hp3 : 3 ≤ p := by
    rcases hp.eq_two_or_odd' with rfl | _
    · exact absurd hodd (by decide)
    · have := hp.two_le
      rcases Nat.odd_iff.mp hodd with _
      omega
  have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp3
  by_cases ha : (2 ^ p - 1).Prime
  · exact Or.inl ⟨ha, h1 ⟨hform, ha⟩⟩
  · by_cases hb : ((2 ^ p + 1) / 3).Prime
    · exact absurd (h2 ⟨hform, hb⟩) ha
    · exact Or.inr ⟨⟨by omega, ha⟩, ⟨by omega, hb⟩⟩
