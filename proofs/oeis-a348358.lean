import OMAStatements.S_oeis_a348358
import Mathlib

namespace OMA.A348358Proof

open OMA.S_oeis_a348358

/-- In a base `b ≥ 4`, the number `2 * b + 3` has the digits `2, 3` (most significant first). -/
lemma digits_two_three (b : ℕ) (hb : 4 ≤ b) : Nat.digits b (2 * b + 3) = [3, 2] := by
  have h1 : 2 * b + 3 = 3 + b * 2 := by ring
  rw [h1, Nat.digits_add b (by omega) 3 2 (by omega) (Or.inl (by norm_num)),
    Nat.digits_of_lt b 2 (by norm_num) (by omega)]

/-- In a base `b ≥ 4`, the number `2 * b + 3` is the concatenation of the primes `2` and `3`. -/
lemma concat_two_three (b : ℕ) (hb : 4 ≤ b) : IsConcatOfSmallerPrimes b (2 * b + 3) := by
  refine ⟨[[3], [2]], ?_, ?_⟩
  · rw [digits_two_three b hb]
    rfl
  · intro B hB
    simp at hB
    rcases hB with rfl | rfl
    · simp only [Nat.ofDigits_singleton]
      exact ⟨by simp, Nat.prime_three, by omega⟩
    · simp only [Nat.ofDigits_singleton]
      exact ⟨by simp, Nat.prime_two, by omega⟩

end OMA.A348358Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a348358.main := by
  intro p hp h7
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h9 : p ≠ 9 := by
    rintro rfl
    norm_num at hp
  obtain ⟨b, rfl⟩ : ∃ b, p = 2 * b + 3 := ⟨(p - 3) / 2, by omega⟩
  exact ⟨b, by omega, OMA.A348358Proof.concat_two_three b (by omega)⟩
