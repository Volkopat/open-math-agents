import OMAStatements.S_oeis_a165719
import Mathlib

/-
A165719: integers of the form k(k+9)/8.

8 divides k(k+9) exactly when k is 0 or 7 modulo 8, that is k = 8m or k = 8m - 1 with m >= 1.
For k = 8m the value is m(8m+9), prime only for m = 1, giving 17. For k = 8m - 1 the value is
(8m-1)(m+1), a product of two factors larger than 1. So 17 is the only prime term.
-/

namespace OMA.P165719

lemma res (k : ℕ) : 8 ∣ k * (k + 9) ↔ k % 8 = 0 ∨ k % 8 = 7 := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod, Nat.add_mod]
  have h := Nat.mod_lt k (by norm_num : 0 < 8)
  interval_cases k % 8 <;> simp

lemma main' :
    (∀ k : ℕ, 1 ≤ k →
      ((8 ∣ k * (k + 9)) ↔ ∃ m : ℕ, 1 ≤ m ∧ (k = 8 * m - 1 ∨ k = 8 * m))) ∧
    (∀ v : ℕ, ((∃ k : ℕ, 1 ≤ k ∧ k * (k + 9) = 8 * v) ∧ v.Prime) ↔ v = 17) := by
  have key : ∀ k : ℕ, 1 ≤ k →
      ((8 ∣ k * (k + 9)) ↔ ∃ m : ℕ, 1 ≤ m ∧ (k = 8 * m - 1 ∨ k = 8 * m)) := by
    intro k hk
    rw [res]
    constructor
    · rintro (h | h)
      · exact ⟨k / 8, by omega, Or.inr (by omega)⟩
      · exact ⟨k / 8 + 1, by omega, Or.inl (by omega)⟩
    · rintro ⟨m, hm, h | h⟩ <;> omega
  refine ⟨key, fun v => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨k, hk, hkv⟩, hv⟩
    obtain ⟨m, hm, h | h⟩ := (key k hk).1 ⟨v, hkv⟩
    · exfalso
      have hv' : v = (8 * m - 1) * (m + 1) := by
        obtain ⟨c, rfl⟩ : ∃ c, m = c + 1 := ⟨m - 1, by omega⟩
        subst h
        have e : 8 * (c + 1) - 1 = 8 * c + 7 := by omega
        rw [e] at hkv ⊢
        nlinarith
      rw [hv'] at hv
      rcases Nat.prime_mul_iff.1 hv with ⟨-, h2⟩ | ⟨-, h2⟩ <;> omega
    · subst h
      have hv' : v = m * (8 * m + 9) := by nlinarith
      rw [hv'] at hv ⊢
      rcases Nat.prime_mul_iff.1 hv with ⟨-, h2⟩ | ⟨-, h2⟩
      · omega
      · subst h2; norm_num
  · rintro rfl
    exact ⟨⟨8, by norm_num, by norm_num⟩, by norm_num⟩

end OMA.P165719

theorem OMA.solution : type_of% @OMA.S_oeis_a165719.main := 
  OMA.P165719.main'
