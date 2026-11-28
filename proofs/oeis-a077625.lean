import OMAStatements.S_oeis_a077625
import Mathlib

/-!
# OEIS A077625: `2^n - 1` is a perfect square only for `n = 1`

For `n ≥ 2` we have `2^n - 1 ≡ 3 (mod 4)`, while a square is `0` or `1` modulo `4`.
For `n = 1`, `2 - 1 = 1 = 1²`.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a077625.main := by
  intro n hn
  constructor
  · rintro ⟨m, hm⟩
    by_contra hne
    -- `n ≥ 2`, so `4 ∣ 2^n`
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have h4 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
    have hpos : 0 < 2 ^ k := by positivity
    have hsq : (m * m) % 4 = 0 ∨ (m * m) % 4 = 1 := by
      have hm4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [Nat.mul_mod]
      interval_cases m % 4 <;> simp
    omega
  · rintro rfl
    exact ⟨1, by norm_num⟩
