import OMAStatements.S_oeis_a077624
import Mathlib

/-!
# OEIS A077624: `2^n + 1` is a perfect square only for `n = 3`

Suppose `2^n + 1 = m²`. Then `m` is odd, say `m = 2t + 1`, and `2^n = 4 t (t + 1)`, so
`t (t + 1) = 2^(n-2)`. Both `t` and `t + 1` are then powers of two, `t = 2^a` and
`t + 1 = 2^b`. From `2^a + 1 = 2^b`: if `a ≥ 1` the left side is odd, forcing `b = 0`, which is
impossible; so `a = 0`, `b = 1`, `t = 1`, `m = 3` and `n = 3`.
-/

namespace OMA.A077624

/-- `2^a + 1 = 2^b` forces `a = 0`. -/
lemma pow_add_one {a b : ℕ} (h : 2 ^ a + 1 = 2 ^ b) : a = 0 := by
  by_contra ha
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have : 0 < 2 ^ (a' + 1) := by positivity
    simp at h
  · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [pow_succ, pow_succ] at h
    omega

end OMA.A077624

open OMA.A077624 in
theorem OMA.solution : type_of% @OMA.S_oeis_a077624.main := by
  intro n
  constructor
  · rintro ⟨m, hm⟩
    -- `m` is odd
    have hmodd : m % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one m with h | h
      · exfalso
        have h1 : (m * m) % 2 = 0 := by rw [Nat.mul_mod, h]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · -- `2 = m²` is impossible
          have : m * m = 2 := by simpa using hm.symm
          have hm2 : m ≤ 1 ∨ 2 ≤ m := by omega
          rcases hm2 with h' | h'
          · interval_cases m <;> omega
          · nlinarith
        · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
          rw [pow_succ] at hm
          omega
      · exact h
    obtain ⟨t, rfl⟩ : ∃ t, m = 2 * t + 1 := ⟨m / 2, by omega⟩
    -- `2^n = 4 t (t + 1)`
    have h1 : 2 ^ n = 4 * (t * (t + 1)) := by
      have : (2 * t + 1) * (2 * t + 1) = 4 * (t * (t + 1)) + 1 := by ring
      omega
    have ht : 0 < t := by
      rcases Nat.eq_zero_or_pos t with rfl | h
      · have : 0 < 2 ^ n := by positivity
        omega
      · exact h
    -- both `t` and `t + 1` are powers of two
    have hd1 : t ∣ 2 ^ n := ⟨4 * (t + 1), by rw [h1]; ring⟩
    have hd2 : t + 1 ∣ 2 ^ n := ⟨4 * t, by rw [h1]; ring⟩
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
    obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have ha0 : a = 0 := pow_add_one (a := a) (b := b) (by rw [← ha, ← hb])
    subst ha0
    have ht1 : t = 1 := by simpa using ha
    subst ht1
    -- `2^n = 8`
    have h8 : 2 ^ n = 2 ^ 3 := by rw [h1]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h8
  · rintro rfl
    exact ⟨3, by norm_num⟩
