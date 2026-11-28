import OMAStatements.S_oeis_a235202
import Mathlib

namespace OMA.A235202Proof

open OMA.S_oeis_a235202

/-! ### Every `quat n` has base-4 digit `0` or `1` at the place `4 ^ 4`, so `quat n ≠ 512 = 2 * 4 ^ 4` -/

/-- Peeling off a binary place. -/
theorem ofDigits_24 (n : ℕ) :
    Nat.ofDigits 4 (digits24 n) = n % 2 + 4 * Nat.ofDigits 4 (digits42 (n / 2)) := by
  rw [digits24]
  split_ifs with h
  · subst h
    rw [digits42]
    simp
  · simp [Nat.ofDigits_cons]

/-- Peeling off a quaternary place. -/
theorem ofDigits_42 (n : ℕ) :
    Nat.ofDigits 4 (digits42 n) = n % 4 + 4 * Nat.ofDigits 4 (digits24 (n / 4)) := by
  rw [digits42]
  split_ifs with h
  · subst h
    rw [digits24]
    simp
  · simp [Nat.ofDigits_cons]

/-- `quat n = d0 + 4 d1 + 16 d2 + 64 d3 + 256 d4 + 1024 t` with `d0, d2, d4 ≤ 1` and `d1, d3 ≤ 3`. -/
theorem quat_ne_512 (n : ℕ) : quat n ≠ 512 := by
  intro h
  have e1 := ofDigits_24 n
  have e2 := ofDigits_42 (n / 2)
  have e3 := ofDigits_24 (n / 2 / 4)
  have e4 := ofDigits_42 (n / 2 / 4 / 2)
  have e5 := ofDigits_24 (n / 2 / 4 / 2 / 4)
  unfold quat at h
  omega

/-! ### `512` is in A126001: `512 = 2 ^ 9` with `9 = 2 * 4 + 1`, `4 = 2 ^ (2 * 1)`, and `1` has no odd bit -/

theorem geZero_one : geZero 1 := by
  rw [geZero]
  intro r hr
  have h0 : (r : ℕ) = 0 := by
    have := r.isLt
    omega
  rw [h0] at hr
  exact absurd hr (by decide)

theorem zeroLf_four : zeroLf 4 := by
  rw [zeroLf]
  exact ⟨⟨1, by norm_num⟩, by decide, geZero_one⟩

theorem geZero_512 : geZero 512 := by
  rw [geZero]
  intro r hr
  have h : Nat.testBit (2 ^ 9) (2 * (r : ℕ) + 1) = decide (9 = 2 * (r : ℕ) + 1) := Nat.testBit_two_pow
  rw [show (2 : ℕ) ^ 9 = 512 by norm_num, hr] at h
  have h9 : 9 = 2 * (r : ℕ) + 1 := of_decide_eq_true h.symm
  have h4 : (r : ℕ) = 4 := by omega
  rw [h4]
  exact zeroLf_four

end OMA.A235202Proof

/-- The conjecture fails at `m = 512`: `512` is in A126001 (`geZero 512`), but `512 ≠ 0` and `512 = 20000` in base 4
has digit `2` at a binary place, so it is no base-4 reading of an A235202 term. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a235202.main) := by
  intro h
  rcases (h 512).mp OMA.A235202Proof.geZero_512 with h0 | ⟨n, _, hn⟩
  · omega
  · exact OMA.A235202Proof.quat_ne_512 n hn
