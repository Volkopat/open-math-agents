import OMAStatements.S_oeis_a249067
import Mathlib

/-!
# A249067: every a(n) is at most 81

Let 10^e ≤ n < 10^(e+1) and T = 10^(e+1). For each digit d a multiple j * n with j ≤ 81 has
first digit d:
* d = 0: j = 0.
* 1 ≤ d ≤ 8, or d = 9 with T ≤ 9 n: j = ceil(d T / n). Then d T ≤ j n < d T + n < (d+1) T, and
  j ≤ 81 because d T ≤ 81 n (for d ≤ 8, d T ≤ 80 * 10^e ≤ 80 n).
* d = 9 with 9 n < T: j = 9, since 9 * 10^e ≤ 9 n < 10 * 10^e.
So k = 81 covers every n ≥ 1, which gives both parts of the statement with N = 81.
The first digit is computed as m / 10 ^ Nat.log 10 m (lemma firstDigit_eq).
-/

namespace OMA.P249067

open OMA.S_oeis_a249067

/-- Dropping the last decimal digit keeps the first digit. -/
lemma firstDigit_div_ten {m : ℕ} (hm : 10 ≤ m) : firstDigit m = firstDigit (m / 10) := by
  have hpos : 0 < m := by omega
  have hne : Nat.digits 10 (m / 10) ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
  obtain ⟨b, l, hbl⟩ := List.exists_cons_of_ne_nil hne
  unfold firstDigit
  rw [Nat.digits_def' (by norm_num) hpos, hbl]
  simp only [List.getLastD_cons]

/-- The first digit of m is m / 10 ^ Nat.log 10 m. -/
lemma firstDigit_eq (m : ℕ) : firstDigit m = m / 10 ^ Nat.log 10 m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rcases Nat.lt_or_ge m 10 with h10 | h10
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [firstDigit]
      · rw [firstDigit, Nat.digits_of_lt 10 m (by omega) h10, Nat.log_of_lt h10]
        simp
    · have hlog : Nat.log 10 m = Nat.log 10 (m / 10) + 1 := by
        rw [Nat.log_div_base]
        have : 0 < Nat.log 10 m := Nat.log_pos (by norm_num) h10
        omega
      rw [firstDigit_div_ten h10, ih (m / 10) (by omega), hlog, pow_succ',
        Nat.div_div_eq_div_mul]

/-- A first digit is at most 9. -/
lemma firstDigit_lt (m : ℕ) : firstDigit m < 10 := by
  rw [firstDigit_eq, Nat.div_lt_iff_lt_mul (by positivity)]
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) m
  rw [Nat.pow_succ] at this
  linarith

/-- A number between d * 10^e and (d+1) * 10^e (d a nonzero digit) has first digit d. -/
lemma firstDigit_of_bounds {d e x : ℕ} (hd1 : 1 ≤ d) (hd9 : d ≤ 9)
    (hlo : d * 10 ^ e ≤ x) (hhi : x < (d + 1) * 10 ^ e) : firstDigit x = d := by
  have hlog : Nat.log 10 x = e := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · calc 10 ^ e = 1 * 10 ^ e := (one_mul _).symm
        _ ≤ d * 10 ^ e := Nat.mul_le_mul_right _ hd1
        _ ≤ x := hlo
    · calc x < (d + 1) * 10 ^ e := hhi
        _ ≤ 10 * 10 ^ e := Nat.mul_le_mul_right _ (by omega)
        _ = 10 ^ (e + 1) := (pow_succ' 10 e).symm
  rw [firstDigit_eq, hlog]
  exact Nat.div_eq_of_lt_le hlo hhi

/-- Every digit d ≤ 9 is the first digit of j * n for some j ≤ 81. -/
lemma exists_mult {n d : ℕ} (hn : 1 ≤ n) (hd : d ≤ 9) :
    ∃ j, j ≤ 81 ∧ firstDigit (j * n) = d := by
  set e := Nat.log 10 n with he
  have hP : 10 ^ e ≤ n := Nat.pow_log_le_self 10 (by omega)
  have hT : n < 10 * 10 ^ e := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 10) n
    rw [Nat.pow_succ] at this
    linarith
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact ⟨0, by norm_num, by simp [firstDigit]⟩
  · by_cases h9 : d = 9 ∧ 9 * n < 10 * 10 ^ e
    · obtain ⟨rfl, h9n⟩ := h9
      refine ⟨9, by norm_num, ?_⟩
      apply firstDigit_of_bounds (e := e) (by norm_num) (by norm_num)
      · omega
      · omega
    · set T := 10 * 10 ^ e with hTdef
      have hD : d * T ≤ 81 * n := by
        rcases Nat.lt_or_ge d 9 with hlt | hge
        · calc d * T ≤ 8 * T := Nat.mul_le_mul_right _ (by omega)
            _ = 80 * 10 ^ e := by rw [hTdef]; ring
            _ ≤ 80 * n := Nat.mul_le_mul_left _ hP
            _ ≤ 81 * n := Nat.mul_le_mul_right _ (by norm_num)
        · have hd9' : d = 9 := by omega
          subst hd9'
          have : T ≤ 9 * n := by
            by_contra hc
            exact h9 ⟨rfl, not_le.mp hc⟩
          omega
      have hdm := Nat.div_add_mod (d * T + n - 1) n
      have hmod := Nat.mod_lt (d * T + n - 1) (show n > 0 by omega)
      refine ⟨(d * T + n - 1) / n, ?_, ?_⟩
      · have : (d * T + n - 1) / n < 82 := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        omega
      · set j := (d * T + n - 1) / n with hj
        apply firstDigit_of_bounds (e := e + 1) hd0 hd
        · rw [pow_succ', ← hTdef, mul_comm j n]
          omega
        · rw [pow_succ', ← hTdef, mul_comm j n, add_mul, one_mul]
          omega

/-- For n ≥ 1 the first digits of 0, n, 2n, ..., 81n are all of 0, 1, ..., 9. -/
lemma covers_81 {n : ℕ} (hn : 1 ≤ n) : covers n 81 := by
  unfold covers
  ext d
  simp only [Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j, _, rfl⟩
    exact ⟨Nat.zero_le _, by have := firstDigit_lt (j * n); omega⟩
  · rintro ⟨_, hd⟩
    obtain ⟨j, hj, hjd⟩ := exists_mult hn hd
    exact ⟨j, ⟨Nat.zero_le _, hj⟩, hjd⟩

theorem sol : type_of% @OMA.S_oeis_a249067.main := by
  have key : ∀ n : ℕ, 1 ≤ n → (∃ k, covers n k) ∧ a n ≤ 81 := fun n hn =>
    ⟨⟨81, covers_81 hn⟩, Nat.sInf_le (covers_81 hn)⟩
  exact ⟨⟨81, key⟩, key⟩

end OMA.P249067

theorem OMA.solution : type_of% @OMA.S_oeis_a249067.main := OMA.P249067.sol

