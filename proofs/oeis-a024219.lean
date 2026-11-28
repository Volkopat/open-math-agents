import OMAStatements.S_oeis_a024219
import Mathlib

namespace A024219
open OMA.S_oeis_a024219

lemma floor_val (n : ℕ) (hn : 1 ≤ n) (z : ℤ) (c : ℚ) (hc : c = 2 ∨ c = 4)
    (hz : 4 * (z : ℚ) = 3 * (n : ℚ) ^ 2 + n - c) : a n = z := by
  unfold a
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℚ) < 4 * (3 * (n : ℚ) + 2) := by positivity
  have hz' : (z : ℚ) = (3 * (n : ℚ) ^ 2 + n - c) / 4 := by linarith
  rw [Int.floor_eq_iff, le_div_iff₀ hpos, div_lt_iff₀ hpos, hz']
  rcases hc with rfl | rfl
  · constructor <;> nlinarith
  · constructor <;> nlinarith

def cc (n : ℕ) : ℤ := if n % 4 < 2 then 4 else 2

lemma cc_rec (m : ℕ) :
    cc (m + 6) - 3 * cc (m + 5) + 4 * cc (m + 4) - 4 * cc (m + 3) + 3 * cc (m + 2) -
      cc (m + 1) = 0 := by
  unfold cc
  split_ifs <;> omega

lemma four_a (n : ℕ) (hn : 1 ≤ n) : 4 * a n = 3 * (n : ℤ) ^ 2 + n - cc n := by
  unfold cc
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + n % 4 := ⟨n / 4, by omega⟩
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = r at hk hr
  interval_cases r
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + k - 1) 4 (Or.inr rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 7 * k) 4 (Or.inr rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 13 * k + 3) 2 (Or.inl rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring
  · have h := floor_val n hn (12 * (k : ℤ) ^ 2 + 19 * k + 7) 2 (Or.inl rfl)
      (by rw [hk]; push_cast; ring)
    rw [h, hk]
    push_cast
    ring

lemma rec_shift (m : ℕ) :
    a (m + 6) - 3 * a (m + 5) + 4 * a (m + 4) - 4 * a (m + 3) + 3 * a (m + 2) - a (m + 1) = 0 := by
  have h0 := four_a (m + 6) (by omega)
  have h1 := four_a (m + 5) (by omega)
  have h2 := four_a (m + 4) (by omega)
  have h3 := four_a (m + 3) (by omega)
  have h4 := four_a (m + 2) (by omega)
  have h5 := four_a (m + 1) (by omega)
  have hc := cc_rec m
  push_cast at h0 h1 h2 h3 h4 h5
  linarith

lemma a0 : a 0 = 0 := by
  unfold a
  norm_num

lemma a1 : a 1 = 0 := floor_val 1 (by norm_num) 0 4 (Or.inr rfl) (by norm_num)
lemma a2 : a 2 = 3 := floor_val 2 (by norm_num) 3 2 (Or.inl rfl) (by norm_num)
lemma a3 : a 3 = 7 := floor_val 3 (by norm_num) 7 2 (Or.inl rfl) (by norm_num)
lemma a4 : a 4 = 12 := floor_val 4 (by norm_num) 12 4 (Or.inr rfl) (by norm_num)
lemma a5 : a 5 = 19 := floor_val 5 (by norm_num) 19 4 (Or.inr rfl) (by norm_num)

end A024219

open PowerSeries OMA.S_oeis_a024219 A024219 in
theorem OMA.solution : type_of% @OMA.S_oeis_a024219.main := by
  have r (m : ℕ) : a (m + 6) = 3 * a (m + 5) - 4 * a (m + 4) + 4 * a (m + 3) - 3 * a (m + 2) + a (m + 1) := by
    linarith [rec_shift m]
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simpa using rec_shift m
  · simp only [F]
    ring_nf
    ext n
    rcases n with _ | _ | _ | _ | _ | _ | n <;> simp [coeff_mul_X_pow', coeff_X_pow, coeff_X, ← map_ofNat C, coeff_mul_C, coeff_succ_mul_X, coeff_X_pow_mul', coeff_succ_X_mul, coeff_C_mul, -eq_intCast, r, a0, a1, a2, a3, a4, a5] <;> ring
