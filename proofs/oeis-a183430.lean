import OMAStatements.S_oeis_a183430
import Mathlib

open OMA.S_oeis_a183430

namespace OMA.P_oeis_a183430

open Finset

theorem ind_sum (t c : ZMod 4) : ∑ x : ZMod 4, (if t - x = c then (1 : ℤ) else 0) = 1 := by
  have h : ∀ x : ZMod 4, (t - x = c) ↔ (t - c = x) := by
    intro x; constructor <;> intro h <;> [rw [← h]; rw [← h]] <;> ring
  simp_rw [h]
  simp

theorem colf (n : ℕ) : ∀ f t : ZMod 4, 4 * column n f t =
    3 ^ n - (-1) ^ n + 4 * (-1) ^ n * (if t = (n : ZMod 4) * f then 1 else 0) := by
  induction n with
  | zero =>
    intro f t
    simp only [column, pow_zero, Nat.cast_zero, zero_mul]
    split_ifs <;> norm_num
  | succ n ih =>
    intro f t
    simp only [column]
    rw [Finset.mul_sum]
    simp_rw [ih]
    rw [Finset.sum_erase_eq_sub (mem_univ f)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card]
    rw [← Finset.mul_sum, ind_sum]
    have e : (t - f = (n : ZMod 4) * f) ↔ (t = ((n + 1 : ℕ) : ZMod 4) * f) := by
      push_cast
      constructor <;> intro h
      · rw [sub_eq_iff_eq_add] at h; rw [h]; ring
      · rw [h]; ring
    by_cases h1 : t = ((n + 1 : ℕ) : ZMod 4) * f
    · rw [if_pos (e.mpr h1), if_pos h1]; ring
    · rw [if_neg (fun h => h1 (e.mp h)), if_neg h1]; ring

theorem B4 (n : ℕ) : ∃ b : ℤ, 4 * b = 3 ^ n - (-1) ^ n := by
  have : (4 : ℤ) ∣ 3 ^ n - (-1) ^ n := by
    have := sub_dvd_pow_sub_pow (3 : ℤ) (-1) n
    simpa using this
  obtain ⟨b, hb⟩ := this
  exact ⟨b, hb.symm⟩

theorem col_eq (n : ℕ) (b : ℤ) (hb : 4 * b = 3 ^ n - (-1) ^ n) (f t : ZMod 4) :
    column n f t = b + (-1) ^ n * (if t = (n : ZMod 4) * f then 1 else 0) := by
  have h := colf n f t
  rw [← hb] at h
  linarith

theorem total_eq (n : ℕ) (b : ℤ) (hb : 4 * b = 3 ^ n - (-1) ^ n) :
    total n = 16 * b ^ 2 + 8 * (-1) ^ n * b + (if n % 2 = 0 then 1 else 4) := by
  unfold total
  simp_rw [col_eq n b hb]
  have hs : ((-1 : ℤ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have hm : (n : ZMod 4) = ((n % 4 : ℕ) : ZMod 4) := by
    rw [ZMod.natCast_mod]
  rw [hm]
  have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hpar : n % 2 = (n % 4) % 2 := by omega
  rw [hpar]
  generalize n % 4 = r at h4 ⊢
  generalize ((-1 : ℤ) ^ n) = s at hs ⊢
  have hu : (univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by decide
  rw [hu]
  interval_cases r <;>
    simp (disch := decide) only [Finset.sum_insert, Finset.mem_insert,
      Finset.mem_singleton, Finset.sum_singleton, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat,
      zero_mul, one_mul, neg_zero, if_true, if_false, Nat.zero_mod, Nat.one_mod, if_pos, if_neg] <;>
    norm_num <;>
    first | linear_combination hs | linear_combination 4 * hs

theorem tot (n : ℕ) : total n = 9 ^ n + (if n % 2 = 0 then 0 else 3) := by
  obtain ⟨b, hb⟩ := B4 n
  rw [total_eq n b hb]
  have hs : ((-1 : ℤ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
  have h9 : (9 : ℤ) ^ n = (4 * b + (-1) ^ n) ^ 2 := by
    rw [hb, show (3 : ℤ) ^ n - (-1) ^ n + (-1) ^ n = 3 ^ n by ring, ← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [h9]
  split_ifs <;> linear_combination (-1 : ℤ) * hs

theorem tt (n : ℕ) (hn : 0 < n) : tripleTerm n = 9 ^ n + (if n % 2 = 0 then 0 else 3) := by
  unfold tripleTerm; rw [if_neg (by omega), tot]

end OMA.P_oeis_a183430

open OMA.P_oeis_a183430 in
theorem OMA.solution : type_of% @OMA.S_oeis_a183430.main := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [tt _ (by omega), if_pos (by omega), add_zero]
  · intro k
    rw [tt _ (by omega), if_neg (by omega)]
  · intro n
    rcases Nat.lt_or_ge n 4 with h | h
    · interval_cases n
      · simp [tripleTerm, delayed]
      · simp only [delayed, show ¬ (2 ≤ 1) by omega, show ¬ (3 ≤ 1) by omega, if_false, le_refl,
          if_true, Nat.sub_self, tt 1 (by norm_num)]
        simp [tripleTerm]
      · simp only [delayed, show 1 ≤ 2 by omega, show 2 ≤ 2 by omega, show ¬ (3 ≤ 2) by omega,
          if_false, if_true, Nat.sub_self, show 2 - 1 = 1 by rfl, tt 1 (by norm_num), tt 2 (by norm_num)]
        simp [tripleTerm]
      · simp only [delayed, show 1 ≤ 3 by omega, show 2 ≤ 3 by omega, show 3 ≤ 3 by omega,
          if_true, Nat.sub_self, show 3 - 1 = 2 by rfl, show 3 - 2 = 1 by rfl, tt 1 (by norm_num),
          tt 2 (by norm_num), tt 3 (by norm_num)]
        simp [tripleTerm]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp only [delayed, show 1 ≤ k + 4 by omega, show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega,
        if_true, show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, tt (k + 4) (by omega), tt (k + 3) (by omega),
        tt (k + 2) (by omega), tt (k + 1) (by omega), show k + 4 ≠ 1 by omega,
        show k + 4 ≠ 2 by omega, show k + 4 ≠ 3 by omega, if_false]
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        ring
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
        ring
