import OMAStatements.S_oeis_a239907

-- Problem: A239907 (Kurkov's conjecture): the alternating run counts equal A329320.
-- Both sides equal the sum over bit positions i of the parity of the number of 1's starting at i
-- (= v_2(floor(n/2^i) + 1)), since the alternating sum of 1's up to r is r mod 2.
-- Credit: @bnb9001

namespace OMA_A239907_Proof

open Finset OMA.S_oeis_a239907

theorem low_ones (m k : ℕ) : (∀ j < k, m / 2 ^ j % 2 = 1) ↔ m % 2 ^ k = 2 ^ k - 1 := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [Nat.mod_pow_succ, pow_succ]
    have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
    have hc : m / 2 ^ k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    constructor
    · intro h
      have h1 := (ih.mp (fun j hj => h j (by omega)))
      have h2 := h k (by omega)
      rw [h1, h2]; omega
    · intro h j hj
      have hboth : m % 2 ^ k = 2 ^ k - 1 ∧ m / 2 ^ k % 2 = 1 := by
        rcases (show m / 2 ^ k % 2 = 0 ∨ m / 2 ^ k % 2 = 1 by omega) with hc0 | hc1
        · rw [hc0, mul_zero, add_zero] at h; omega
        · rw [hc1, mul_one] at h; exact ⟨by omega, hc1⟩
      rcases Nat.lt_or_ge j k with hjk | hjk
      · exact ih.mpr hboth.1 j hjk
      · rw [show j = k by omega]; exact hboth.2

theorem ones_iff (m k : ℕ) : (∀ j < k, m / 2 ^ j % 2 = 1) ↔ k ≤ padicValNat 2 (m + 1) := by
  rw [low_ones, ← padicValNat_dvd_iff_le (by omega), Nat.dvd_iff_mod_eq_zero, Nat.add_mod]
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hr : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (by positivity)
  rcases Nat.lt_or_ge (m % 2 ^ k + 1) (2 ^ k) with hlt | hge
  · have h1 : 1 % 2 ^ k + m % 2 ^ k = m % 2 ^ k + 1 % 2 ^ k := by ring
    rcases Nat.eq_or_lt_of_le hP with hP1 | hP1
    · -- 2^k = 1
      rw [← hP1]; simp
    · rw [Nat.mod_eq_of_lt (show 1 < 2 ^ k from hP1), Nat.mod_eq_of_lt hlt]; omega
  · have heq : m % 2 ^ k = 2 ^ k - 1 := by omega
    rcases Nat.eq_or_lt_of_le hP with hP1 | hP1
    · rw [← hP1]; simp
    · rw [Nat.mod_eq_of_lt (show 1 < 2 ^ k from hP1), heq, Nat.sub_add_cancel hP, Nat.mod_self]
      omega

theorem alt_sum (t : ℕ) : ∑ k ∈ Icc 1 t, ((-1 : ℤ) ^ (k + 1)) = (t % 2 : ℕ) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    rcases Nat.even_or_odd t with ⟨s, rfl⟩ | ⟨s, rfl⟩
    · rw [show (s + s + 1 + 1) = 2 * (s + 1) by ring, pow_mul]; norm_num; omega
    · rw [show (2 * s + 1 + 1 + 1) = 2 * (s + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
      push_cast; omega

theorem alt_trunc (r n : ℕ) (h : r ≤ n) :
    ∑ k ∈ Icc 1 n, ((-1 : ℤ) ^ (k + 1) * (if k ≤ r then 1 else 0)) = (r % 2 : ℕ) := by
  rw [← alt_sum r]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext k; simp only [mem_filter, mem_Icc]; omega

theorem v2_le (m n : ℕ) (hm : m ≤ n) : padicValNat 2 (m + 1) ≤ n := by
  have h1 : 2 ^ padicValNat 2 (m + 1) ∣ m + 1 := pow_padicValNat_dvd
  have h2 := Nat.le_of_dvd (by omega) h1
  have h3 : padicValNat 2 (m + 1) < 2 ^ padicValNat 2 (m + 1) := Nat.lt_two_pow_self
  omega

theorem F_eq (n : ℕ) : ∑ k ∈ Icc 1 n, (-1 : ℤ) ^ (k + 1) * (cn n k : ℤ) =
    ∑ i ∈ range n, ((padicValNat 2 (n / 2 ^ i + 1) % 2 : ℕ) : ℤ) := by
  unfold cn
  simp only [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n := mem_range.mp hi
  rw [← alt_trunc (padicValNat 2 (n / 2 ^ i + 1)) n (v2_le _ _ (Nat.div_le_self _ _))]
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  have key : (∀ j < k, n.testBit (i + j)) ↔ k ≤ padicValNat 2 (n / 2 ^ i + 1) := by
    rw [← ones_iff]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_iff, pow_add, Nat.div_div_eq_div_mul]
  by_cases hk2 : k ≤ padicValNat 2 (n / 2 ^ i + 1)
  · rw [if_pos (key.mpr hk2), if_pos hk2]; simp
  · rw [if_neg (fun h => hk2 (key.mp h)), if_neg hk2]; simp

theorem G_eq (n : ℕ) : A329320 n = ∑ k ∈ range (Nat.log 2 n + 1), (padicValNat 2 (n / 2 ^ k + 1) % 2) := by
  unfold A329320 A035263
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [add_comm 1]; omega

end OMA_A239907_Proof

open Finset OMA.S_oeis_a239907 OMA_A239907_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a239907.main := by
  intro n
  unfold a
  rw [F_eq, G_eq]
  congr 1
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · symm
    apply Finset.sum_subset
    · intro k hk
      simp only [mem_range] at hk ⊢
      have := Nat.log_lt_self 2 (show n ≠ 0 by omega)
      omega
    · intro k hk hk'
      simp only [mem_range, not_lt] at hk hk'
      have hlt : n < 2 ^ k := Nat.lt_pow_of_log_lt (by norm_num) (by omega)
      rw [Nat.div_eq_of_lt hlt]; simp
