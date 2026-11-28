import OMAStatements.S_oeis_a055272

-- Problem: A055272, the period of 1/7^n is 6*7^(n-1): order of 10 mod 7^n via LTE.
-- Credit: @bnb9001

namespace OMA_A055272_Proof

open OMA.S_oeis_a055272

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem v7_base : padicValNat 7 (10 ^ 6 - 1) = 1 := by
  rw [show (10 : ℕ) ^ 6 - 1 = 7 * 142857 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
    padicValNat.self (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]

theorem v7_pow (t : ℕ) (ht : t ≠ 0) :
    padicValNat 7 (10 ^ (6 * t) - 1) = 1 + padicValNat 7 t := by
  have h := padicValNat.pow_sub_pow (p := 7) (x := 10 ^ 6) (y := 1) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ht
  rw [one_pow, ← pow_mul] at h
  rw [h, v7_base]

theorem pow_eq_one_iff (n k : ℕ) :
    (10 : ZMod (7 ^ n)) ^ k = 1 ↔ 7 ^ n ∣ 10 ^ k - 1 := by
  have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [← Nat.modEq_iff_dvd' h1, ← ZMod.natCast_eq_natCast_iff]
  push_cast
  exact eq_comm

theorem dvd_iff_le (n k : ℕ) (hk : k ≠ 0) :
    7 ^ n ∣ 10 ^ (6 * k) - 1 ↔ n ≤ 1 + padicValNat 7 k := by
  have hne : 10 ^ (6 * k) - 1 ≠ 0 := by
    have : 10 ≤ 10 ^ (6 * k) := Nat.le_self_pow (by omega) 10
    omega
  rw [padicValNat_dvd_iff_le hne, v7_pow k hk]

theorem order_mod7 : orderOf (10 : ZMod 7) = 6 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

end OMA_A055272_Proof

open OMA.S_oeis_a055272 OMA_A055272_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a055272.main := by
  intro n hn
  have ha : a n = 6 * 7 ^ (n - 1) := by
    unfold a
    rw [if_neg (by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    omega
  rw [ha]
  unfold period
  set o := orderOf (10 : ZMod (7 ^ n)) with ho
  -- o divides 6 * 7^(n-1)
  have hdvd : o ∣ 6 * 7 ^ (n - 1) := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_eq_one_iff, dvd_iff_le _ _ (by positivity), padicValNat.prime_pow]
    omega
  -- 6 divides o
  have h6 : 6 ∣ o := by
    have hmap := orderOf_map_dvd
      (ZMod.castHom (dvd_pow_self 7 (by omega : n ≠ 0)) (ZMod 7)).toMonoidHom (10 : ZMod (7 ^ n))
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hmap
    rw [map_ofNat, order_mod7] at hmap
    exact hmap
  obtain ⟨q, hq⟩ := h6
  have hq7 : q ∣ 7 ^ (n - 1) := by
    rw [hq] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow (by norm_num)).mp hq7
  -- j = n - 1
  have hpow : (10 : ZMod (7 ^ n)) ^ (6 * 7 ^ j) = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  rw [pow_eq_one_iff, dvd_iff_le _ _ (by positivity), padicValNat.prime_pow] at hpow
  rw [hq, show j = n - 1 by omega]
