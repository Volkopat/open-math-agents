import OMAStatements.S_oeis_a361034
import Mathlib

open OMA.S_oeis_a361034

namespace OMA.P_oeis_a361034

theorem T_aux (m c d n : ℕ) (hm : 0 < m) (hc : c ≤ m) (hd : 4 * c ≤ (d + 1) * m) :
    n / m + 3 * ((n + c) / m) ≤ 4 * n / m + d := by
  have hq : n / m * m ≤ n := Nat.div_mul_le_self n m
  have hk : (n + c) / m * m ≤ n + c := Nat.div_mul_le_self (n + c) m
  have hkq : (n + c) / m ≤ n / m + 1 := by
    calc (n + c) / m ≤ (n + m) / m := Nat.div_le_div_right (by omega)
      _ = n / m + 1 := Nat.add_div_right n hm
  have key : (n / m + 3 * ((n + c) / m)) * m ≤ 4 * n + d * m := by
    rcases Nat.lt_or_ge (n / m) ((n + c) / m) with h | h
    · have e : (n + c) / m = n / m + 1 := by omega
      rw [e] at hk ⊢
      nlinarith
    · have := Nat.mul_le_mul_right m h
      nlinarith
  have : n / m + 3 * ((n + c) / m) ≤ (4 * n + d * m) / m :=
    (Nat.le_div_iff_mul_le hm).mpr key
  rwa [Nat.add_mul_div_right _ _ hm] at this

theorem oddp (p c K n : ℕ) [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hc : c ≤ 2) (hK : K ≠ 0)
    (hd : 4 * c ≤ (padicValNat p K + 1) * p) :
    padicValNat p (n.factorial * (n + c).factorial ^ 3) ≤ padicValNat p (K * (4 * n).factorial) := by
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
    padicValNat.pow, padicValNat.mul hK (Nat.factorial_ne_zero _)]
  have hb : ∀ x, x ≤ 4 * n + c → Nat.log p x < Nat.log p (4 * n + c) + 2 := fun x hx =>
    (Nat.log_mono_right hx).trans_lt (by omega)
  rw [padicValNat_factorial (hb n (by omega)), padicValNat_factorial (hb (n + c) (by omega)),
    padicValNat_factorial (hb (4 * n) (by omega))]
  have hb1 : 1 < Nat.log p (4 * n + c) + 2 := by omega
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_eq_sum_Ico_succ_bot (a := 1) hb1,
    Finset.sum_eq_sum_Ico_succ_bot (a := 1) hb1]
  have h1 := T_aux (p ^ 1) c (padicValNat p K) n (by positivity) (by simp; omega) (by simpa using hd)
  have hs : ∑ i ∈ Finset.Ico (1 + 1) (Nat.log p (4 * n + c) + 2), (n / p ^ i + 3 * ((n + c) / p ^ i))
      ≤ ∑ i ∈ Finset.Ico (1 + 1) (Nat.log p (4 * n + c) + 2), 4 * n / p ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi2 : 2 ≤ i := (Finset.mem_Ico.mp hi).1
    have h9 : 9 ≤ p ^ i := by
      calc 9 ≤ p ^ 2 := by nlinarith
        _ ≤ p ^ i := Nat.pow_le_pow_right (by omega) hi2
    have := T_aux (p ^ i) c 0 n (by omega) (by omega) (by omega)
    simpa using this
  linarith

theorem v2_four (n : ℕ) : padicValNat 2 (4 * n).factorial = padicValNat 2 n.factorial + 3 * n := by
  have := Fact.mk Nat.prime_two
  rw [show 4 * n = 2 * (2 * n) by ring, padicValNat_factorial_mul, padicValNat_factorial_mul]
  ring

theorem pow2 : ∀ m, 0 < m → (padicValNat 2 m.factorial + 1 = m ↔ ∃ k, m = 2 ^ k) := by
  have := Fact.mk Nat.prime_two
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    obtain ⟨q, rfl | rfl⟩ : ∃ q, m = 2 * q ∨ m = 2 * q + 1 := ⟨m / 2, by omega⟩
    · rw [padicValNat_factorial_mul]
      have hq : 0 < q := by omega
      have := ih q (by omega) hq
      constructor
      · intro h
        obtain ⟨k, hk⟩ := this.mp (by omega)
        exact ⟨k + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · have : 2 * q = 1 := by simp at hk
          omega
        · have : q = 2 ^ k := by rw [pow_succ] at hk; omega
          have := (ih q (by omega) hq).mpr ⟨k, this⟩
          omega
    · rw [padicValNat_factorial_mul_add q (by norm_num), padicValNat_factorial_mul]
      constructor
      · intro h
        have : q = 0 := by
          by_contra hq
          have := padicValNat_factorial_lt_of_ne_zero 2 hq
          omega
        exact ⟨0, by simp [this]⟩
      · rintro ⟨k, hk⟩
        rcases k with _ | k
        · have : q = 0 := by simp at hk; omega
          subst this; simp
        · rw [pow_succ] at hk; omega

theorem gen (c K n : ℕ) (hc : c ≤ 2) (hK : K ≠ 0) (hc1 : 1 ≤ c)
    (hodd : ∀ p, p.Prime → 3 ≤ p → 4 * c ≤ (padicValNat p K + 1) * p)
    (h2 : padicValNat 2 K + 3 = 3 * c) :
    (n.factorial * (n + c).factorial ^ 3 ∣ K * (4 * n).factorial) ∧
    (Odd (K * (4 * n).factorial / (n.factorial * (n + c).factorial ^ 3)) ↔
      padicValNat 2 (n + c).factorial + 1 = n + c) := by
  have hy : n.factorial * (n + c).factorial ^ 3 ≠ 0 := by positivity
  have hx : K * (4 * n).factorial ≠ 0 := by positivity
  have := Fact.mk Nat.prime_two
  have V := padicValNat_factorial_lt_of_ne_zero 2 (show n + c ≠ 0 by omega)
  have ex : padicValNat 2 (K * (4 * n).factorial) = padicValNat 2 K + padicValNat 2 n.factorial + 3 * n := by
    rw [padicValNat.mul hK (Nat.factorial_ne_zero _), v2_four]; ring
  have ey : padicValNat 2 (n.factorial * (n + c).factorial ^ 3) = padicValNat 2 n.factorial + 3 * padicValNat 2 (n + c).factorial := by
    rw [padicValNat.mul (Nat.factorial_ne_zero _) (pow_ne_zero _ (Nat.factorial_ne_zero _)),
      padicValNat.pow]
  have hdvd : n.factorial * (n + c).factorial ^ 3 ∣ K * (4 * n).factorial := by
    rw [← Nat.factorization_prime_le_iff_dvd hy hx]
    intro p hp
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
    have := Fact.mk hp
    rcases (show p = 2 ∨ 3 ≤ p by have := hp.two_le; omega) with rfl | h3
    · rw [ex, ey]; omega
    · exact oddp p c K n h3 hc hK (hodd p hp h3)
  refine ⟨hdvd, ?_⟩
  obtain ⟨a, ha⟩ := hdvd
  have ha0 : a ≠ 0 := by rintro rfl; rw [mul_zero] at ha; exact hx ha
  rw [ha, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hy)]
  have e := congrArg (padicValNat 2) ha
  rw [padicValNat.mul hy ha0, ex, ey] at e
  have : Odd a ↔ padicValNat 2 a = 0 := by
    rw [padicValNat.eq_zero_iff, Nat.odd_iff]; omega
  rw [this]
  omega
end OMA.P_oeis_a361034

open OMA.P_oeis_a361034

theorem OMA.solution : type_of% @OMA.S_oeis_a361034.main := by
  intro n
  have := Fact.mk Nat.prime_two
  have h2 : padicValNat 2 2520 = 3 := by
    rw [show (2520 : ℕ) = 2 ^ 3 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  have hodd : ∀ p, p.Prime → 3 ≤ p → 4 * 2 ≤ (padicValNat p 2520 + 1) * p := by
    intro p hp hp3
    have := Fact.mk hp
    have hz := Nat.zero_le (padicValNat p 2520)
    rcases (show p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ 8 ≤ p by omega) with
      rfl | rfl | rfl | rfl | rfl | h
    · have : 2 ≤ padicValNat 3 2520 := (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      omega
    · exact absurd hp (by norm_num)
    · have : 1 ≤ padicValNat 5 2520 := (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      omega
    · exact absurd hp (by norm_num)
    · have : 1 ≤ padicValNat 7 2520 := (padicValNat_dvd_iff_le (by norm_num)).mp (by norm_num)
      omega
    · nlinarith
  rw [a, (gen 2 2520 n le_rfl (by norm_num) (by norm_num) hodd (by rw [h2])).2,
    pow2 (n + 2) (by omega)]
  constructor
  · rintro ⟨k, hk⟩
    rcases k with _ | k
    · simp at hk
    · exact ⟨k + 1, by omega, by omega⟩
  · rintro ⟨k, hk1, hk⟩
    refine ⟨k, ?_⟩
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk1
    omega
