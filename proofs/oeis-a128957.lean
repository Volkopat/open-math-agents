import OMAStatements.S_oeis_a128957
import Mathlib

/-!
Credit: @ivillar
Proof: the condition says that 10 ∤ m and 21 ∤ m, so by inclusion-exclusion
a(n) = 10^n - floor(10^n/10) - floor(10^n/21) + floor(10^n/210) (the formula in the OEIS entry).
Writing 10^k = 21*q(k) + r(k), this gives 21*a(k+1) = 180*10^k + r(k+1) - r(k), and r has period 6
because 10^6 = 1 (mod 21). The recurrence follows, and with the first six terms the g.f.
-/

namespace OMAA128957Helpers
open PowerSeries OMA.S_oeis_a128957

theorem count (N : ℕ) :
    (((Finset.Icc 1 N).filter
        (fun m => (¬ 2 ∣ m ∨ ¬ 5 ∣ m) ∧ (¬ 3 ∣ m ∨ ¬ 7 ∣ m))).card : ℤ) =
      ((N : ℕ) : ℤ) - ((N / 10 : ℕ) : ℤ) - ((N / 21 : ℕ) : ℤ) + ((N / 210 : ℕ) : ℤ) := by
  have hs : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hs]
  set s := Finset.Ioc 0 N
  have hp : s.filter (fun m => (¬ 2 ∣ m ∨ ¬ 5 ∣ m) ∧ (¬ 3 ∣ m ∨ ¬ 7 ∣ m)) =
      s.filter (fun m => ¬ (10 ∣ m ∨ 21 ∣ m)) :=
    Finset.filter_congr (fun m _ => by omega)
  have h210 : s.filter (fun m => 10 ∣ m ∧ 21 ∣ m) = s.filter (fun m => 210 ∣ m) :=
    Finset.filter_congr (fun m _ => by omega)
  have c10 : (s.filter (fun m => 10 ∣ m)).card = N / 10 := Nat.Ioc_filter_dvd_card_eq_div N 10
  have c21 : (s.filter (fun m => 21 ∣ m)).card = N / 21 := Nat.Ioc_filter_dvd_card_eq_div N 21
  have c210 : (s.filter (fun m => 210 ∣ m)).card = N / 210 :=
    Nat.Ioc_filter_dvd_card_eq_div N 210
  have cs : s.card = N := by simp [s]
  have hU : (s.filter (fun m => 10 ∣ m ∨ 21 ∣ m)).card + (s.filter (fun m => 210 ∣ m)).card =
      N / 10 + N / 21 := by
    rw [Finset.filter_or, ← h210, Finset.filter_and, Finset.card_union_add_card_inter, c10, c21]
  have hT : (s.filter (fun m => 10 ∣ m ∨ 21 ∣ m)).card +
      (s.filter (fun m => ¬ (10 ∣ m ∨ 21 ∣ m))).card = N := by
    rw [Finset.card_filter_add_card_filter_not, cs]
  rw [hp]
  omega

theorem r_period (k j : ℕ) (hj : j = k + 6) : 10 ^ j % 21 = 10 ^ k % 21 := by
  subst hj
  rw [pow_add, Nat.mul_mod]
  norm_num

theorem a_succ (k j : ℕ) (hj : j = k + 1) :
    21 * (a j : ℤ) = 180 * ((10 ^ k : ℕ) : ℤ) + ((10 ^ j % 21 : ℕ) : ℤ) - ((10 ^ k % 21 : ℕ) : ℤ) := by
  subst hj
  have h := count (10 ^ (k + 1))
  unfold a
  rw [h]
  have e10 : 10 ^ (k + 1) / 10 = 10 ^ k := by
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have e210 : 10 ^ (k + 1) / 210 = 10 ^ k / 21 := by
    rw [pow_succ, show (210 : ℕ) = 10 * 21 by norm_num, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [e10, e210]
  have d1 := Nat.div_add_mod (10 ^ (k + 1)) 21
  have d0 := Nat.div_add_mod (10 ^ k) 21
  have p : 10 ^ (k + 1) = 10 * 10 ^ k := by ring
  rw [p] at d1 ⊢
  omega

theorem rec (m : ℕ) :
    (a (m + 8) : ℤ) = 9 * a (m + 7) + 9 * a (m + 6) + 9 * a (m + 5) + 9 * a (m + 4) +
      9 * a (m + 3) + 10 * a (m + 2) := by
  have h8 := a_succ (m + 7) (m + 8) (by omega)
  have h7 := a_succ (m + 6) (m + 7) (by omega)
  have h6 := a_succ (m + 5) (m + 6) (by omega)
  have h5 := a_succ (m + 4) (m + 5) (by omega)
  have h4 := a_succ (m + 3) (m + 4) (by omega)
  have h3 := a_succ (m + 2) (m + 3) (by omega)
  have h2 := a_succ (m + 1) (m + 2) (by omega)
  have p8 := r_period (m + 2) (m + 8) (by omega)
  have p7 := r_period (m + 1) (m + 7) (by omega)
  have q7 : 10 ^ (m + 7) = 1000000 * 10 ^ (m + 1) := by ring
  have q6 : 10 ^ (m + 6) = 100000 * 10 ^ (m + 1) := by ring
  have q5 : 10 ^ (m + 5) = 10000 * 10 ^ (m + 1) := by ring
  have q4 : 10 ^ (m + 4) = 1000 * 10 ^ (m + 1) := by ring
  have q3 : 10 ^ (m + 3) = 100 * 10 ^ (m + 1) := by ring
  have q2 : 10 ^ (m + 2) = 10 * 10 ^ (m + 1) := by ring
  omega

def c (n : ℕ) : ℤ := if n < 2 then 0 else (a n : ℤ)

theorem coeff_mk_mul_X_pow (n k : ℕ) :
    coeff n (PowerSeries.mk c * X ^ k) = if k ≤ n then c (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * (if k ≤ n then c (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (n k j : ℕ) (h : n = j + k) : coeff n (PowerSeries.mk c * X ^ k) = c j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk c * (C r * X ^ k)) = r * c j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at n k j h]

theorem a_val (n : ℕ) : (a n : ℤ) =
    ((10 ^ n : ℕ) : ℤ) - ((10 ^ n / 10 : ℕ) : ℤ) - ((10 ^ n / 21 : ℕ) : ℤ) +
      ((10 ^ n / 210 : ℕ) : ℤ) := by
  unfold a
  exact count _

end OMAA128957Helpers

open PowerSeries OMAA128957Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a128957.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
    rw [show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
      show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
      show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega]
    exact rec m
  · change PowerSeries.mk c * _ = _
    ext n
    have hD : ((1 + X) * (1 - 10 * X) * (1 - X + X ^ 2) * (1 + X + X ^ 2) : PowerSeries ℤ) =
        X ^ 0 - C 9 * X ^ 1 - C 9 * X ^ 2 - C 9 * X ^ 3 - C 9 * X ^ 4 - C 9 * X ^ 5 -
          C 10 * X ^ 6 := by
      rw [map_ofNat C 9, map_ofNat C 10]; ring
    have hN : (X ^ 2 * (86 + 83 * X + 84 * X ^ 2 + 89 * X ^ 3 + 81 * X ^ 4 + 90 * X ^ 5) :
        PowerSeries ℤ) = C 86 * X ^ 2 + C 83 * X ^ 3 + C 84 * X ^ 4 + C 89 * X ^ 5 +
          C 81 * X ^ 6 + C 90 * X ^ 7 := by
      rw [map_ofNat C 86, map_ofNat C 83, map_ofNat C 84, map_ofNat C 89, map_ofNat C 81,
        map_ofNat C 90]
      ring
    rw [hD, hN]
    have v0 : c 0 = 0 := rfl
    have v1 : c 1 = 0 := rfl
    have v2 : c 2 = 86 := by rw [show c 2 = (OMA.S_oeis_a128957.a 2 : ℤ) from rfl, a_val]; norm_num
    have v3 : c 3 = 857 := by rw [show c 3 = (OMA.S_oeis_a128957.a 3 : ℤ) from rfl, a_val]; norm_num
    have v4 : c 4 = 8571 := by
      rw [show c 4 = (OMA.S_oeis_a128957.a 4 : ℤ) from rfl, a_val]; norm_num
    have v5 : c 5 = 85715 := by
      rw [show c 5 = (OMA.S_oeis_a128957.a 5 : ℤ) from rfl, a_val]; norm_num
    have v6 : c 6 = 857142 := by
      rw [show c 6 = (OMA.S_oeis_a128957.a 6 : ℤ) from rfl, a_val]; norm_num
    have v7 : c 7 = 8571429 := by
      rw [show c 7 = (OMA.S_oeis_a128957.a 7 : ℤ) from rfl, a_val]; norm_num
    rcases Nat.lt_or_ge n 8 with h | h
    · simp only [mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
        coeff_C_mul, coeff_X_pow]
      interval_cases n
      · norm_num [v0]
      · norm_num [v0, v1]
      · norm_num [v0, v1, v2]
      · norm_num [v0, v1, v2, v3]
      · norm_num [v0, v1, v2, v3, v4]
      · norm_num [v0, v1, v2, v3, v4, v5]
      · norm_num [v0, v1, v2, v3, v4, v5, v6]
      · norm_num [v1, v2, v3, v4, v5, v6, v7]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
      simp only [mul_sub, map_add, map_sub]
      rw [coeff_at (m + 8) 0 (m + 8) (by omega), coeff_at_C 9 (m + 8) 1 (m + 7) (by omega),
        coeff_at_C 9 (m + 8) 2 (m + 6) (by omega), coeff_at_C 9 (m + 8) 3 (m + 5) (by omega),
        coeff_at_C 9 (m + 8) 4 (m + 4) (by omega), coeff_at_C 9 (m + 8) 5 (m + 3) (by omega),
        coeff_at_C 10 (m + 8) 6 (m + 2) (by omega), coeff_C_mul, coeff_C_mul, coeff_C_mul,
        coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow,
        coeff_X_pow, coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      have hr := rec m
      simp only [c, show ¬ m + 8 < 2 by omega, show ¬ m + 7 < 2 by omega,
        show ¬ m + 6 < 2 by omega, show ¬ m + 5 < 2 by omega, show ¬ m + 4 < 2 by omega,
        show ¬ m + 3 < 2 by omega, show ¬ m + 2 < 2 by omega, ↓reduceIte]
      linear_combination hr
