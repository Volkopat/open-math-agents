import OMAStatements.S_oeis_a095121
import Mathlib

/-!
Credit: @ivillar
Proof: the g.f. gives a(0) = 1, a(1) = 2, a(2) = 6 and a(n) = 3a(n-1) - 2a(n-2), so
a(n) = 2^(n+1) - 2 for n >= 1. Write s(x) for the binary digit sum of x. Legendre's formula
v_2(x!) = x - s(x), together with (m+1) C(m) = binom(2m, m), binom(2m, m) m! m! = (2m)!,
(m+1)! = (m+1) m! and s(2m) = s(m), gives v_2(C(m)) + 1 = s(m+1). Since 2^s(x) <= x + 1 and
s(2^j - 1) = j, the least m > 0 with s(m+1) = n + 1 is 1 for n = 0 and 2^(n+1) - 2 for n >= 1.
-/

namespace OMAA095121Helpers
open PowerSeries OMA.S_oeis_a095121

theorem gf : PowerSeries.mk a * ((1 - X) * (1 - 2 * X) : PowerSeries ℤ) = 1 - X + 2 * X ^ 2 := by
  have h1 : PowerSeries.mk a = (1 - X + 2 * X ^ 2) * invOfUnit ((1 - X) * (1 - 2 * X)) 1 := by
    ext n
    rw [coeff_mk]
    rfl
  have h2 : ((1 - X) * (1 - 2 * X) : PowerSeries ℤ) * invOfUnit ((1 - X) * (1 - 2 * X)) 1 = 1 :=
    mul_invOfUnit _ _ (by simp)
  rw [h1, mul_assoc, mul_comm (invOfUnit _ _), h2, mul_one]

theorem coeff_mk_mul_X_pow (f : ℕ → ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℤ) (r : ℤ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℤ) (r : ℤ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

theorem rel (n : ℕ) : coeff n (PowerSeries.mk a * (X ^ 0 - C 3 * X ^ 1 + C 2 * X ^ 2)) =
    coeff n (X ^ 0 - X ^ 1 + C 2 * X ^ 2 : PowerSeries ℤ) := by
  have hD : ((1 - X) * (1 - 2 * X) : PowerSeries ℤ) = X ^ 0 - C 3 * X ^ 1 + C 2 * X ^ 2 := by
    rw [map_ofNat C 3, map_ofNat C 2]; ring
  have hN : (1 - X + 2 * X ^ 2 : PowerSeries ℤ) = X ^ 0 - X ^ 1 + C 2 * X ^ 2 := by
    rw [map_ofNat C 2]; ring
  rw [← hD, ← hN, gf]

theorem a0 : a 0 = 1 := by
  have h := rel 0
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
    coeff_C_mul, coeff_X_pow] at h
  norm_num at h
  linarith

theorem a1 : a 1 = 2 := by
  have h := rel 1
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
    coeff_C_mul, coeff_X_pow] at h
  norm_num at h
  linarith [a0]

theorem a2 : a 2 = 6 := by
  have h := rel 2
  simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
    coeff_C_mul, coeff_X_pow] at h
  norm_num at h
  linarith [a0, a1]

theorem arec (m : ℕ) : a (m + 3) = 3 * a (m + 2) - 2 * a (m + 1) := by
  have h := rel (m + 3)
  simp only [mul_add, mul_sub, map_add, map_sub] at h
  rw [coeff_at a (m + 3) 0 (m + 3) (by omega), coeff_at_C a 3 (m + 3) 1 (m + 2) (by omega),
    coeff_at_C a 2 (m + 3) 2 (m + 1) (by omega), coeff_C_mul, coeff_X_pow, coeff_X_pow,
    coeff_X_pow, if_neg (by omega), if_neg (by omega), if_neg (by omega)] at h
  linarith

theorem closed (n : ℕ) : a (n + 1) = 2 ^ (n + 2) - 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · norm_num [a1]
    · norm_num [a2]
    · have e1 := ih (n + 1) (by omega)
      have e0 := ih n (by omega)
      rw [show n + 1 + 1 = n + 2 by ring] at e1
      rw [show n + 1 + 1 + 1 = n + 3 by ring, arec, e1, e0]
      ring

theorem s_double (m : ℕ) : (Nat.digits 2 (2 * m)).sum = (Nat.digits 2 m).sum := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Nat.digits_def' (by norm_num) (by omega : 0 < 2 * m),
      show 2 * m % 2 = 0 by omega, show 2 * m / 2 = m by omega]
    simp

theorem s_succ_double (m : ℕ) : (Nat.digits 2 (2 * m + 1)).sum = (Nat.digits 2 m).sum + 1 := by
  rw [Nat.digits_def' (by norm_num) (by omega : 0 < 2 * m + 1),
    show (2 * m + 1) % 2 = 1 by omega, show (2 * m + 1) / 2 = m by omega]
  simp only [List.sum_cons]
  omega

theorem pow_s_le (x : ℕ) : 2 ^ (Nat.digits 2 x).sum ≤ x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    · obtain ⟨q, rfl | rfl⟩ : ∃ q, x = 2 * q ∨ x = 2 * q + 1 := ⟨x / 2, by omega⟩
      · rw [s_double]
        have := ih q (by omega)
        omega
      · rw [s_succ_double, pow_succ]
        have := ih q (by omega)
        omega

theorem s_mersenne (k : ℕ) : (Nat.digits 2 (2 ^ k - 1)).sum = k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [show 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 by rw [pow_succ]; omega, s_succ_double, ih]

theorem vcat (m : ℕ) : padicValNat 2 (catalan m) + 1 = (Nat.digits 2 (m + 1)).sum := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have L : ∀ n : ℕ, padicValNat 2 (Nat.factorial n) + (Nat.digits 2 n).sum = n := by
    intro n
    have h := sub_one_mul_padicValNat_factorial (p := 2) n
    have h2 := Nat.digit_sum_le 2 n
    simp only [show (2 : ℕ) - 1 = 1 from rfl, one_mul] at h
    omega
  have hc : (m + 1) * catalan m = Nat.centralBinom m := succ_mul_catalan_eq_centralBinom m
  have hcb : Nat.centralBinom m * Nat.factorial m * Nat.factorial m =
      Nat.factorial (2 * m) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have := Nat.choose_mul_factorial_mul_factorial (show m ≤ 2 * m by omega)
    rwa [show 2 * m - m = m by omega] at this
  have hcat : catalan m ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact Nat.centralBinom_ne_zero m hc.symm
  have v1 : padicValNat 2 (Nat.factorial (2 * m)) = padicValNat 2 (m + 1) +
      padicValNat 2 (catalan m) + padicValNat 2 (Nat.factorial m) +
        padicValNat 2 (Nat.factorial m) := by
    rw [← hcb, ← hc, padicValNat.mul, padicValNat.mul, padicValNat.mul]
    all_goals simp [hcat, Nat.factorial_ne_zero]
  have v2 : padicValNat 2 (Nat.factorial (m + 1)) =
      padicValNat 2 (m + 1) + padicValNat 2 (Nat.factorial m) := by
    rw [Nat.factorial_succ, padicValNat.mul]
    all_goals simp [Nat.factorial_ne_zero]
  have l1 := L (2 * m)
  have l2 := L m
  have l3 := L (m + 1)
  rw [s_double] at l1
  omega

end OMAA095121Helpers

open OMAA095121Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a095121.main := by
  intro n
  rcases n with _ | k
  · refine ⟨1, by simp [a0], ⟨by norm_num, ?_⟩, ?_⟩
    · simp
    · rintro x ⟨hx, -⟩
      exact hx
  · have hp : 4 ≤ 2 ^ (k + 2) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨2 ^ (k + 2) - 2, ?_, ⟨by omega, ?_⟩, ?_⟩
    · rw [closed, Nat.cast_sub (show 2 ≤ 2 ^ (k + 2) by omega)]
      simp
    · have h1 := vcat (2 ^ (k + 2) - 2)
      rw [show 2 ^ (k + 2) - 2 + 1 = 2 ^ (k + 2) - 1 by omega, s_mersenne] at h1
      omega
    · rintro x ⟨-, hv⟩
      have h1 := vcat x
      have h2 := pow_s_le (x + 1)
      rw [← h1, hv, show k + 1 + 1 = k + 2 by ring] at h2
      omega
