import OMAStatements.S_oeis_a103627
import Mathlib

/-!
Credit: @ivillar
Proof: a(3k) = a(3k+2) = k and a(3k+1) = 1. Writing n = 3k + r, the angles (2n+1)*Pi/3 and
(8n+1)*Pi/6 reduce modulo 2*Pi to Pi/3, Pi/6 (r = 0), Pi, 3*Pi/2 (r = 1) and -Pi/3, 5*Pi/6
(r = 2), which gives the trigonometric formula (using sqrt(3)^2 = 3). Next,
a(m+3) = a(m) + [m mod 3 is not 1], which gives the recurrence (the denominator is (1-x^3)^2),
and with the first six terms the g.f.
-/

namespace OMAA103627Helpers
open PowerSeries OMA.S_oeis_a103627

theorem a0 (k : ℕ) : a (3 * k + 0) = k := by
  unfold a S
  rw [show (3 * k + 0) / 3 = k by omega, show (3 * k + 0) % 3 = 0 by omega]
  rfl

theorem a1 (k : ℕ) : a (3 * k + 1) = 1 := by
  unfold a S
  rw [show (3 * k + 1) / 3 = k by omega, show (3 * k + 1) % 3 = 1 by omega]
  rfl

theorem a2 (k : ℕ) : a (3 * k + 2) = k := by
  unfold a S
  rw [show (3 * k + 2) / 3 = k by omega, show (3 * k + 2) % 3 = 2 by omega]
  rfl

theorem trig (n : ℕ) :
    (a n : ℝ) = (2 * n + 1 + (2 * n - 8) * Real.cos ((2 * n + 1) * Real.pi / 3) +
        Real.sqrt 3 * Real.cos ((8 * n + 1) * Real.pi / 6) +
        Real.sqrt 3 * Real.sin ((2 * n + 1) * Real.pi / 3)) / 9 := by
  have s : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ n = 3 * k + r :=
    ⟨n / 3, n % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 3).symm⟩
  interval_cases r
  · have hA : (2 * ((3 * k + 0 : ℕ) : ℝ) + 1) * Real.pi / 3 =
        Real.pi / 3 + (k : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    have hB : (8 * ((3 * k + 0 : ℕ) : ℝ) + 1) * Real.pi / 6 =
        Real.pi / 6 + ((2 * k : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [hA, hB, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi,
      Real.sin_add_nat_mul_two_pi, Real.cos_pi_div_three, Real.cos_pi_div_six,
      Real.sin_pi_div_three, a0]
    push_cast
    linear_combination (-1 / 9 : ℝ) * s
  · have hA : (2 * ((3 * k + 1 : ℕ) : ℝ) + 1) * Real.pi / 3 =
        Real.pi + (k : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    have hB : (8 * ((3 * k + 1 : ℕ) : ℝ) + 1) * Real.pi / 6 =
        (Real.pi / 2 + Real.pi) + ((2 * k : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [hA, hB, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi,
      Real.sin_add_nat_mul_two_pi, Real.cos_pi, Real.cos_add_pi, Real.cos_pi_div_two,
      Real.sin_pi, a1]
    push_cast
    ring
  · have hA : (2 * ((3 * k + 2 : ℕ) : ℝ) + 1) * Real.pi / 3 =
        -(Real.pi / 3) + ((k + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    have hB : (8 * ((3 * k + 2 : ℕ) : ℝ) + 1) * Real.pi / 6 =
        (-(Real.pi / 6) + Real.pi) + ((2 * k + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    rw [hA, hB, Real.cos_add_nat_mul_two_pi, Real.cos_add_nat_mul_two_pi,
      Real.sin_add_nat_mul_two_pi, Real.cos_neg, Real.cos_add_pi, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_three, Real.cos_pi_div_six, Real.sin_pi_div_three, a2]
    push_cast
    linear_combination (1 / 9 : ℝ) * s

theorem astep (m : ℕ) : (a (m + 3) : ℤ) = a m + (if m % 3 = 1 then 0 else 1) := by
  unfold a S
  rw [show (m + 3) / 3 = m / 3 + 1 by omega, show (m + 3) % 3 = m % 3 by omega]
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h <;> simp [h]

theorem rec (m : ℕ) : (a (m + 6) : ℤ) = 2 * a (m + 3) - a m := by
  have h1 := astep (m + 3)
  have h2 := astep m
  rw [show m + 3 + 3 = m + 6 by ring, show (m + 3) % 3 = m % 3 by omega] at h1
  rw [h1, h2]
  ring

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

end OMAA103627Helpers

open PowerSeries OMAA103627Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a103627.main := by
  have hrec : ∀ n : ℕ, 5 < n → (OMA.S_oeis_a103627.a n : ℤ) =
      2 * OMA.S_oeis_a103627.a (n - 3) - OMA.S_oeis_a103627.a (n - 6) := by
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 3 = m + 3 by omega, show m + 6 - 6 = m by omega]
    exact rec m
  refine ⟨trig, ?_, hrec⟩
  set f : ℕ → ℤ := fun n => (OMA.S_oeis_a103627.a n : ℤ) with hfdef
  ext n
  have hD : ((1 - X) ^ 2 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℤ) =
      X ^ 0 - C 2 * X ^ 3 + X ^ 6 := by
    rw [map_ofNat C 2]; ring
  have hN : (X * (1 + X ^ 2 - X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      X ^ 1 + X ^ 3 - X ^ 4 + X ^ 5 := by
    ring
  rw [hD, hN]
  have v0 : f 0 = 0 := by simp only [hfdef]; decide
  have v1 : f 1 = 1 := by simp only [hfdef]; decide
  have v2 : f 2 = 0 := by simp only [hfdef]; decide
  have v3 : f 3 = 1 := by simp only [hfdef]; decide
  have v4 : f 4 = 1 := by simp only [hfdef]; decide
  have v5 : f 5 = 1 := by simp only [hfdef]; decide
  rcases Nat.lt_or_ge n 6 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow,
      coeff_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v1]
    · norm_num [v2]
    · norm_num [v0, v3]
    · norm_num [v1, v4]
    · norm_num [v2, v5]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at f (m + 6) 0 (m + 6) (by omega), coeff_at_C f 2 (m + 6) 3 (m + 3) (by omega),
      coeff_at f (m + 6) 6 m (by omega), coeff_X_pow, coeff_X_pow, coeff_X_pow, coeff_X_pow,
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hr := rec m
    simp only [hfdef]
    linear_combination hr
