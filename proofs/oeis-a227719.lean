import OMAStatements.S_oeis_a227719
import Mathlib

/-!
# A227719: a(n) = Floor(1/s(n)) = 3n^2 + (9n - 1) div 4

With y = 1/(2n+1), Mathlib gives log(1 + 1/n) = sum over k of 2 y^(2k+1)/(2k+1)
(`Real.hasSum_log_one_add_inv`). Three terms of that series bound the logarithm from below, and
two terms plus a geometric tail bound it from above. Put back into s(n), the two bounds give
(12n^2 + 9n - 1) s(n) ≤ 4 - (88n^3 + 196n^2 + 126n + 30)/(60 n (n+1) (2n+1)^3) ≤ 4 and
(12n^2 + 9n) s(n) ≥ 4 + (48n^3 + 56n^2 + 20n + 5)/(10 (2n+1)^5) > 4, so 4/s(n) lies in
[12n^2 + 9n - 1, 12n^2 + 9n), an interval of length 1 starting at an integer. Hence
a(n) = (12n^2 + 9n - 1) div 4 = 3n^2 + (9n - 1) div 4 for n ≥ 1 (a period-4 quasi-polynomial).
The recurrence follows from that closed form, and the g.f. follows from the recurrence and the
first six terms 5, 16, 33, 56, 86, 121.
-/

namespace OMA.P227719

open OMA.S_oeis_a227719 PowerSeries

/-- Lower bound for log(1 + 1/m): the first three terms of the series. -/
lemma log_lower (m : ℝ) (hm : 0 < m) :
    2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * m + 1)) ^ 3 + 2 / 5 * (1 / (2 * m + 1)) ^ 5
      ≤ Real.log (1 + m⁻¹) := by
  have h := Real.hasSum_log_one_add_inv hm
  have h2 := sum_le_hasSum (Finset.range 3) (fun i _ => by positivity) h
  have e : ∑ i ∈ Finset.range 3, 2 * (1 / (2 * (i : ℝ) + 1)) * (1 / (2 * m + 1)) ^ (2 * i + 1)
      = 2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * m + 1)) ^ 3
          + 2 / 5 * (1 / (2 * m + 1)) ^ 5 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  linarith

/-- Upper bound for log(1 + 1/m): two terms plus a geometric tail. -/
lemma log_upper (m : ℝ) (hm : 0 < m) :
    Real.log (1 + m⁻¹) ≤
      2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * (1 - (1 / (2 * m + 1)) ^ 2)⁻¹ := by
  have h := Real.hasSum_log_one_add_inv hm
  set y : ℝ := 1 / (2 * m + 1) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y < 1 := by
    rw [hy, div_lt_one (by positivity)]
    linarith
  have h' := (hasSum_nat_add_iff' 2).mpr h
  have hg : HasSum (fun k : ℕ => 2 / 5 * y ^ 5 * (y ^ 2) ^ k) (2 / 5 * y ^ 5 * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by nlinarith)).mul_left (2 / 5 * y ^ 5)
  have hle := hasSum_le (fun k => ?_) h' hg
  · simp [Finset.sum_range_succ] at hle
    norm_num at hle
    linarith
  · show 2 * (1 / (2 * ((k + 2 : ℕ) : ℝ) + 1)) * y ^ (2 * (k + 2) + 1) ≤ 2 / 5 * y ^ 5 * (y ^ 2) ^ k
    have e : y ^ (2 * (k + 2) + 1) = y ^ 5 * (y ^ 2) ^ k := by ring
    rw [e]
    have hk : (1 : ℝ) / (2 * ((k + 2 : ℕ) : ℝ) + 1) ≤ 1 / 5 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      push_cast
      have : (0 : ℝ) ≤ k := k.cast_nonneg
      linarith
    have hp : 0 ≤ y ^ 5 * (y ^ 2) ^ k := by positivity
    nlinarith

/-- For S = m log(1 + 1/m) - (2m-1)/(2m) and m ≥ 1: 12m^2 + 9m - 1 ≤ 4/S < 12m^2 + 9m. -/
lemma bounds (m : ℝ) (hm : 1 ≤ m) (S : ℝ)
    (hS : S = m * Real.log (1 + m⁻¹) - (2 * m - 1) / (2 * m)) :
    12 * m ^ 2 + 9 * m - 1 ≤ 4 * (1 / S) ∧ 4 * (1 / S) < 12 * m ^ 2 + 9 * m := by
  have hm0 : 0 < m := by linarith
  have hlo := log_lower m hm0
  have hhi := log_upper m hm0
  have ht : 0 < 2 * m + 1 := by linarith
  have hmne : m ≠ 0 := hm0.ne'
  have hm1ne : m + 1 ≠ 0 := by linarith
  have htne : 2 * m + 1 ≠ 0 := ht.ne'
  -- S is at most the value given by the upper bound on the logarithm
  have hA : (12 * m ^ 2 + 9 * m - 1) * S ≤ 4 := by
    have hq : 1 - (1 / (2 * m + 1)) ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 := by
      field_simp
      ring
    rw [hq, inv_div] at hhi
    have h1 : S ≤ m * (2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * ((2 * m + 1) ^ 2 / (4 * m * (m + 1))))
        - (2 * m - 1) / (2 * m) := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left hhi hm0.le
      linarith
    have h2 : (12 * m ^ 2 + 9 * m - 1) * (m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * ((2 * m + 1) ^ 2 / (4 * m * (m + 1))))
        - (2 * m - 1) / (2 * m))
        = 4 - (88 * m ^ 3 + 196 * m ^ 2 + 126 * m + 30)
          / (60 * m * (m + 1) * (2 * m + 1) ^ 3) := by
      field_simp
      ring
    have h3 : 0 ≤ (88 * m ^ 3 + 196 * m ^ 2 + 126 * m + 30)
        / (60 * m * (m + 1) * (2 * m + 1) ^ 3) := by positivity
    have hc : 0 ≤ 12 * m ^ 2 + 9 * m - 1 := by nlinarith
    calc (12 * m ^ 2 + 9 * m - 1) * S
        ≤ (12 * m ^ 2 + 9 * m - 1) * (m * (2 * (1 / (2 * m + 1))
          + 2 / 3 * (1 / (2 * m + 1)) ^ 3
          + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * ((2 * m + 1) ^ 2 / (4 * m * (m + 1))))
          - (2 * m - 1) / (2 * m)) := mul_le_mul_of_nonneg_left h1 hc
      _ = _ := h2
      _ ≤ 4 := by linarith
  -- S is at least the value given by the lower bound on the logarithm
  have hB : 4 < (12 * m ^ 2 + 9 * m) * S := by
    have h1 : m * (2 * (1 / (2 * m + 1)) + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5) - (2 * m - 1) / (2 * m) ≤ S := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left hlo hm0.le
      linarith
    have h2 : (12 * m ^ 2 + 9 * m) * (m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5) - (2 * m - 1) / (2 * m))
        = 4 + (48 * m ^ 3 + 56 * m ^ 2 + 20 * m + 5) / (10 * (2 * m + 1) ^ 5) := by
      field_simp
      ring
    have h3 : 0 < (48 * m ^ 3 + 56 * m ^ 2 + 20 * m + 5) / (10 * (2 * m + 1) ^ 5) := by
      positivity
    have hc : 0 ≤ 12 * m ^ 2 + 9 * m := by positivity
    calc (4 : ℝ) < 4 + (48 * m ^ 3 + 56 * m ^ 2 + 20 * m + 5) / (10 * (2 * m + 1) ^ 5) := by
          linarith
      _ = _ := h2.symm
      _ ≤ (12 * m ^ 2 + 9 * m) * S := mul_le_mul_of_nonneg_left h1 hc
  have hc : 0 < 12 * m ^ 2 + 9 * m := by positivity
  have hSpos : 0 < S := by
    by_contra hneg
    have hle : S ≤ 0 := not_lt.mp hneg
    nlinarith
  constructor
  · rw [mul_one_div, le_div_iff₀ hSpos]
    linarith
  · rw [mul_one_div, div_lt_iff₀ hSpos]
    linarith

/-- The closed form a(n) = 3n^2 + (9n - 1) div 4 for n ≥ 1. -/
lemma closed (n : ℕ) (hn : 1 ≤ n) : a n = 3 * (n : ℤ) ^ 2 + (9 * (n : ℤ) - 1) / 4 := by
  have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hs : s n = (n : ℝ) * Real.log (1 + (n : ℝ)⁻¹) - (2 * (n : ℝ) - 1) / (2 * (n : ℝ)) := by
    unfold s
    rw [one_div]
  obtain ⟨h1, h2⟩ := bounds (n : ℝ) hm1 (s n) hs
  have hk1 : 4 * ((9 * (n : ℤ) - 1) / 4) ≤ 9 * (n : ℤ) - 1 := by omega
  have hk2 : 9 * (n : ℤ) - 1 + 1 ≤ 4 * ((9 * (n : ℤ) - 1) / 4) + 4 := by omega
  have hk1' : (4 : ℝ) * (((9 * (n : ℤ) - 1) / 4 : ℤ) : ℝ) ≤ 9 * (n : ℝ) - 1 := by
    exact_mod_cast hk1
  have hk2' : 9 * (n : ℝ) - 1 + 1 ≤ 4 * (((9 * (n : ℤ) - 1) / 4 : ℤ) : ℝ) + 4 := by
    exact_mod_cast hk2
  unfold a
  rw [Int.floor_eq_iff]
  constructor
  · push_cast
    linarith
  · push_cast
    linarith

/-- The recurrence for n ≥ 7, from the closed form. -/
lemma recur (n : ℕ) (hn : 7 ≤ n) :
    a n = 2 * a (n - 1) - a (n - 2) + a (n - 4) - 2 * a (n - 5) + a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega,
    show k + 7 - 6 = k + 1 by omega, closed (k + 7) (by omega), closed (k + 6) (by omega),
    closed (k + 5) (by omega), closed (k + 3) (by omega), closed (k + 2) (by omega),
    closed (k + 1) (by omega)]
  push_cast
  have hq : (3 : ℤ) * ((k : ℤ) + 7) ^ 2 = 2 * (3 * ((k : ℤ) + 6) ^ 2) - 3 * ((k : ℤ) + 5) ^ 2
      + 3 * ((k : ℤ) + 3) ^ 2 - 2 * (3 * ((k : ℤ) + 2) ^ 2) + 3 * ((k : ℤ) + 1) ^ 2 := by ring
  have e1 : (9 * ((k : ℤ) + 7) - 1) / 4 = (9 * ((k : ℤ) + 3) - 1) / 4 + 9 := by
    rw [show 9 * ((k : ℤ) + 7) - 1 = 9 * ((k : ℤ) + 3) - 1 + 9 * 4 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num)]
  have e2 : (9 * ((k : ℤ) + 6) - 1) / 4 = (9 * ((k : ℤ) + 2) - 1) / 4 + 9 := by
    rw [show 9 * ((k : ℤ) + 6) - 1 = 9 * ((k : ℤ) + 2) - 1 + 9 * 4 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num)]
  have e3 : (9 * ((k : ℤ) + 5) - 1) / 4 = (9 * ((k : ℤ) + 1) - 1) / 4 + 9 := by
    rw [show 9 * ((k : ℤ) + 5) - 1 = 9 * ((k : ℤ) + 1) - 1 + 9 * 4 by ring,
      Int.add_mul_ediv_right _ _ (by norm_num)]
  linarith

/-- The numerator of the g.f., with its coefficients written as constants. -/
lemma rhs_eq : (-5 - 6 * X - 6 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4 + X ^ 5 : PowerSeries ℤ) =
    -(C 5) - C 6 * X ^ 1 - C 6 * X ^ 2 - C 6 * X ^ 3 - C 2 * X ^ 4 + C 1 * X ^ 5 := by
  simp

/-- A sequence with these six first terms and this recurrence has the stated g.f. -/
lemma gf_of (f : ℕ → ℤ) (h0 : f 0 = 5) (h1 : f 1 = 16) (h2 : f 2 = 33) (h3 : f 3 = 56)
    (h4 : f 4 = 86) (h5 : f 5 = 121)
    (hr : ∀ j : ℕ, f (j + 6) = 2 * f (j + 5) - f (j + 4) + f (j + 2) - 2 * f (j + 1) + f j) :
    PowerSeries.mk f * ((-1 + X) ^ 3 * (1 + X + X ^ 2 + X ^ 3) : PowerSeries ℤ) =
      -5 - 6 * X - 6 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4 + X ^ 5 := by
  have e : PowerSeries.mk f * ((-1 + X) ^ 3 * (1 + X + X ^ 2 + X ^ 3) : PowerSeries ℤ)
      = -PowerSeries.mk f + (PowerSeries.mk f * X ^ 1 + PowerSeries.mk f * X ^ 1)
        - PowerSeries.mk f * X ^ 2 + PowerSeries.mk f * X ^ 4
        - (PowerSeries.mk f * X ^ 5 + PowerSeries.mk f * X ^ 5) + PowerSeries.mk f * X ^ 6 := by
    ring
  rw [e, rhs_eq]
  ext m
  simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_mk, coeff_C]
  obtain hm | hm : m ≤ 5 ∨ 6 ≤ m := by omega
  · interval_cases m <;> simp [h0, h1, h2, h3, h4, h5]
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 6 := ⟨m - 6, by omega⟩
    have := hr j
    simp only [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega,
      show j + 6 - 4 = j + 2 by omega, show j + 6 - 5 = j + 1 by omega, show j + 6 - 6 = j by omega]
    simp
    linarith

theorem sol : type_of% @OMA.S_oeis_a227719.main := by
  refine ⟨recur, ?_⟩
  apply gf_of
  · rw [closed 1 le_rfl]; norm_num
  · rw [closed 2 (by norm_num)]; norm_num
  · rw [closed 3 (by norm_num)]; norm_num
  · rw [closed 4 (by norm_num)]; norm_num
  · rw [closed 5 (by norm_num)]; norm_num
  · rw [closed 6 (by norm_num)]; norm_num
  · intro j
    have := recur (j + 7) (by omega)
    simpa [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega] using this

end OMA.P227719

theorem OMA.solution : type_of% @OMA.S_oeis_a227719.main := OMA.P227719.sol

