import OMAStatements.S_oeis_a227721
import Mathlib

/-!
# A227721: a(n) = Floor(1/s(n)) = 2 + 9n + 6n^2

With t = 2n+1 and y = 1/t, Mathlib gives log(1 + 1/n) = sum over k of 2 y^(2k+1)/(2k+1)
(`Real.hasSum_log_one_add_inv`). Three terms of that series bound the logarithm from below, and
two terms plus a geometric tail bound it from above. Put back into s(n), the two bounds give
(6n^2+9n+2) s(n) ≤ 1 - (14t^4 - 6t^3 - 5t^2 - 9t + 6)/(30 t^5 (t+1)) ≤ 1 and
(6n^2+9n+3) s(n) ≥ 1 + 1/(5t^2) > 1, so 1/s(n) lies in [6n^2+9n+2, 6n^2+9n+3).
The recurrence then follows from the closed form.
-/

namespace OMA.P227721

open OMA.S_oeis_a227721

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

/-- The two-sided bound on 1/S, for S = (2m+1)/(2m+2) - m log(1 + 1/m) and m ≥ 1. -/
lemma bounds (m : ℝ) (hm : 1 ≤ m) (S : ℝ)
    (hS : S = (2 * m + 1) / (2 * m + 2) - m * Real.log (1 + m⁻¹)) :
    2 + 9 * m + 6 * m ^ 2 ≤ 1 / S ∧ 1 / S < 2 + 9 * m + 6 * m ^ 2 + 1 := by
  have hm0 : 0 < m := by linarith
  have hlo := log_lower m hm0
  have hhi := log_upper m hm0
  have ht : 0 < 2 * m + 1 := by linarith
  have hmne : m ≠ 0 := hm0.ne'
  have hm1ne : m + 1 ≠ 0 := by linarith
  have htne : 2 * m + 1 ≠ 0 := ht.ne'
  have ht2ne : 2 * m + 2 ≠ 0 := by linarith
  -- S is at most the value given by the lower bound on the logarithm
  have hA : (6 * m ^ 2 + 9 * m + 2) * S ≤ 1 := by
    have h1 : S ≤ (2 * m + 1) / (2 * m + 2) - m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3 + 2 / 5 * (1 / (2 * m + 1)) ^ 5) := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left hlo hm0.le
      linarith
    have h2 : (6 * m ^ 2 + 9 * m + 2) * ((2 * m + 1) / (2 * m + 2) - m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3 + 2 / 5 * (1 / (2 * m + 1)) ^ 5))
        = 1 - (14 * (2 * m + 1) ^ 4 - 6 * (2 * m + 1) ^ 3 - 5 * (2 * m + 1) ^ 2
            - 9 * (2 * m + 1) + 6) / (30 * (2 * m + 1) ^ 5 * (2 * m + 2)) := by
      field_simp
      ring
    have h3 : 0 ≤ (14 * (2 * m + 1) ^ 4 - 6 * (2 * m + 1) ^ 3 - 5 * (2 * m + 1) ^ 2
            - 9 * (2 * m + 1) + 6) / (30 * (2 * m + 1) ^ 5 * (2 * m + 2)) := by
      apply div_nonneg _ (by positivity)
      have h3' : 0 ≤ 2 * m + 1 - 3 := by linarith
      nlinarith [mul_nonneg (pow_nonneg ht.le 3) h3', mul_nonneg (pow_nonneg ht.le 2) h3',
        mul_nonneg ht.le h3']
    have hc : 0 ≤ 6 * m ^ 2 + 9 * m + 2 := by positivity
    calc (6 * m ^ 2 + 9 * m + 2) * S
        ≤ (6 * m ^ 2 + 9 * m + 2) * ((2 * m + 1) / (2 * m + 2) - m * (2 * (1 / (2 * m + 1))
          + 2 / 3 * (1 / (2 * m + 1)) ^ 3 + 2 / 5 * (1 / (2 * m + 1)) ^ 5)) :=
          mul_le_mul_of_nonneg_left h1 hc
      _ = _ := h2
      _ ≤ 1 := by linarith
  -- S is at least the value given by the upper bound on the logarithm
  have hB : 1 < (6 * m ^ 2 + 9 * m + 3) * S := by
    have hq : 1 - (1 / (2 * m + 1)) ^ 2 = 4 * m * (m + 1) / (2 * m + 1) ^ 2 := by
      field_simp
      ring
    rw [hq, inv_div] at hhi
    have h1 : (2 * m + 1) / (2 * m + 2) - m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * ((2 * m + 1) ^ 2 / (4 * m * (m + 1)))) ≤ S := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left hhi hm0.le
      linarith
    have h2 : (6 * m ^ 2 + 9 * m + 3) * ((2 * m + 1) / (2 * m + 2) - m * (2 * (1 / (2 * m + 1))
        + 2 / 3 * (1 / (2 * m + 1)) ^ 3
        + 2 / 5 * (1 / (2 * m + 1)) ^ 5 * ((2 * m + 1) ^ 2 / (4 * m * (m + 1)))))
        = 1 + 1 / (5 * (2 * m + 1) ^ 2) := by
      field_simp
      ring
    have h3 : 0 < 1 / (5 * (2 * m + 1) ^ 2) := by positivity
    have hc : 0 ≤ 6 * m ^ 2 + 9 * m + 3 := by positivity
    calc (1 : ℝ) < 1 + 1 / (5 * (2 * m + 1) ^ 2) := by linarith
      _ = _ := h2.symm
      _ ≤ (6 * m ^ 2 + 9 * m + 3) * S := mul_le_mul_of_nonneg_left h1 hc
  have hc3 : 0 < 6 * m ^ 2 + 9 * m + 3 := by positivity
  have hSpos : 0 < S := by
    by_contra hneg
    have hle : S ≤ 0 := not_lt.mp hneg
    nlinarith
  constructor
  · rw [le_div_iff₀ hSpos]
    linarith
  · rw [div_lt_iff₀ hSpos]
    linarith

/-- The closed form a(n) = 2 + 9n + 6n^2 for n ≥ 1. -/
lemma closed (n : ℕ) (hn : 1 ≤ n) : a n = 2 + 9 * (n : ℤ) + 6 * (n : ℤ) ^ 2 := by
  have hm1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ)) = Real.log (1 + (n : ℝ)⁻¹) := by
    congr 1
    field_simp
  have hs : s n = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
      - (n : ℝ) * Real.log (1 + (n : ℝ)⁻¹) := by
    unfold s
    rw [hlog]
  have hb := bounds (n : ℝ) hm1 (s n) hs
  unfold a
  rw [Int.floor_eq_iff]
  push_cast
  exact hb

theorem sol : type_of% @OMA.S_oeis_a227721.main := by
  refine ⟨closed, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [closed (k + 4) (by omega), show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, closed (k + 3) (by omega), closed (k + 2) (by omega),
    closed (k + 1) (by omega)]
  push_cast
  ring

end OMA.P227721

theorem OMA.solution : type_of% @OMA.S_oeis_a227721.main := OMA.P227721.sol

