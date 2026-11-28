import OMAStatements.S_oeis_a373162

-- Problem: A373162: a(n) = denominator of Sum_{k>=0} cos(2k*Pi/3)/n^k.
-- Upstream: formal-conjectures statements/oeis-a373162.lean:0 (declaration OMA.S_oeis_a373162.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: cos(2k*Pi/3) has period 3 in k, with values 1, -1/2, -1/2, so splitting off the first
-- three terms of the series gives x(n) = (1 - 1/(2n) - 1/(2n^2)) + x(n)/n^3 for n >= 2, that is
-- 1 - x(n) = (n+2)/(2(n^2+n+1)). First reading: x(2) = 5/7 < x(3) = 21/26, so the case j = 1,
-- n = 2 fails. Second reading: by Mathlib's binomial formula for iterated forward differences,
-- (Delta^40 (1 - x))(2) = Sum_{k=0..40} (-1)^(40-k) C(40,k) (k+4)/(2((k+2)^2+(k+2)+1)), an
-- explicit rational number, about -6.0e-7, so the case j = 40, n = 2 fails.

namespace K11A373162

open OMA.S_oeis_a373162

theorem cos3 (k : ℕ) :
    Real.cos (2 * ((k + 3 : ℕ) : ℝ) * Real.pi / 3) = Real.cos (2 * (k : ℝ) * Real.pi / 3) := by
  have e : 2 * ((k + 3 : ℕ) : ℝ) * Real.pi / 3 = 2 * (k : ℝ) * Real.pi / 3 + 2 * Real.pi := by
    push_cast
    ring
  rw [e]
  exact Real.cos_add_two_pi _

theorem x_rec (n : ℕ) (hn : 2 ≤ n) :
    x n = (1 - 1 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ) ^ 2)) + x n / (n : ℝ) ^ 3 := by
  have hr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : (0 : ℝ) < n := by linarith
  have hsum : Summable (fun k : ℕ => Real.cos (2 * (k : ℝ) * Real.pi / 3) / (n : ℝ) ^ k) := by
    refine Summable.of_norm_bounded (g := fun k : ℕ => (1 / (n : ℝ)) ^ k)
      (summable_geometric_of_lt_one (by positivity) ?_) ?_
    · rw [div_lt_one hr0]
      linarith
    · intro k
      show ‖Real.cos (2 * (k : ℝ) * Real.pi / 3) / (n : ℝ) ^ k‖ ≤ (1 / (n : ℝ)) ^ k
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hr0 k), one_div_pow]
      gcongr
      exact Real.abs_cos_le_one _
  have h3 := hsum.sum_add_tsum_nat_add 3
  have hshift : ∀ k : ℕ, Real.cos (2 * ((k + 3 : ℕ) : ℝ) * Real.pi / 3) / (n : ℝ) ^ (k + 3) =
      Real.cos (2 * (k : ℝ) * Real.pi / 3) / (n : ℝ) ^ k / (n : ℝ) ^ 3 := by
    intro k
    rw [cos3 k, pow_add, div_div]
  have c0 : Real.cos (2 * ((0 : ℕ) : ℝ) * Real.pi / 3) = 1 := by simp
  have e1 : 2 * ((1 : ℕ) : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by
    push_cast
    ring
  have c1 : Real.cos (2 * ((1 : ℕ) : ℝ) * Real.pi / 3) = -(1 / 2) := by
    rw [e1, Real.cos_pi_sub, Real.cos_pi_div_three]
  have e2 : 2 * ((2 : ℕ) : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi := by
    push_cast
    ring
  have c2 : Real.cos (2 * ((2 : ℕ) : ℝ) * Real.pi / 3) = -(1 / 2) := by
    rw [e2, Real.cos_add_pi, Real.cos_pi_div_three]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, c0, c1, c2,
    tsum_congr hshift, tsum_div_const] at h3
  unfold OMA.S_oeis_a373162.x
  linear_combination -h3

theorem y_eq (n : ℕ) (hn : 2 ≤ n) :
    1 - x n = ((n : ℝ) + 2) / (2 * ((n : ℝ) ^ 2 + n + 1)) := by
  have h := x_rec n hn
  have hr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have hu : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hr0
  have hden : 2 * ((n : ℝ) ^ 2 + n + 1) ≠ 0 :=
    (by positivity : (0 : ℝ) < 2 * ((n : ℝ) ^ 2 + n + 1)).ne'
  have hr1 : (n : ℝ) - 1 ≠ 0 := (by linarith : (0 : ℝ) < (n : ℝ) - 1).ne'
  have key : ((n : ℝ) - 1) * ((1 - x n) * (2 * ((n : ℝ) ^ 2 + n + 1)) - ((n : ℝ) + 2)) = 0 := by
    linear_combination (-2 * (n : ℝ) ^ 3) * h +
      ((n : ℝ) ^ 2 + (n : ℝ) * ((n : ℝ) * (n : ℝ)⁻¹ + 1) -
        2 * x n * ((n : ℝ) ^ 2 * (n : ℝ)⁻¹ ^ 2 + (n : ℝ) * (n : ℝ)⁻¹ + 1)) * hu
  have key2 := (mul_eq_zero.mp key).resolve_left hr1
  rw [eq_div_iff hden]
  linear_combination key2

theorem x_two : x 2 = 5 / 7 := by
  have h := x_rec 2 le_rfl
  norm_num at h
  linarith

theorem x_three : x 3 = 21 / 26 := by
  have h := x_rec 3 (by norm_num)
  norm_num at h
  linarith

end K11A373162

open OMA.S_oeis_a373162 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a373162.main) := by
  rintro (h | h)
  · have h1 : (0 : ℝ) ≤ (-1) ^ 1 * (x 3 - x 2) := h 1 2 le_rfl
    rw [K11A373162.x_two, K11A373162.x_three] at h1
    norm_num at h1
  · have h40 := h 40 2 le_rfl
    rw [fwdDiff_iter_eq_sum_shift] at h40
    norm_num [Finset.sum_range_succ, Nat.choose_eq_factorial_div_factorial, K11A373162.y_eq] at h40
