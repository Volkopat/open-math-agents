import OMAStatements.S_mo_349002
import Mathlib

-- Problem: mo-349002, for odd q > 1 the polynomial z^q - z^(q-2) - 1 has a real root r > 1
-- which strictly dominates every other complex root in absolute value.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Write q = m + 2 with m odd. The equation reads z^m (z^2 - 1) = 1. On [1, 2] the real function
-- x^m (x^2 - 1) goes from 0 to 3 * 2^m >= 1, so it takes the value 1 at some r > 1.
-- If z is a root with |z| >= r, then
--   1 = |z|^m |z^2 - 1| >= |z|^m (|z|^2 - 1) >= r^m (r^2 - 1) = 1,
-- so |z| = r and |z^2 - 1| = |z^2| - 1, which forces z^2 = r^2, i.e. z = r or z = -r.
-- For z = -r the left side is -r^q + r^(q-2) - 1 = -2 because q is odd. Hence z = r.

namespace MO349002

theorem exists_root (m : ℕ) : ∃ r : ℝ, 1 < r ∧ r ^ m * (r ^ 2 - 1) = 1 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ m * (x ^ 2 - 1)) (Set.Icc 1 2) := by
    fun_prop
  have h1 : (1 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ m * (x ^ 2 - 1)) 1)
      ((fun x : ℝ => x ^ m * (x ^ 2 - 1)) 2) := by
    constructor
    · simp
    · have h2 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
      show (1 : ℝ) ≤ 2 ^ m * (2 ^ 2 - 1)
      nlinarith
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2) hcont h1
  have hfr' : r ^ m * (r ^ 2 - 1) = 1 := hfr
  refine ⟨r, ?_, hfr'⟩
  rcases eq_or_lt_of_le hr.1 with h | h
  · exfalso
    rw [← h] at hfr'
    norm_num at hfr'
  · exact h

theorem sq_eq_of_norms (w : ℂ) (s : ℝ) (h1 : ‖w‖ = s) (h2 : ‖w - 1‖ = s - 1) :
    w = (s : ℂ) := by
  have e1 : w.re * w.re + w.im * w.im = s ^ 2 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, h1]
  have e2 : (w.re - 1) * (w.re - 1) + w.im * w.im = (s - 1) ^ 2 := by
    have h := Complex.sq_norm (w - 1)
    rw [Complex.normSq_apply, h2] at h
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h
    linarith
  have hre : w.re = s := by linear_combination (1 / 2 : ℝ) * e1 - (1 / 2 : ℝ) * e2
  have him : w.im = 0 := by
    have h0 : w.im * w.im = 0 := by
      rw [hre] at e1
      linear_combination e1
    exact mul_self_eq_zero.mp h0
  exact Complex.ext (by simpa using hre) (by simpa using him)

end MO349002

theorem OMA.solution : type_of% @OMA.S_mo_349002.main := by
  intro q hodd hq1
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 2 := ⟨q - 2, by omega⟩
  have hmodd : Odd m := ⟨k - 1, by omega⟩
  have hodd2 : Odd (m + 2) := ⟨k, hk⟩
  obtain ⟨r, hr1, hr⟩ := MO349002.exists_root m
  have hr0 : 0 < r := by linarith
  simp only [Nat.add_sub_cancel]
  have hreal : r ^ (m + 2) - r ^ m - 1 = 0 := by linear_combination hr
  have hc : (r : ℂ) ^ (m + 2) - (r : ℂ) ^ m - 1 = 0 := by exact_mod_cast hreal
  refine ⟨r, hr1, hc, ?_⟩
  intro z hz hne
  by_contra hlt
  have hρ : r ≤ ‖z‖ := not_lt.mp hlt
  have hz' : z ^ m * (z ^ 2 - 1) = 1 := by linear_combination hz
  have hnorm : ‖z‖ ^ m * ‖z ^ 2 - 1‖ = 1 := by
    rw [← norm_pow, ← norm_mul, hz', norm_one]
  have htri : ‖z‖ ^ 2 - 1 ≤ ‖z ^ 2 - 1‖ := by
    have h := norm_sub_norm_le (z ^ 2) 1
    rw [norm_pow, norm_one] at h
    exact h
  have hP : r ^ m ≤ ‖z‖ ^ m := pow_le_pow_left₀ hr0.le hρ m
  have hR : 0 < r ^ m := pow_pos hr0 m
  have hPpos : 0 < ‖z‖ ^ m := lt_of_lt_of_le hR hP
  have hb : 0 < r ^ 2 - 1 := by nlinarith
  have hab : r ^ 2 - 1 ≤ ‖z‖ ^ 2 - 1 := by nlinarith
  have ha : 0 < ‖z‖ ^ 2 - 1 := lt_of_lt_of_le hb hab
  -- r^m * a <= P * a <= P * N = 1 = r^m * b
  have h1 : r ^ m * (‖z‖ ^ 2 - 1) ≤ ‖z‖ ^ m * (‖z‖ ^ 2 - 1) :=
    mul_le_mul_of_nonneg_right hP ha.le
  have h2 : ‖z‖ ^ m * (‖z‖ ^ 2 - 1) ≤ ‖z‖ ^ m * ‖z ^ 2 - 1‖ :=
    mul_le_mul_of_nonneg_left htri hPpos.le
  have hle : ‖z‖ ^ 2 - 1 ≤ r ^ 2 - 1 := by
    have h3 : r ^ m * (‖z‖ ^ 2 - 1) ≤ r ^ m * (r ^ 2 - 1) := by linarith
    exact le_of_mul_le_mul_left h3 hR
  have heq : ‖z‖ ^ 2 = r ^ 2 := by linarith
  have hnz : ‖z‖ = r := by
    have h4 : (‖z‖ - r) * (‖z‖ + r) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith
    · have := norm_nonneg z
      linarith
  have hN : ‖z ^ 2 - 1‖ = r ^ 2 - 1 := by
    have h6 : ‖z‖ ^ m * ‖z ^ 2 - 1‖ = ‖z‖ ^ m * (r ^ 2 - 1) := by
      rw [hnorm, hnz, hr]
    exact mul_left_cancel₀ hPpos.ne' h6
  have hw : z ^ 2 = ((r ^ 2 : ℝ) : ℂ) :=
    MO349002.sq_eq_of_norms (z ^ 2) (r ^ 2) (by rw [norm_pow, hnz]) hN
  have hfac : (z - (r : ℂ)) * (z + (r : ℂ)) = 0 := by
    push_cast at hw
    linear_combination hw
  rcases mul_eq_zero.mp hfac with h7 | h7
  · exact hne (sub_eq_zero.mp h7)
  · have hzr : z = -(r : ℂ) := eq_neg_of_add_eq_zero_left h7
    rw [hzr, Odd.neg_pow hodd2, Odd.neg_pow hmodd] at hz
    have h8 : (2 : ℂ) = 0 := by linear_combination -hz - hc
    norm_num at h8
