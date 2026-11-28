import OMAStatements.S_oeis_a007840
import Mathlib

-- Problem: A007840: Number of factorizations of permutations of n letters into ordered cycles.
-- Upstream: formal-conjectures statements/oeis-a007840.lean:0 (declaration OMA.S_oeis_a007840.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Yanev's integral formula for A007840.

For x > 0, Gamma(x + n) / Gamma(x) is the rising factorial x (x + 1) ... (x + n - 1), whose
coefficient of x^k is the unsigned Stirling number of the first kind s(n, k) (both satisfy the
same recurrence). So the integrand is e^(-x) times the sum of s(n, k) x^k, and the integral of
x^k e^(-x) over (0, ∞) is Gamma(k + 1) = k!. -/

namespace A007840Aux

open MeasureTheory Polynomial

theorem stirling_zero_mul (n : ℕ) : Nat.stirlingFirst n 0 * n = 0 := by
  cases n <;> simp

theorem coeff_ascPochhammer (n k : ℕ) :
    (ascPochhammer ℝ n).coeff k = (Nat.stirlingFirst n k : ℝ) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp
    | succ k => simp [Polynomial.coeff_one]
  | succ n ih =>
    rw [ascPochhammer_succ_right, mul_add, Polynomial.coeff_add, Polynomial.coeff_mul_natCast]
    cases k with
    | zero =>
      rw [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, mul_zero, zero_add, ih,
        Nat.stirlingFirst_succ_zero, Nat.cast_zero]
      exact_mod_cast stirling_zero_mul n
    | succ k =>
      rw [Polynomial.coeff_mul_X, ih, ih, Nat.stirlingFirst_succ_succ]
      push_cast
      ring

theorem gamma_add_nat (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + n) = (ascPochhammer ℝ n).eval x * Real.Gamma x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : x + ((n + 1 : ℕ) : ℝ) = (x + n) + 1 := by push_cast; ring
    have h2 : x + (n : ℝ) ≠ 0 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact ne_of_gt (by linarith)
    rw [h1, Real.Gamma_add_one h2, ih, ascPochhammer_succ_eval]
    ring

theorem integral_pow_exp (k : ℕ) :
    IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ k) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), Real.exp (-x) * x ^ k = (k.factorial : ℝ) := by
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hconv := Real.GammaIntegral_convergent hpos
  have heq : Set.EqOn (fun x : ℝ => Real.exp (-x) * x ^ ((k : ℝ) + 1 - 1))
      (fun x : ℝ => Real.exp (-x) * x ^ k) (Set.Ioi 0) := by
    intro x _
    simp only
    rw [add_sub_cancel_right, Real.rpow_natCast]
  constructor
  · exact hconv.congr_fun heq measurableSet_Ioi
  · rw [← Real.Gamma_nat_eq_factorial, Real.Gamma_eq_integral hpos]
    exact (setIntegral_congr_fun measurableSet_Ioi heq).symm

theorem main_aux (n : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), Real.Gamma (x + n) / (Real.exp x * Real.Gamma x) =
      ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : ℝ) * (k.factorial : ℝ) := by
  have h1 : Set.EqOn (fun x : ℝ => Real.Gamma (x + n) / (Real.exp x * Real.Gamma x))
      (fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingFirst n k : ℝ) * (Real.exp (-x) * x ^ k)) (Set.Ioi 0) := by
    intro x hx
    have hx' : 0 < x := hx
    have hG : Real.Gamma x ≠ 0 := (Real.Gamma_pos_of_pos hx').ne'
    have hE : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
    simp only
    rw [gamma_add_nat n hx', Polynomial.eval_eq_sum_range, ascPochhammer_natDegree, Real.exp_neg,
      Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_ascPochhammer]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul, (integral_pow_exp k).2]
  · intro k _
    exact ((integral_pow_exp k).1).const_mul _

end A007840Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a007840.main := by
  intro n
  rw [A007840Aux.main_aux]
  unfold OMA.S_oeis_a007840.a
  push_cast
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
