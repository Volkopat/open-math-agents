import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1
import Mathlib.NumberTheory.Harmonic.Bounds

open Finset

/-- Reindex the divisor sum by complementary divisors and bound the resulting
reciprocal sum by the full harmonic sum. -/
theorem OMA.solution : OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1.H2 := by
  intro n hn
  have subset : n.divisors ⊆ Icc 1 n := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)⟩
  calc
    (ArithmeticFunction.sigma 1 n : ℝ) = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) := by
      rw [Nat.sum_div_divisors n (fun d => (d : ℝ)), ArithmeticFunction.sigma_one_apply, Nat.cast_sum]
    _ = n * ∑ d ∈ n.divisors, (d : ℝ)⁻¹ := by
      rw [mul_sum]
      refine sum_congr rfl fun d hd => ?_
      rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) (by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'),
        div_eq_mul_inv]
    _ ≤ n * ∑ d ∈ Icc 1 n, (d : ℝ)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg subset (by intros; positivity)) (Nat.cast_nonneg n)
    _ ≤ n * (1 + Real.log n) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
      simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log n
