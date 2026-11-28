import OMAReductions.R_Erdos969_erdos_969_variants_prime_number_theorem_R1
import Mathlib

/-! Evaluate the absolutely convergent Möbius Dirichlet series at two. -/
open ArithmeticFunction
open scoped Moebius

theorem OMA.solution : OMA.R_Erdos969_erdos_969_variants_prime_number_theorem_R1.H3 := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have hz := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at hz
  let f (d : ℕ) := (μ d : ℂ)
  change (Real.pi : ℂ)^2 / 6 * LSeries f 2 = 1 at hz
  have he : LSeries f 2 = 6 / (Real.pi : ℂ)^2 := by
    apply (eq_div_iff (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mpr
    linear_combination 6 * hz
  have hsum : Summable (LSeries.term f 2) := LSeriesSummable_moebius_iff.mpr hs
  apply Complex.hasSum_ofReal.mp
  convert hsum.hasSum using 1
  · ext d
    rcases eq_or_ne d 0 with rfl | hd
    · simp
    · rw [LSeries.term_of_ne_zero hd, show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, Complex.cpow_natCast]
      simp [f]
  · push_cast
    exact he.symm
