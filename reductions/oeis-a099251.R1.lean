import OMAStatements.S_oeis_a099251
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Irwin's integral for A099251

Sela Fried, *Proof of a conjecture stated in A099251* (2026),
https://oeis.org/A099251/a099251_1.pdf, expands the squared linear factor,
evaluates beta moments, and identifies the signed Catalan transform with the
Riordan number. The last identification is attributed to Kruchinin.
Here the finite moment expansion, including endpoint integrability, is proved.
-/
-- Credit: @Aryan-Poonacha

namespace OMA.R_oeis_a099251_R1

open MeasureTheory OMA.S_oeis_a099251

private lemma weight_integrable : IntervalIntegrable (fun t : ℝ => Real.sqrt ((1-t)/t)) volume 0 1 := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
    (r := -(1/2:ℝ)) (by norm_num)
  have hc : Continuous (fun t : ℝ => Real.sqrt (1-t)) := by fun_prop
  apply (h.mul_continuousOn hc.continuousOn).congr_uIoo
  intro t ht
  rw [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
  change t ^ (-(1/2:ℝ)) * Real.sqrt (1-t) = Real.sqrt ((1-t)/t)
  rw [Real.sqrt_div (by linarith [ht.2]), Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
  ring

private lemma expand (m : ℕ) (t : ℝ) :
    Real.sqrt ((1-t)/t) * (1 - 4*t)^m =
      ∑ j ∈ Finset.range (m+1), ((-1:ℝ)^j * m.choose j) * (Real.sqrt ((1-t)/t) * (4*t)^j) := by
  rw [show 1-4*t = (-1)*(4*t)+1 by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_pow,one_pow]
  ring

/-- Binomial expansion under the improper endpoint for every exponent. -/
private lemma transform (m : ℕ) :
    (∫ t in (0:ℝ)..1, Real.sqrt ((1-t)/t) * (1-4*t)^m) =
      ∑ j ∈ Finset.range (m+1), ((-1:ℝ)^j * m.choose j) *
        ∫ t in (0:ℝ)..1, Real.sqrt ((1-t)/t) * (4*t)^j := by
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact intervalIntegral.integral_const_mul _ _
  · intro j _
    apply IntervalIntegrable.const_mul
    apply weight_integrable.mul_continuousOn
    fun_prop

/-- The beta moment, scaled to the Catalan integer. -/
def H1 : Prop := ∀ j : ℕ,
  (2 / Real.pi) * (∫ t in (0:ℝ)..1, Real.sqrt ((1-t)/t) * (4*t)^j) = catalan j

/-- The signed binomial transform at even indices, as an integer identity. -/
def H2 : Prop := ∀ n : ℕ, (riordan (2*n) : ℤ) =
  ∑ j ∈ Finset.range (2*n+1), (-1:ℤ)^j * (2*n).choose j * catalan j

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a099251.main := by
  intro beta kruchinin n
  have identity : (riordan (2*n) : ℝ) =
      ∑ j ∈ Finset.range (2*n+1), (-1:ℝ)^j * (2*n).choose j * catalan j := by
    exact_mod_cast kruchinin n
  rw [identity]
  change _ = (2/Real.pi) * ∫ t in (0:ℝ)..1, Real.sqrt ((1-t)/t) * (1-8*t+16*t^2)^n
  simp_rw [show ∀ t : ℝ, 1-8*t+16*t^2 = (1-4*t)^2 by intro; ring, ← pow_mul]
  rw [transform, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← beta j]
  ring

end OMA.R_oeis_a099251_R1
