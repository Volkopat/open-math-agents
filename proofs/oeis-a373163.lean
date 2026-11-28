import OMAStatements.S_oeis_a373163
import Mathlib

/-!
# The first difference has the wrong sign

The cosine weights repeat every three terms, with values one, minus
one half, and minus one half. The tail after the first block is the
original sum scaled by the inverse cube of the index. This evaluates
the sum at 2 and 3, where it increases.
-/

namespace OMA.A373163

open OMA.S_oeis_a373163

/-- The cosine at twice the angle π/3. -/
private lemma cos_first : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = 2 * (Real.pi / 3) by ring, Real.cos_two_mul,
    Real.cos_pi_div_three]
  norm_num

/-- The third cosine is the reflection of the second around a full turn. -/
private lemma cos_second : Real.cos (4 * Real.pi / 3) = -(1 / 2) := by
  rw [show 4 * Real.pi / 3 = (1 : ℝ) * (2 * Real.pi) - 2 * Real.pi / 3 by ring]
  simpa only [Nat.cast_one] using (Real.cos_nat_mul_two_pi_sub (2 * Real.pi / 3) 1).trans cos_first

/-- Splitting off the first three summands gives a linear equation for the sum. -/
private lemma block_equation (n : ℕ) (hn : 2 ≤ n) :
    1 - 1 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ) ^ 2) +
      fraction n / (n : ℝ) ^ 3 = fraction n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  let f : ℕ → ℝ := fun k => Real.cos (2 * (k : ℝ) * Real.pi / 3) / (n : ℝ) ^ k
  have hs : Summable f := by
    refine (summable_geometric_of_lt_one (r := (n : ℝ)⁻¹) (by positivity)
      (inv_lt_one_of_one_lt₀ (by linarith))).of_norm_bounded ?_
    intro k
    rw [show f k = Real.cos (2 * (k : ℝ) * Real.pi / 3) * (n : ℝ)⁻¹ ^ k by
      simp [f, div_eq_mul_inv, inv_pow]]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg
      (show 0 ≤ (n : ℝ)⁻¹ ^ k by positivity)]
    exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
  have shift (k : ℕ) : f (k + 3) = f k / (n : ℝ) ^ 3 := by
    dsimp [f]
    rw [Nat.cast_add, Nat.cast_ofNat,
      show 2 * ((k : ℝ) + 3) * Real.pi / 3 =
        2 * (k : ℝ) * Real.pi / 3 + 2 * Real.pi by ring,
      Real.cos_add_two_pi, pow_add, div_div]
  have h := hs.sum_add_tsum_nat_add 3
  simp_rw [shift] at h
  rw [tsum_div_const] at h
  change (∑ k ∈ Finset.range 3, f k) + fraction n / (n : ℝ) ^ 3 = fraction n at h
  have first : (∑ k ∈ Finset.range 3, f k) =
      1 - 1 / (2 * (n : ℝ)) - 1 / (2 * (n : ℝ) ^ 2) := by
    norm_num [Finset.sum_range_succ, f, cos_first, cos_second, show
      (2 : ℝ) * 2 * Real.pi / 3 = 4 * Real.pi / 3 by ring]
    field_simp
    ring
  exact first ▸ h

end OMA.A373163

open OMA.S_oeis_a373163 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a373163.main) := by
  intro h
  have h₂ := A373163.block_equation 2 (by decide)
  have h₃ := A373163.block_equation 3 (by decide)
  norm_num at h₂ h₃
  have hd := h 1 2 (by decide)
  simp only [Function.iterate_one, pow_one, fwdDiff] at hd
  change 0 ≤ -1 * (fraction 3 - fraction 2) at hd
  linarith
