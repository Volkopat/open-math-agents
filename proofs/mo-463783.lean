import OMAStatements.S_mo_463783
import Mathlib

/-!
# MathOverflow 463783: a vanishing sum does not force `z ^ k = 1`

Counterexample: `p = 3 - 3 X²`, `k = 4` and `z = exp(iπ/3)`.
The values `p(1), …, p(4) = 0, -9, -24, -45` reduce to `0, 3, 0, 3` modulo `4`, so the sum is
`2 + 2 z³ = 2 - 2 = 0` because `z³ = exp(iπ) = -1`.  But `z⁴ = -z ≠ 1`, since the real part of `z`
is `cos(π/3) = 1/2`, not `-1`.
-/

open Polynomial in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_463783.main) := by
  intro h
  have hz3 : Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) ^ 3 = -1 := by
    rw [← Complex.exp_nat_mul]
    have e : ((3 : ℕ) : ℂ) * (((Real.pi / 3 : ℝ) : ℂ) * Complex.I) = Real.pi * Complex.I := by
      push_cast
      ring
    rw [e, Complex.exp_pi_mul_I]
  have hre : (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I)).re = 1 / 2 := by
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  have hp : ∀ t : ℤ, (C 3 - C 3 * X ^ 2 : Polynomial ℤ).eval t = 3 - 3 * t ^ 2 := by
    intro t
    simp
  have key := h (C 3 - C 3 * X ^ 2) 4 (by norm_num) (Complex.exp ((Real.pi / 3 : ℝ) * Complex.I))
    (Complex.norm_exp_ofReal_mul_I _) (by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      simp only [hp]
      have v0 : ((3 - 3 * (((0 : ℕ) : ℤ) + 1) ^ 2) % ((4 : ℕ) : ℤ)).toNat = 0 := by decide
      have v1 : ((3 - 3 * (((1 : ℕ) : ℤ) + 1) ^ 2) % ((4 : ℕ) : ℤ)).toNat = 3 := by decide
      have v2 : ((3 - 3 * (((2 : ℕ) : ℤ) + 1) ^ 2) % ((4 : ℕ) : ℤ)).toNat = 0 := by decide
      have v3 : ((3 - 3 * (((3 : ℕ) : ℤ) + 1) ^ 2) % ((4 : ℕ) : ℤ)).toNat = 3 := by decide
      rw [v0, v1, v2, v3, hz3]
      norm_num)
  -- `z ^ 4 = z ^ 3 * z = -z`, so `z = -1`, contradicting `re z = 1/2`
  have h4 : Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) ^ 4 =
      -Complex.exp ((Real.pi / 3 : ℝ) * Complex.I) := by
    rw [pow_succ, hz3]
    ring
  rw [h4] at key
  have hre' := congrArg Complex.re key
  rw [Complex.neg_re, hre, Complex.one_re] at hre'
  norm_num at hre'
