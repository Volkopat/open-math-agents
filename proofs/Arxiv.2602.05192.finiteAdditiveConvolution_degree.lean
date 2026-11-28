import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Original proof by @daniel-inderos. Previous shortening by @nskath.
-- Only the term indexed by zero contributes to the top coefficient.

open Arxiv.«2602.05192» Polynomial Finset

theorem OMA.solution : type_of% @Arxiv.«2602.05192».finiteAdditiveConvolution_degree := by
  intro n p q hp hq
  classical
  unfold finiteAdditiveConvolution
  apply degree_eq_of_le_of_coeff_ne_zero
  · exact (degree_sum_le _ _).trans (Finset.sup_le fun k _ => (degree_smul_le _ _).trans (by simp))
  · simp only [finsetSum_coeff, Polynomial.coeff_smul, coeff_X_pow, smul_eq_mul]
    rw [sum_eq_single 0]
    · simpa [show (n.factorial : ℝ) ≠ 0 by positivity] using
        mul_ne_zero (coeff_ne_zero_of_eq_degree hp) (coeff_ne_zero_of_eq_degree hq)
    · intro k hk hk0
      simp [show n ≠ n - k by have := mem_range.mp hk; omega]
    · simp
