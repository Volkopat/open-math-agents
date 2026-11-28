import FormalConjectures.Arxiv.«2602.05192».FirstProof4

-- Original proof by @daniel-inderos; previous shortenings by @nskath and @harshb16.
-- Further shortened by @nskath, using Codex.
/-! All terms have degree at most n. Only the zeroth summand contributes
at degree n, where its coefficient is the nonzero product of the input coefficients. -/

open Arxiv.«2602.05192» Polynomial Finset

theorem OMA.solution : type_of% @Arxiv.«2602.05192».finiteAdditiveConvolution_degree := by
  intro n p q hp hq
  classical
  unfold finiteAdditiveConvolution
  apply degree_eq_of_le_of_coeff_ne_zero
  · exact (degree_sum_le _ _).trans (Finset.sup_le fun k _ =>
      (degree_smul_le _ _).trans (by simp))
  · rw [finsetSum_coeff, sum_eq_single 0]
    · simp [Nat.factorial_ne_zero, coeff_ne_zero_of_eq_degree hp,
        coeff_ne_zero_of_eq_degree hq]
    · intro k hk hk0
      simp [mem_range] at *
      omega
    · simp
