import Mathlib

/-!
# A moment formula for the coefficients of exp(exp x - 1)/(2 - exp x)

For an exponential generating function, the nth coefficient is its nth
derivative at zero. At the positive integer orders used here, the upper
incomplete gamma function has the finite expression
Γ(k+1,2) = k! exp(-2) ∑_{j=0}^k 2^j/j!.

Sources: https://oeis.org/A059099 and https://dlmf.nist.gov/8.4.E8
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a059099

noncomputable def egf (x : ℝ) : ℝ := Real.exp (Real.exp x - 1) / (2 - Real.exp x)

noncomputable def a (n : ℕ) : ℝ := iteratedDeriv n egf 0

noncomputable def partialExp (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (2 : ℝ)^j / (j.factorial : ℝ)

noncomputable def upperGamma (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * Real.exp (-2) * partialExp k

noncomputable def term (n k : ℕ) : ℝ :=
  (k : ℝ)^n * upperGamma k / ((2 : ℝ)^(k+1) * (k.factorial : ℝ))

theorem main : ∀ n : ℕ, 0 < n →
    Summable (term n) ∧ a n = Real.exp 1 * ∑' k, term n k := by
  sorry

end OMA.S_oeis_a059099
