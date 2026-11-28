import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A144575: recurrence for the EGF exp(1 - sqrt(1 - 2x - 3x²))

The coefficient of xⁿ/n! in an analytic function is its nth derivative at zero.
The source recurrence at n ≥ 4 is written at index n+4 to avoid integer
subtraction of sequence indices. Source: R. J. Mathar, OEIS A144575,
January 24, 2020. https://oeis.org/A144575
-/
namespace OMA.S_oeis_a144575

noncomputable def a (n : ℕ) : ℝ :=
  iteratedDeriv n (fun x : ℝ => Real.exp (1-Real.sqrt (1-2*x-3*x^2))) 0

theorem main : ∀ n : ℕ,
    a (n+4) - (2*(n:ℝ)+5)*a (n+3) - (3*(n:ℝ)^2+12*n+10)*a (n+2) -
      3*(2*(n:ℝ)+5)*a (n+1) - 9*((n:ℝ)+3)*(n+1)*a n = 0 := by
  sorry

end OMA.S_oeis_a144575
