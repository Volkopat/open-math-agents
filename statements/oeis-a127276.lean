import Mathlib

/-!
# The Hankel transform A127276

Source: Paul Barry, A127275 and A127276, https://oeis.org/A127275 and
https://oeis.org/A127276 (OEIS Foundation, CC BY-SA 4.0). R. J. Mathar
conjectured the formula and the generating function. Credit: @connoranderson.

The source coefficients below use Barry's binomial expression, with 0⁰=1
at index zero. The stated formula is written without negative exponents
so it applies directly at the two smallest indices.
-/

namespace OMA.S_oeis_a127276
noncomputable def term (n : ℕ) : ℚ :=
  (Nat.centralBinom n : ℚ) - ((4:ℚ)^n - 0^n)/4

noncomputable def hankel (n : ℕ) : ℚ :=
  (Matrix.of fun i j : Fin (n+1) => term (i.val+j.val)).det

theorem main : (∀ n : ℕ, hankel n = 2^n*(1-(n:ℚ)*(n+1)/4)) ∧
    (1-2*PowerSeries.X)^3 * PowerSeries.mk hankel =
      (1-4*PowerSeries.X)*(1-PowerSeries.X) := by
  sorry

end OMA.S_oeis_a127276
