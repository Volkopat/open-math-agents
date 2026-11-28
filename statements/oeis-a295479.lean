import Mathlib

/-!
# A295479: a(n) = (24*n)!*(4*n)!*n!/((12*n)!*(8*n)!*(7*n)!*(2*n)!).

Source: https://oeis.org/A295479
Credit: @Squee451

Data (offset 0): 1, 76488984, 36856530424884600, ...

The entry's comment (Peter Bala, 2026): Conjecture: for n >= 0, a(n/2) = (12*n)!*(2*n)!*(n/2)! / ((6*n)!*(4*n)!*(7*n/2)!*n!) is an integer, where fractional factorials are defined using the Gamma function - for example, (n/2)! := Gamma(n/2 + 1).

Conventions.
* As the conjecture says, `x!` for real `x` is `Gamma(x + 1)`; this is `fac`. For natural `x` it is
  the usual factorial, so `a` below extends the title's sequence to real arguments.
* The conjecture is that `a (n / 2)` is an integer for every natural number `n` (for even `n` this is
  the integrality of the title's sequence itself). The displayed closed form for `a(n/2)` in the
  conjecture is just the definition with `n/2` substituted, so it is not restated.
-/

namespace OMA.S_oeis_a295479

/-- `x!` for real `x`, defined with the Gamma function. -/
noncomputable def fac (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- A295479, extended to real arguments through `fac`. -/
noncomputable def a (x : ℝ) : ℝ := fac (24 * x) * fac (4 * x) * fac x / (fac (12 * x) * fac (8 * x) * fac (7 * x) * fac (2 * x))

/-- `a (n / 2)` is an integer for every natural number `n`. -/
theorem main : ∀ n : ℕ, ∃ z : ℤ, a ((n : ℝ) / 2) = (z : ℝ) := by
  sorry

end OMA.S_oeis_a295479
