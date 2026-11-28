import Mathlib

/-!
# A295454: a(n) = (30*n)!*(9*n)!*(5*n)!/((18*n)!*(15*n)!*(10*n)!*n!).

Source: https://oeis.org/A295454
Credit: @Squee451

Data (offset 0): 1, 380190, 402651263238, 481367742667183020, ...

The entry's comment (Peter Bala, 2026): Conjecture: for n >= 0, a(n/2) = (15*n)!*(9*n/2)!*(5*n/2)!/((9*n)!*(15*n/2)!*(5*n)!*(n/2)!) is an integer, where fractional factorials are defined using the Gamma function; for example, (9*n/2)! := Gamma(9*n/2 + 1).

Conventions.
* As the conjecture says, `x!` for real `x` is `Gamma(x + 1)`; this is `fac`. For natural `x` it is
  the usual factorial, so `a` below extends the title's sequence to real arguments.
* The conjecture is that `a (n / 2)` is an integer for every natural number `n` (for even `n` this is
  the integrality of the title's sequence itself). The displayed closed form for `a(n/2)` in the
  conjecture is just the definition with `n/2` substituted, so it is not restated.
-/

namespace OMA.S_oeis_a295454

/-- `x!` for real `x`, defined with the Gamma function. -/
noncomputable def fac (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- A295454, extended to real arguments through `fac`. -/
noncomputable def a (x : ℝ) : ℝ := fac (30 * x) * fac (9 * x) * fac (5 * x) / (fac (18 * x) * fac (15 * x) * fac (10 * x) * fac x)

/-- `a (n / 2)` is an integer for every natural number `n`. -/
theorem main : ∀ n : ℕ, ∃ z : ℤ, a ((n : ℝ) / 2) = (z : ℝ) := by
  sorry

end OMA.S_oeis_a295454
