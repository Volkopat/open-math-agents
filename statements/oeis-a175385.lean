import Mathlib

/-!
# A175385: a(n) = numerator of Sum_{i=1..n} binomial(2n-i-1, i-1)/i

Source: https://oeis.org/A175385 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A175385 (Vladimir Shevelev, Zak Seidov, Apr 24 2010), offset 1: a(n) = numerator of
Sum_{i=1..n} binomial(2n-i-1,i-1)/i. Data
1, 3, 17, 23, 61, 107, 421, 1103, 5777, 7563, 19801, 103681, 135721, 355323, ...
(the sums are 1, 3/2, 17/6, 23/4, 61/5, 107/4, 421/7, 1103/8, 5777/18, 7563/10, ...).

Comments: We conjecture that Sum_{i=1..n} ((1/i)*C(2n-i-1,i-1)) is not an integer for n>1.

Formalization notes.
* The sum is a rational number: the sum over i in `Finset.Icc 1 n` of the binomial coefficient
  C(2n-i-1, i-1), cast to `ℚ`, divided by i. For 1 <= i <= n the natural subtractions
  `2 * n - i - 1` and `i - 1` are exact.
* `main` says: for each n > 1, this rational number is not equal to an integer.
-/

namespace OMA.S_oeis_a175385

/-- For n > 1, the sum Sum_{i=1..n} C(2n-i-1, i-1)/i is not an integer. -/
theorem main : ∀ n : ℕ, 1 < n →
    ¬ ∃ z : ℤ, (∑ i ∈ Finset.Icc 1 n, ((2 * n - i - 1).choose (i - 1) : ℚ) / (i : ℚ)) = (z : ℚ) := by
  sorry

end OMA.S_oeis_a175385
