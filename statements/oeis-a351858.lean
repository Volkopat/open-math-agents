import Mathlib

/-!
# A351858: a binomial-sum formula for [x^n] (1 + x + x^2)^(3n) / (1 + x)^(2n)

Source: https://oeis.org/A351858 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Peter Bala, Feb 27 2022), offset 0:
a(n) = [x^n] (1 + x + x^2)^(3*n)/(1 + x)^(2*n), with data
1, 1, 7, 19, 103, 376, 1825, 7547, 35175, 153838, ...

Formula section: Conjecture: a(n) = Sum_{k = 0..floor(n/2)} C(3*n,k)*C(n-k,k).

Formalization notes.
* The coefficient is taken in the ring of formal power series over the rationals, where
  1/(1 + x)^(2n) is the inverse of the power series (1 + x)^(2n) (its constant coefficient is 1).
  The coefficients are integers; `a n` is that coefficient as a rational number.
* The sum runs over k = 0, ..., floor(n/2), that is `Finset.range (n / 2 + 1)`. For these k one
  has k <= n - k, so the subtraction of natural numbers n - k is the true one.
* The entry has a second conjecture, in the comments, on supercongruences for a family of
  sequences. It is a different claim and is not stated here.
-/

namespace OMA.S_oeis_a351858

open PowerSeries

/-- A351858(n): the coefficient of x^n in (1 + x + x^2)^(3n) / (1 + x)^(2n). -/
noncomputable def a (n : ℕ) : ℚ :=
  coeff n (((1 : ℚ⟦X⟧) + X + X ^ 2) ^ (3 * n) * (((1 : ℚ⟦X⟧) + X) ^ (2 * n))⁻¹)

/-- Bala's conjecture: a(n) = Sum_{k = 0..floor(n/2)} C(3n, k) C(n - k, k). -/
theorem main : ∀ n : ℕ,
    a n = ∑ k ∈ Finset.range (n / 2 + 1), ((3 * n).choose k : ℚ) * ((n - k).choose k : ℚ) := by
  sorry

end OMA.S_oeis_a351858
