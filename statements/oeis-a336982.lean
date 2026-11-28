import Mathlib

/-!
# A336982: a(n) = (Sum_{k=0..n-1}(540*k + 137)*3136^(n-1-k)*C(2*k, k)*T_k(2, 81)*T_k(14, 81))/ (2*n*C(2*n, n)), where T_k(b, c) denotes the coefficient of x^k in the expansion of (x^2 + b*x + c)^k.

Source: https://oeis.org/A336982
Credit: @azmiozgen

Conjecture 1 (Zhi-Wei Sun, from the entry): a(n) is an integer for each n > 1. Moreover, a(n) is odd if
and only if n = 2^k + 1 for some nonnegative integer k. (Conjecture 2 of the entry is not stated here.)

Formalization notes:
* a(n), offset 2, is defined in ℚ by the formula in the name; T_k(b, c) uses Mathlib polynomials over ℤ.
* Controls (computed): a(2..4) = 19481, 15834677, 11228057204, as in the entry; for 2 ≤ n < 60 every a(n)
  is an integer, odd exactly at n = 2, 3, 5, 9, 17, 33.
-/

namespace OMA.S_oeis_a336982

/-- `T_k(b, c)`: the coefficient of `x^k` in `(x^2 + b x + c)^k`. -/
noncomputable def T (k : ℕ) (b c : ℤ) : ℤ := ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ k).coeff k

/-- A336982(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((540 * k + 137) * 3136 ^ (n - 1 - k) * ((2 * k).choose k : ℤ) * T k 2 81 *
    T k 14 81 : ℤ)) / (2 * n * ((2 * n).choose n : ℚ))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 < n → ∃ z : ℤ, a n = z ∧ (Odd z ↔ ∃ k : ℕ, n = 2 ^ k + 1) := by
  sorry

end OMA.S_oeis_a336982
