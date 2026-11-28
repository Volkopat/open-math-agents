import Mathlib

/-!
# A336981: a(n) = (Sum_{k=0..n-1} (4290*k + 367)*3136^(n-1-k)*C(2*k, k)*T_k(14, 1)*T_k(17, 16)) / (n*C(2*n-1, n-1)), where T_k(b, c) denotes the coefficient of x^k in the expansion of (x^2 + b*x + c)^k.

Source: https://oeis.org/A336981
Credit: @azmiozgen

Conjecture 1 (Zhi-Wei Sun, from the entry): a(n) is an integer for each n > 0. Moreover, a(n) is even
for every n > 1. (Conjecture 2 of the entry, on series identities and congruences, is not stated here.)

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; T_k(b, c) uses Mathlib polynomials over ℤ.
* Controls (computed): a(1..3) = 367, 561274, 465761738, as in the entry; for n < 70 every a(n) is an
  integer, even for n > 1.
-/

namespace OMA.S_oeis_a336981

/-- `T_k(b, c)`: the coefficient of `x^k` in `(x^2 + b x + c)^k`. -/
noncomputable def T (k : ℕ) (b c : ℤ) : ℤ := ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ k).coeff k

/-- A336981(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((4290 * k + 367) * 3136 ^ (n - 1 - k) * ((2 * k).choose k : ℤ) * T k 14 1 *
    T k 17 16 : ℤ)) / (n * ((2 * n - 1).choose (n - 1) : ℚ))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = z) ∧ ∀ n : ℕ, 1 < n → ∃ z : ℤ, a n = z ∧ Even z := by
  sorry

end OMA.S_oeis_a336981
