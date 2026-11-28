import Mathlib

/-!
# A328786: a(n) = (Sum_{k=0..n-1}(-1)^k*(39480*k+7321)*29700^(n-1-k)*T_k(14,1)*T_k(11,-11)^2)/n, where T_k(b,c) denotes the coefficient of x^k in the expansion of (x^2+b*x+c)^k.

Source: https://oeis.org/A328786
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry), first part of (i): a(n) is a positive integer for each n > 0,
and a(n) is odd if and only if n is a power of two. (The series identity in (i) and the congruence in
(ii) are not stated here.)

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; T_k(b, c) uses Mathlib polynomials over ℤ.
* The statement: for n ≥ 1 there is a positive integer m with a(n) = m, and m is odd iff n = 2^j.
* Controls (computed): a(1..3) = 7321, 69076403, 1423525024746, as in the entry; for n < 70 every a(n) is a
  positive integer, odd exactly at n = 1, 2, 4, 8, 16, 32, 64.
-/

namespace OMA.S_oeis_a328786

/-- `T_k(b, c)`: the coefficient of `x^k` in `(x^2 + b x + c)^k`. -/
noncomputable def T (k : ℕ) (b c : ℤ) : ℤ := ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ k).coeff k

/-- A328786(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((-1 : ℤ) ^ k * (39480 * k + 7321) * 29700 ^ (n - 1 - k) * T k 14 1 *
    T k 11 (-11) ^ 2 : ℤ)) / n

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ a n = m ∧ (Odd m ↔ ∃ j : ℕ, n = 2 ^ j) := by
  sorry

end OMA.S_oeis_a328786
