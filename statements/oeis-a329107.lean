import Mathlib

/-!
# A329107: a(n) = (Sum_{k=0..n-1}(840*k+197)(-1)^k*2430^(n-1-k)*T_k(8,1)*T_k(5,-5)^2)/(n*5^(n-1)), where T_k(b,c) denotes the coefficient of x^k in the expansion of (x^2+b*x+c)^k.

Source: https://oeis.org/A329107
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry), first part of (i): a(n) is a positive integer for each n > 0.
(The series identity in (i) and the congruence in (ii) are not stated here.)

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; T_k(b, c) uses Mathlib polynomials over ℤ.
* Controls (computed): a(1..3) = 197, 27131, 9162090, as in the entry; a(n) is a positive integer for
  n < 70.
-/

namespace OMA.S_oeis_a329107

/-- `T_k(b, c)`: the coefficient of `x^k` in `(x^2 + b x + c)^k`. -/
noncomputable def T (k : ℕ) (b c : ℤ) : ℤ := ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ k).coeff k

/-- A329107(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((840 * k + 197) * (-1 : ℤ) ^ k * 2430 ^ (n - 1 - k) * T k 8 1 *
    T k 5 (-5) ^ 2 : ℤ)) / (n * 5 ^ (n - 1))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, 0 < m ∧ a n = m := by
  sorry

end OMA.S_oeis_a329107
