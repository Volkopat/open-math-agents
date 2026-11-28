import Mathlib

/-!
# A329105: a(n) = (Sum_{k=0..n-1} (1435*k+113)*3240^(n-1-k)*T_k(7,1)*T_k(10,10)^2)/(n*10^(n-1)), where T_k(b,c) denotes the coefficient of x^k in the expansion of (x^2+b*x+c)^k.

Source: https://oeis.org/A329105
Credit: @azmiozgen

Conjecture 1 (Zhi-Wei Sun, from the entry), first part of (i): a(n) is an integer for each n > 0. (The
series identity in (i), the congruence in (ii) and the further remarks are not stated here.)

Formalization notes:
* a(n), offset 1, is defined in ℚ by the formula in the name; T_k(b, c) uses Mathlib polynomials over ℤ.
* Controls (computed): a(1..3) = 113, 72486, 22959360, as in the entry; a(n) is an integer for n < 60.
-/

namespace OMA.S_oeis_a329105

/-- `T_k(b, c)`: the coefficient of `x^k` in `(x^2 + b x + c)^k`. -/
noncomputable def T (k : ℕ) (b c : ℤ) : ℤ := ((Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ^ k).coeff k

/-- A329105(n), in `ℚ`. -/
noncomputable def a (n : ℕ) : ℚ :=
  (∑ k ∈ Finset.range n, ((1435 * k + 113) * 3240 ^ (n - 1 - k) * T k 7 1 * T k 10 10 ^ 2 : ℤ)) /
    (n * 10 ^ (n - 1))

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ z : ℤ, a n = z := by
  sorry

end OMA.S_oeis_a329105
