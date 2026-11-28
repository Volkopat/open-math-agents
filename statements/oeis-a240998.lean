import Mathlib

/-!
# A240998: G.f. satisfies: A(x)^2 = x + A(x + 2*x^2).

Source: https://oeis.org/A240998
Credit: @avivorly

A240998 (offset 0): the coefficients of the power series `A(x)` with `A(0) = 1` and `A(x)^2 = x + A(x + 2x^2)`:
1, 1, 1, 2, 11, 86, 942, 12996, 217179, ...

Conjecture (in the entry, Paul D. Hanna's sequence): for `n > 0`, `a(n) == 1 (mod 2)` iff `n = 2^k` for some `k >= 0`.

Conventions:
- `A` is a formal power series over `ℤ` with constant coefficient `1` satisfying `A^2 = X + A(X + 2X^2)`, where
  `A(X + 2X^2)` is the substitution `PowerSeries.subst (X + 2X^2) A` (well defined: `X + 2X^2` has constant coefficient 0).
  These two conditions determine `A` uniquely (comparing coefficients of `x^n` gives `a(n) = [n = 1] +
  Sum_{k<n} a(k) C(k, n-k) 2^(n-k) - Sum_{0<i<n} a(i) a(n-i)` for `n ≥ 1`), so `a(n)` is the coefficient of `x^n` in `A`.
  (The constant coefficient must be fixed: `A(0)^2 = A(0)` also allows `A(0) = 0`, which gives a different series.)
- The claim is stated for every such `A` and every `n > 0`.
-/

namespace OMA.S_oeis_a240998

open PowerSeries

theorem main :
    ∀ A : PowerSeries ℤ, constantCoeff A = 1 →
      A ^ 2 = X + A.subst (X + 2 * X ^ 2 : PowerSeries ℤ) →
      ∀ n : ℕ, 0 < n → (Odd (coeff n A) ↔ ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a240998
