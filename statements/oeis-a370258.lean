import Mathlib

/-!
# A370258: Triangle T(n, k) = binomial(n, k)*binomial(2*n+k, k), 0 <= k <= n

Source: https://oeis.org/A370258

Offset 0. Row polynomial R(n, t) = Sum_{k = 0..n} binomial(n, k)*binomial(2*n+k, k)*t^k.
Conjecture (Peter Bala, formula section of the entry):
exp( Sum_{n >= 1} R(n,t)*x^n/n ) = 1 + (1 + 3*t)*x + (1 + 8*t + 12*t^2)*x^2 + ...
is the o.g.f. for A102537, where A102537(n, k) = (1/n)*C(2n+k, k-1)*C(n, k), n, k >= 1
(offset 1). Matching the displayed terms, the coefficient of x^n (n >= 1) is the row n+1
polynomial Sum_{k = 1..n+1} A102537(n+1, k)*t^(k-1). The Gauss congruences mentioned in the
entry are stated there only as a consequence of this conjecture, so they are not the target.

Formalized: everything lives in the polynomial ring ℚ[t]. Writing
F(x) = 1 + Sum_{n >= 1} B(n) x^n with B(n) as above, the identity F = exp(Sum R(n) x^n/n)
is equivalent (F has constant term 1) to x F'(x) = (Sum_{n >= 1} R(n) x^n) F(x), i.e.
to n*B(n) = Sum_{j = 1..n} R(j)*B(n-j) for all n >= 1 with B(0) = 1. That coefficient
recurrence is the statement. A102537(n+1, k) is written as the rational number
C(2n+2+k, k-1)*C(n+1, k)/(n+1).
-/

namespace OMA.S_oeis_a370258

open Polynomial

/-- Row polynomial R(n, t) of A370258. -/
noncomputable def R (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C ((Nat.choose n k * Nat.choose (2 * n + k) k : ℕ) : ℚ) * X ^ k

/-- A102537(n, k) = (1/n) * C(2n+k, k-1) * C(n, k), as a rational number. -/
noncomputable def T102537 (n k : ℕ) : ℚ :=
  ((Nat.choose (2 * n + k) (k - 1) * Nat.choose n k : ℕ) : ℚ) / (n : ℚ)

/-- Coefficient of x^n in the conjectured o.g.f.: 1 for n = 0, and row n+1 of A102537
as a polynomial in t for n >= 1. -/
noncomputable def B (n : ℕ) : ℚ[X] :=
  if n = 0 then 1 else
    ∑ k ∈ Finset.Icc 1 (n + 1), C (T102537 (n + 1) k) * X ^ (k - 1)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (n : ℚ[X]) * B n = ∑ j ∈ Finset.Icc 1 n, R j * B (n - j) := by
  sorry

end OMA.S_oeis_a370258
