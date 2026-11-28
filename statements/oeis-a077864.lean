import Mathlib

/-!
# A077864: Expansion of (1-x)^(-1)/(1-x-2*x^2-x^3).

Source: https://oeis.org/A077864
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A077864 (Werner Schulte, Sep 29 2015):
Conjecture: a(n) = Sum_{j=0..n/2} A027907(n+1-j,2*j+1), n >= 0.

Conventions:
* A077864 has offset 0 and is the expansion of (1-x)^(-1)/(1-x-2*x^2-x^3).
  Since (1-x)*(1-x-2*x^2-x^3) = 1 - 2*x - x^2 + x^3 + x^4, its coefficients are given by
  a(0) = 1, a(1) = 2, a(2) = 5, a(3) = 11 and a(n) = 2*a(n-1) + a(n-2) - a(n-3) - a(n-4) for n > 3
  (this recurrence is also stated in the entry); data 1, 2, 5, 11, 24, 52, 112, ...
* A027907 is the triangle of trinomial coefficients: T(n,k), for n >= 0 and 0 <= k <= 2n, is the
  coefficient of x^k in the expansion of (1 + x + x^2)^n. `T n k` is this coefficient of the
  polynomial `(1 + X + X^2)^n` over the integers.
* The upper limit n/2 of the sum is the integer part of n/2 (natural-number division), so the
  sum runs over j = 0, ..., floor(n/2), i.e. over `Finset.range (n / 2 + 1)`. For these j one has j <= n, so the row index n+1-j is a positive natural number.
* The identity is asserted for every n >= 0, as in the source.
-/

namespace OMA.S_oeis_a077864

open Polynomial

/-- A077864 (offset 0): a(0) = 1, a(1) = 2, a(2) = 5, a(3) = 11, a(n) = 2a(n-1) + a(n-2) - a(n-3) - a(n-4). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | 2 => 5
  | 3 => 11
  | n + 4 => 2 * a (n + 3) + a (n + 2) - a (n + 1) - a n

/-- A027907: the trinomial coefficient T(n,k), the coefficient of x^k in (1 + x + x^2)^n. -/
noncomputable def T (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- For every n >= 0, a(n) = Sum_{j=0..n/2} A027907(n+1-j, 2j+1). -/
theorem main : ∀ n : ℕ, a n = ∑ j ∈ Finset.range (n / 2 + 1), T (n + 1 - j) (2 * j + 1) := by
  sorry

end OMA.S_oeis_a077864
