import Mathlib

/-!
# A262735: Expansion of x*(1-x-x^2)/((1-x)*(1-x-2*x^2-x^3)).

Source: https://oeis.org/A262735
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A262735:
Conjecture: a(n+1) = Sum_{j=0..n/2} A027907(n-j,2*j), n >= 0.

Conventions:
* A262735 has offset 0 and is the expansion of x*(1-x-x^2)/((1-x)*(1-x-2*x^2-x^3)).
  Since (1-x)*(1-x-2*x^2-x^3) = 1 - 2*x - x^2 + x^3 + x^4, its coefficients are given by
  a(0) = 0, a(1) = 1, a(2) = 1, a(3) = 2 and a(n) = 2*a(n-1) + a(n-2) - a(n-3) - a(n-4) for n > 3
  (this recurrence is also stated in the entry); data 0, 1, 1, 2, 4, 8, 17, 36, ...
* A027907 is the triangle of trinomial coefficients: T(n,k), for n >= 0 and 0 <= k <= 2n, is the
  coefficient of x^k in the expansion of (1 + x + x^2)^n. `T n k` is this coefficient of the
  polynomial `(1 + X + X^2)^n` over the integers.
* The upper limit n/2 of the sum is the integer part of n/2 (natural-number division), so the
  sum runs over j = 0, ..., floor(n/2), i.e. over `Finset.range (n / 2 + 1)`. For these j one has j <= n, so the row index n-j is a natural number.
* The identity is asserted for every n >= 0, as in the source.
-/

namespace OMA.S_oeis_a262735

open Polynomial

/-- A262735 (offset 0): a(0) = 0, a(1) = 1, a(2) = 1, a(3) = 2, a(n) = 2a(n-1) + a(n-2) - a(n-3) - a(n-4). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | n + 4 => 2 * a (n + 3) + a (n + 2) - a (n + 1) - a n

/-- A027907: the trinomial coefficient T(n,k), the coefficient of x^k in (1 + x + x^2)^n. -/
noncomputable def T (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- For every n >= 0, a(n+1) = Sum_{j=0..n/2} A027907(n-j, 2j). -/
theorem main : ∀ n : ℕ, a (n + 1) = ∑ j ∈ Finset.range (n / 2 + 1), T (n - j) (2 * j) := by
  sorry

end OMA.S_oeis_a262735
