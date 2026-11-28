import Mathlib

/-!
# A051924: a(n) = binomial(2*n,n) - binomial(2*n-2,n-1); or (3n-2)*C(n-1), where C = Catalan numbers (A000108).

Source: https://oeis.org/A051924
Credit: @divmxnd0x

Conjecture (Gary Detlefs, Feb 19 2013, stated in A051924): `a(n) mod n^2 = n + 2` if and only if
`n` is an odd prime.

Formalization notes:
* Offset 1: `a 1, a 2, ... = 1, 4, 14, 50, 182, ...` with
  `a n = binomial(2n, n) - binomial(2n - 2, n - 1)` (the subtraction is exact in `ℕ`, as
  `binomial(2n-2, n-1) ≤ binomial(2n, n)`).
* The conjecture is stated for all indices `n ≥ 1`.
-/

namespace OMA.S_oeis_a051924

/-- A051924(n) = binomial(2n, n) - binomial(2n-2, n-1). -/
def a (n : ℕ) : ℕ := (2 * n).choose n - (2 * n - 2).choose (n - 1)

/-- Detlefs' conjecture: for `n ≥ 1`, `a(n) mod n^2 = n + 2` iff `n` is an odd prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n % n ^ 2 = n + 2 ↔ n.Prime ∧ Odd n) := by
  sorry

end OMA.S_oeis_a051924
