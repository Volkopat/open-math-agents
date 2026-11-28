import Mathlib

/-!
# A066888: Number of primes p between triangular numbers T(n) < p <= T(n+1).

Source: https://oeis.org/A066888
Credit: @gblacher2

Conjecture (comment section of A066888):
"It is conjectured that for n > 0, a(n) > 0. See also A190661." (John W. Nicholson,
May 18 2011)

The sequence has offset 0: 0, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, ...

Modelling choices:
* `T n = n * (n + 1) / 2` is the n-th triangular number (A000217), so T(0) = 0, T(1) = 1,
  T(2) = 3, ...; the division is exact because n * (n + 1) is even.
* `a n` counts the primes p with T(n) < p ≤ T(n+1), i.e. the primes in the half-open
  interval `Finset.Ioc (T n) (T (n + 1))`, exactly as in the name of the entry. For example
  a(1) = 2 (the primes 2 and 3) and a(2) = 1 (the prime 5).
* The conjecture is the statement "for n > 0, a(n) > 0"; a(0) = 0, so the hypothesis n > 0
  is needed.
-/

namespace OMA.S_oeis_a066888

/-- The n-th triangular number T(n) = n(n+1)/2. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A066888(n): the number of primes p with T(n) < p ≤ T(n+1). -/
def a (n : ℕ) : ℕ := ((Finset.Ioc (T n) (T (n + 1))).filter Nat.Prime).card

/-- The conjecture: for n > 0, a(n) > 0. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a066888
