import Mathlib

/-!
# A093538: Number of primes between 10^n and 10^n+100.

Source: https://oeis.org/A093538
Credit: @darealpandaboi

Conjecture (Robert Israel, Feb 28 2020): a(n) = 1 for infinitely many n, but a(n) >= 2 for only
finitely many.

Translation notes.
* a(n) counts primes p with 10^n <= p <= 10^n + 100 (offset 0). The endpoints matter only for
  n = 0, where 101 is counted: this reproduces the listed data 26, 25, 21, 16, 11, 6, 6, 2, ...
  (checked by computer). For n >= 1 both endpoints are even.
* The remark that a(n) <= 1 may hold for n > 775 is a speculation, not part of the conjecture.
-/

namespace OMA.S_oeis_a093538

/-- The number of primes in [10^n, 10^n + 100]. -/
def a (n : ℕ) : ℕ := ((Finset.Icc (10 ^ n) (10 ^ n + 100)).filter Nat.Prime).card

theorem main : {n : ℕ | a n = 1}.Infinite ∧ {n : ℕ | 2 ≤ a n}.Finite := by
  sorry

end OMA.S_oeis_a093538
