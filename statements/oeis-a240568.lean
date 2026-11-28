import Mathlib

/-!
# A240568: Difference between n times the n-th prime and twice the sum of the first n primes.

Source: https://oeis.org/A240568
Credit: @azmiozgen

Conjecture (Robert Mandl), proved by Rosser and Schoenfeld (Math. Comp. 29 (1975), 243-269), as
noted in the entry: a(n) > 0 for n > 8.

Formalization notes:
* prime(n) is the n-th prime with prime(1) = 2 (offset 1), i.e. `Nat.nth Nat.Prime (n - 1)`.
* a(n) = n * prime(n) - 2 * Sum_{k=1..n} prime(k), computed in the integers.
* Controls: a(1..12) = -2, -4, -5, -6, -1, -4, 3, -2, 7, 32, 21, 50, as in the entry
  (e.g. a(1) = 1*2 - 2*2 = -2, a(9) = 9*23 - 2*100 = 7).
-/

namespace OMA.S_oeis_a240568

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A240568(n) = n * prime(n) - 2 * (prime(1) + ... + prime(n)). -/
noncomputable def a (n : ℕ) : ℤ :=
  (n : ℤ) * prime n - 2 * ∑ k ∈ Finset.Icc 1 n, (prime k : ℤ)

/-- Mandl's conjecture (Rosser–Schoenfeld): `a(n) > 0` for `n > 8`. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a240568
