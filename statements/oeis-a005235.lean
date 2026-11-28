import Mathlib

/-!
# A005235: Fortunate numbers: least m > 1 such that m + prime(n)# is prime, where p# denotes the product of all primes <= p.

Source: https://oeis.org/A005235
Credit: @divmxnd0x

Conjecture (Reo F. Fortune, stated in A005235): `a(n)` is always prime.

Formalization notes:
* `prime n` is the `n`-th prime with `prime 1 = 2`, and `prime(n)#` is Mathlib's `primorial`
  (the product of all primes `≤ prime n`).
* `a n` is the least `m > 1` with `m + prime(n)#` prime (offset 1: `a 1, a 2, ... = 3, 5, 7, 13,
  23, 17, ...`). Such `m` always exists (there are infinitely many primes), so the infimum is
  attained.
-/

namespace OMA.S_oeis_a005235

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A005235(n): the least `m > 1` such that `m + prime(n)#` is prime. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ (m + primorial (prime n)).Prime}

/-- Fortune's conjecture: every Fortunate number is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a005235
