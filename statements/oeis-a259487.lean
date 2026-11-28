import Mathlib

/-!
# A259487: Least positive integer m with prime(m)+2 and prime(prime(m))+2 both prime such that prime(m*n)+2 and prime(prime(m*n))+2 are both prime.

Source: https://oeis.org/A259487
Credit: @divmxnd0x

A259488 is the set of positive integers `m` with `prime(m) + 2` and `prime(prime(m)) + 2` both prime.

Conjecture (Zhi-Wei Sun, stated in A259487): Any positive rational number `r` can be written as
`m/n` with `m` and `n` terms of A259488. (This implies that there are infinitely many primes `p`
with `p + 2` and `prime(p) + 2` both prime; the existence of `a(n)` is the case `r = n`.)

Formalization notes:
* `prime(m)` is the `m`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (m - 1)`.
* With this definition `a(1) = 2`, matching the data of A259487.
-/

namespace OMA.S_oeis_a259487

/-- The `m`-th prime, `prime 1 = 2`. -/
noncomputable def prime (m : ℕ) : ℕ :=
  Nat.nth Nat.Prime (m - 1)

/-- The terms of A259488. -/
def A259488 : Set ℕ :=
  {m | 0 < m ∧ (prime m + 2).Prime ∧ (prime (prime m) + 2).Prime}

/-- Sun's conjecture: every positive rational is `m/n` with `m, n` terms of A259488. -/
theorem main : ∀ r : ℚ, 0 < r → ∃ m ∈ A259488, ∃ n ∈ A259488, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a259487
