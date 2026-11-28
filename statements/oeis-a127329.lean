import Mathlib

/-!
# OEIS A127329: semiprimes that are the sum of three primes in arithmetic progression

Source: https://oeis.org/A127329
Credit: @PEELY350 (Vihaan Naik; agent: Claude Code, model claude-opus-5-5)

The sequence lists, in increasing order, the semiprimes equal to `p + q + r` for primes
`p < q < r` in arithmetic progression (`15 = 3 + 5 + 7`, `21 = 3 + 7 + 11`, `33, 39, 51, …`).
Conjecture (Zak Seidov, 2015, formula field of the entry): `a(n) = 3 · prime(n + 2)` for `n ≥ 1`,
that is, the terms are exactly `3q` for the primes `q ≥ 5`.

Conventions:
* A semiprime is a natural number with exactly two prime factors counted with multiplicity
  (`n.primeFactorsList.length = 2`).
* The progression is `p, p + d, p + 2d` with common difference `d ≥ 1`: the three primes are
  distinct (a constant progression would put `6 = 2 + 2 + 2` and `9 = 3 + 3 + 3` in the sequence,
  but it starts at `15`).
* OEIS offset 1: `a(n)` is `Nat.nth IsTerm (n - 1)`, and `prime(k)` (`prime(1) = 2`) is
  `Nat.nth Nat.Prime (k - 1)`, so `a(n + 1) = 3 · prime(n + 3)` reads as below for `n ≥ 0`.
-/

namespace OMA.S_oeis_a127329

/-- `m` is a semiprime equal to the sum of three primes in arithmetic progression. -/
def IsTerm (m : ℕ) : Prop :=
  m.primeFactorsList.length = 2 ∧
    ∃ p d : ℕ, 0 < d ∧ p.Prime ∧ (p + d).Prime ∧ (p + 2 * d).Prime ∧
      m = p + (p + d) + (p + 2 * d)

/-- The conjecture `a(n) = 3 · prime(n + 2)`, in 0-indexed form. -/
theorem main : ∀ n : ℕ, Nat.nth IsTerm n = 3 * Nat.nth Nat.Prime (n + 2) := by
  sorry

end OMA.S_oeis_a127329
