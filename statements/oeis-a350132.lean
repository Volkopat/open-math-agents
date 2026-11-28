import Mathlib

/-!
# A350132: smallest m with tau(m-1) = tau(m+1) = tau(m)^n

Source: https://oeis.org/A350132

A350132 (offset 1): `a(n)` is the smallest number `m` such that
`tau(m-1) = tau(m+1) = tau(m)^n`, where `tau(m)` is the number of divisors of `m` (A000005):
34, 7, 41, 919, 18089, 446081, 27033161, 663929729, …  The corresponding triples
`[tau(a(n)-1), tau(a(n)), tau(a(n)+1)]` are `[4, 4, 4]`, `[4, 2, 4]`, `[8, 2, 8]`, `[16, 2, 16]`, …

Conjecture (Jaroslav Krizek, Dec 15 2021): `a(n)` is prime for all `n ≥ 2`, i.e., the sequence
without its first term is the sequence of smallest primes `p` such that
`tau(p-1) = tau(p+1) = 2^n` for `n ≥ 2`.

Conventions:
- `tau(m)` is `(Nat.divisors m).card`.
- `a(n)` is the least element of the set of `m > 1` with `tau(m-1) = tau(m)^n` and
  `tau(m+1) = tau(m)^n`. The restriction `m > 1` keeps `m - 1` positive; it excludes nothing,
  since `m = 0` and `m = 1` do not satisfy the two equations for `n ≥ 1` in any case.
- The statement is: for every `n ≥ 2`, any `m` that is the least element (`IsLeast`) of this set
  is prime. This does not assert that the set is nonempty.
-/

namespace OMA.S_oeis_a350132

/-- The number of divisors of `m`. -/
def tau (m : ℕ) : ℕ := (Nat.divisors m).card

theorem main :
    ∀ n m : ℕ, 2 ≤ n →
      IsLeast {m : ℕ | 1 < m ∧ tau (m - 1) = tau m ^ n ∧ tau (m + 1) = tau m ^ n} m →
      Nat.Prime m := by
  sorry

end OMA.S_oeis_a350132
