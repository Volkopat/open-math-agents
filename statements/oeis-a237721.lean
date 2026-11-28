import Mathlib

/-!
# A237721: primes p ≤ n with floor(sqrt(n - p)) a square

Source: https://oeis.org/A237721

A237721 (offset 1): `a(n)` is the number of primes `p ≤ n` with `floor(sqrt(n-p))` a square:
0, 1, 2, 2, 3, 2, 2, 2, 1, 1, 1, 1, …  For example `a(3) = 2` since 2 is prime with
`floor(sqrt(3-2)) = 1^2`, and 3 is prime with `floor(sqrt(3-3)) = 0^2`.

Conjecture (Zhi-Wei Sun, Feb 12 2014): `a(n) > 0` for all `n > 1`, and `a(n) = 1` only for
`n = 2, 9, 10, 11, 12, 15, 16, 17`. The entry notes that this has been verified for `n` up to
`10^6`.

Both clauses are stated, as a conjunction. The second clause is given as an equivalence:
`a(n) = 1` if and only if `n` is one of the eight listed values. (That `a(n) = 1` at the eight
listed values is a finite computation, shown in the entry's examples; the open content is that
there are no others.)

Conventions:
- `floor(sqrt(m))` is `Nat.sqrt m`, and a square is a perfect square `j^2` with `j ≥ 0`
  (`IsSquare`), so `0` and `1` count as squares, as in the entry's examples.
- `a n` is the cardinality (`Set.ncard`) of the finite set of primes `p ≤ n` with
  `Nat.sqrt (n - p)` a square; `n - p` is an exact subtraction because `p ≤ n`. Indexing is the
  OEIS one (offset 1).
-/

namespace OMA.S_oeis_a237721

/-- A237721: the number of primes `p ≤ n` such that `floor(sqrt(n - p))` is a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : ℕ | p ≤ n ∧ Nat.Prime p ∧ IsSquare (Nat.sqrt (n - p))}.ncard

theorem main :
    (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔ n ∈ ({2, 9, 10, 11, 12, 15, 16, 17} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a237721
