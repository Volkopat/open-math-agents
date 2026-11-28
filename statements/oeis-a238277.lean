import Mathlib

/-!
# A238277: a(n) = |{0 <= k < n: the number of primes in the interval (k*n, (k+1)*n] is a square}|.

Source: https://oeis.org/A238277
Credit: @ceejcake

Conjecture (Zhi-Wei Sun, 2014, stated in the OEIS entry): `a(n) > 0` for all `n > 0`.
(The entry reports a verification for `n` up to `10^5`.)

Formalization notes:
* The sequence has offset `1`; `a n` is defined for all `n : ℕ` and the conjecture is stated for
  `0 < n`.
* The number of primes in the interval `(k * n, (k + 1) * n]` is the number of primes in
  `Finset.Ioc (k * n) ((k + 1) * n)`, which equals `π((k + 1) * n) - π(k * n)` as in the
  Mathematica program of the entry.
* A square means a perfect square `m ^ 2` with `m ≥ 0`, so `0` counts as a square
  (`IsSquare 0` holds); this is the convention of the entry: `a(1) = 1`, coming from `k = 0`,
  where the interval `(0, 1]` contains no prime.
* Initial values for `n = 1, 2, ..., 16`:
  `a(n) = 1, 2, 2, 2, 2, 2, 2, 3, 1, 3, 2, 4, 1, 5, 3, 3, ...`.
-/

namespace OMA.S_oeis_a238277

/-- The number of primes in the interval `(k * n, (k + 1) * n]`. -/
def primesIn (n k : ℕ) : ℕ :=
  ((Finset.Ioc (k * n) ((k + 1) * n)).filter Nat.Prime).card

/-- `a n` is the number of `k` with `0 ≤ k < n` such that the number of primes in the interval
`(k * n, (k + 1) * n]` is a perfect square (OEIS A238277). -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun k => IsSquare (primesIn n k)).card

/-- OEIS A238277 conjecture (Zhi-Wei Sun): `a n > 0` for every `n > 0`. -/
theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a238277
