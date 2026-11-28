import FormalConjectures.OEIS.«238281»

-- Reduction OeisA238281.conjecture_1.R1 of equal prime counts in adjacent intervals
-- (kn, (k+1)n) and ((k+1)n, (k+2)n)
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Equal prime counts in adjacent blocks: the tabulated range and the open tail

`a n` counts the integers `0 < k < n` for which the intervals `(k n, (k + 1) n)` and
`((k + 1) n, (k + 2) n)` contain the same number of primes, written with `Nat.primeCounting` as
`pi ((k + 1) n) - pi (k n) = pi ((k + 2) n) - pi ((k + 1) n)`. Sun's conjecture (i) is `a n > 0`
for every `n > 1`: among the `n - 1` consecutive block pairs below `(n + 1) n`, one pair has equal
prime counts.

For a fixed `n` the count is a finite sum over `k < n` of prime counts up to `(n + 1) n`, so every
single `n` is decided by computation; what is open is a uniform argument, and no argument is known
for equality of prime counts in blocks of this shape.

The OEIS entry A238281 carries Sun's table of `a(n)` for `n = 1..5000`, and that table has
`a(n) > 0` for every `n > 1` in it. Beyond a finite search there is no proof, so the conjecture
splits at the end of the tabulated range:

* `H1` (tabulated range): `1 < n <= 5000` has `a n > 0`. Finite: for each `n` at most `n - 1`
  block pairs, with prime counts below `(n + 1) n`.
* `H2` (the open tail): `5000 < n` has `a n > 0`. Nothing is known here: the primes in blocks of
  length `n` up to the unknown `n`-th terms behave as irregularly as Siegel zeros allow, so no
  argument is known for it.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA238281_conjecture_1_R1

/-- The tabulated range: every `n` with `1 < n <= 5000` has a `k < n` for which the two consecutive
blocks `(k n, (k + 1) n)` and `((k + 1) n, (k + 2) n)` contain the same number of primes
(OEIS A238281: Sun's table of `a(n)` for `n = 1..5000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 5000 → 0 < OeisA238281.a n

/-- The open tail: every `n > 5000` has such a `k`. Nothing is known here, so no argument is
available for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 5000 < n → 0 < OeisA238281.a n

theorem main : H1 → H2 → type_of% @OeisA238281.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 5000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA238281_conjecture_1_R1
