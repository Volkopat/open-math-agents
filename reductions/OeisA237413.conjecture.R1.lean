import FormalConjectures.OEIS.«237413»

-- Reduction OeisA237413.conjecture.R1 of ways to write n = k + m with p(k)^2 - 2, p(m)^2 - 2
-- and p(p(m))^2 - 2 all prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes `p^2 - 2` in two summands: the tabulated range and the open tail

`a n` counts the ways to write `n = k + m` with `k > 0` and `m > 0` such that `p_k ^ 2 - 2`,
`p_m ^ 2 - 2` and `p_{p_m} ^ 2 - 2` are all prime, where `p_j` is the `j`-th prime. Sun's
conjecture is `a n > 0` for every `n > 1`: every `n > 1` splits into two indices whose primes
stay prime after squaring and subtracting 2, and the index of the second one does too. It was
motivated by the Super Twin Prime Conjecture, and it forces infinitely many primes `q` with both
`q ^ 2 - 2` and `p_q ^ 2 - 2` prime (A237414).

For a fixed `n` the count is a finite sum over `k < n`, so every single `n` is decided by
computation; what is open is a uniform argument, and no argument is known for a shape built from
two nested prime-indexings.

The OEIS entry A237413 carries Sun's table of `a(n)` for `n = 1..10000`, and that table has
`a(n) > 0` for every `n > 1` in it. Beyond a finite search there is no proof, so the conjecture
splits at the end of the tabulated range:

* `H1` (tabulated range): `1 < n <= 10000` has `a n > 0`. Finite: for each `n` at most `n - 1`
  triples of primality tests of numbers below `(p_{p_n}) ^ 2`.
* `H2` (the open tail): `10000 < n` has `a n > 0`. Nothing is known here: it contains the
  infinitude of primes `q` with `q ^ 2 - 2` and `p_q ^ 2 - 2` both prime (A237414), which is open.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA237413_conjecture_R1

/-- The tabulated range: every `n` with `1 < n <= 10000` has a split `n = k + m` with `p_k ^ 2 - 2`,
`p_m ^ 2 - 2` and `p_{p_m} ^ 2 - 2` all prime
(OEIS A237413: Sun's table of `a(n)` for `n = 1..10000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 10000 → 0 < OeisA237413.a n

/-- The open tail: every `n > 10000` has such a split. This range contains the (open) statement
that there are infinitely many primes `q` with `q ^ 2 - 2` and `p_q ^ 2 - 2` both prime, so no
argument is known for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → 0 < OeisA237413.a n

theorem main : H1 → H2 → type_of% @OeisA237413.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA237413_conjecture_R1
