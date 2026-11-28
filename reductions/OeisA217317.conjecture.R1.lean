import FormalConjectures.OEIS.«217317»

-- Reduction OeisA217317.conjecture.R1 of Number of primes between $n^2$ and $n^2 + (\log_2 n)^2$
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes in `(n^2, n^2 + (log2 n)^2]`: the searched range and the open tail

`a n` counts the primes between `n^2` and `n^2 + (log2 n)^2`. The window has length about
`(ln n)^2 / (ln 2)^2`, and by the prime number theorem it should contain about
`(ln n) / (2 (ln 2)^2)` primes on average, so zeros are expected to become rarer as `n` grows; the
question is whether they stop. Zeros are known exactly at `n = 1, 1165, 4292936, 4765516`, and
Greathouse's conjecture in A217317 is that they stop there: `a(n) > 0` for every `n > 4765516`.

A fixed `n` is a finite count, so each `n` is decided by computation; a uniform argument is out of
reach, because a single prime in a window of length about `(log2 n)^2` is a Legendre-type statement
(between `n^2` and `(n+1)^2` on average) and the conjecture is consistent with Granville's
`lim sup (p(n+1) - p(n)) / (log p(n))^2 >= 2 / e^gamma`.

The OEIS entry A217317 records where the computation stops: the conjecture was checked up to
`5 * 10^10` (Charles R Greathouse IV, Mar 21 2013) and then up to `4 * 10^18` (Mar 21 2016).
So the conjecture splits at the end of the searched range:

* `H1` (searched range): `4765516 < n <= 4 * 10^18` has `a n > 0`. Finite: for each `n` a window of
  about `(log2 n)^2` consecutive numbers below `n^2 + (log2 n)^2`.
* `H2` (the open tail): `4 * 10^18 < n` has `a n > 0`. Nothing is known here.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA217317_conjecture_R1

/-- The searched range: every `n` with `4765516 < n <= 4 * 10^18` has a prime in
`(n^2, n^2 + (log2 n)^2]` (OEIS A217317: the conjecture was checked up to `5 * 10^10` by
Charles R Greathouse IV in 2013 and up to `4 * 10^18` in 2016). -/
def H1 : Prop :=
  ∀ n : ℕ, 4765516 < n → n ≤ 4000000000000000000 → 0 < OeisA217317.a n

/-- The open tail: every `n > 4 * 10^18` has a prime in `(n^2, n^2 + (log2 n)^2]`. No known
argument gives a prime in such a short window for all large `n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 4000000000000000000 < n → 0 < OeisA217317.a n

theorem main : H1 → H2 → type_of% @OeisA217317.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 4000000000000000000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA217317_conjecture_R1
