import FormalConjectures.OEIS.«236097»

-- Reduction OeisA236097.conjecture.R1 of the count of k with p = phi(k) + phi(n - k) / 2 + 1
-- and prime(p) - p -+ 1 twin primes
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Totients followed by a twin prime of primes: the tabulated range and the open tail

`a n` counts the integers `0 < k < n - 2` for which `p = phi k + phi (n - k) / 2 + 1` is prime and
`p_p - p - 1`, `p_p - p + 1` are both prime, where `p_p` is the `p`-th prime. Sun's conjecture is
`a n > 0` for every `n > 31`: every such `n` has a `k` whose totients produce a prime index `p`
with a twin prime pair just below the `p`-th prime, which would give infinitely many primes `p`
with `{p_p - p - 1, p_p - p + 1}` a twin prime pair.

For a fixed `n` the count is a finite sum over `k < n - 1`, so every single `n` is decided by
computation; what is open is a uniform argument, and no argument is known for the twin prime shape
it forces.

The OEIS entry A236097 carries Sun's table of `a(n)` for `n = 1..10000`, and that table has
`a(n) > 0` for every `n > 31` in it. Beyond a finite search there is no proof, so the conjecture
splits at the end of the tabulated range:

* `H1` (tabulated range): `31 < n <= 10000` has `a n > 0`. Finite: for each `n` at most `n - 3`
  totient sums and primality tests of numbers below `n log n`.
* `H2` (the open tail): `10000 < n` has `a n > 0`. Nothing is known here: it contains the
  infinitude of twin prime pairs `(p_p - p - 1, p_p - p + 1)`, which is open.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA236097_conjecture_R1

/-- The tabulated range: every `n` with `31 < n <= 10000` has a witness `k < n - 2` with
`p = phi k + phi (n - k) / 2 + 1` prime and `p_p - p -+ 1` a twin prime pair
(OEIS A236097: Sun's table of `a(n)` for `n = 1..10000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 31 < n → n ≤ 10000 → 0 < OeisA236097.a n

/-- The open tail: every `n > 10000` has such a witness. This range contains the (open) statement
that there are infinitely many primes `p` with `p_p - p - 1` and `p_p - p + 1` both prime, so no
argument is known for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → 0 < OeisA236097.a n

theorem main : H1 → H2 → type_of% @OeisA236097.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA236097_conjecture_R1
