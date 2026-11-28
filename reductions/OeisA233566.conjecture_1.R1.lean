import FormalConjectures.OEIS.«233566»

-- Reduction OeisA233566.conjecture_1.R1 of the count of primes p < n with p * phi(n - p) - 1 prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `p * phi(n - p) - 1` prime: the tabulated range and the open tail

`a n` counts the primes `p < n` for which `p * phi (n - p) - 1` is also prime, with `phi` Euler's
totient. Sun's conjecture (i) is `a n > 0` for every `n > 3`: every `n > 3` has a prime `p < n`
whose product with the totient of the remaining part, minus one, is prime again.

For a fixed `n` the count is a finite sum over the primes `p < n`, so every single `n` is decided
by computation; what is open is a uniform argument, and no argument is known for a product of a
prime with a totient.

The OEIS entry A233566 carries Sun's table of `a(n)` for `n = 1..10000`, and that table has
`a(n) > 0` for every `n > 3` in it. Beyond a finite search there is no proof, so the conjecture
splits at the end of the tabulated range:

* `H1` (tabulated range): `3 < n <= 10000` has `a n > 0`. Finite: for each `n` at most `pi n`
  products `p * phi (n - p) - 1` below `n ^ 2`.
* `H2` (the open tail): `10000 < n` has `a n > 0`. Nothing is known here: it contains the
  infinitude of primes of this shape, which is open.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA233566_conjecture_1_R1

/-- The tabulated range: every `n` with `3 < n <= 10000` has a prime `p < n` with
`p * phi (n - p) - 1` prime (OEIS A233566: Sun's table of `a(n)` for `n = 1..10000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 10000 → 0 < OeisA233566.a n

/-- The open tail: every `n > 10000` has such a prime `p < n`. Nothing is known here, so no
argument is available for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → 0 < OeisA233566.a n

theorem main : H1 → H2 → type_of% @OeisA233566.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA233566_conjecture_1_R1
