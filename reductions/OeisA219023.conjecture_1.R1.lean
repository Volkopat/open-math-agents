import FormalConjectures.OEIS.«219023»

-- Reduction OeisA219023.conjecture_1.R1 of Primes $p < n$ with $n^2 - n + p$ and $n^2 + n - p$ prime — conjecture 1
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes `p < n` with `n^2 - n + p` and `n^2 + n - p` both prime

`a n` counts the primes `p < n` for which `n^2 - n + p` and `n^2 + n - p` are both prime. Sun's
conjecture is that `a n > 0` for every `n > 2732`; the entry notes that it is stronger than
Oppermann's conjecture, which says that both intervals `(n^2 - n, n^2)` and `(n^2, n^2 + n)` contain a
prime.

For a fixed `n` the count is a finite search over the primes `p < n`, so every single `n` is decided
by computation; what is open is a uniform argument. The statement puts two primes of different
parity conditions around `n^2`, so it is not reachable by interval-prime estimates alone.

The OEIS entry A219023 records how far the computation was pushed: the conjecture was verified for `n`
up to `1.4 * 10^7` (Zhi-Wei Sun, with a table of `a(n)` for `n = 1..20000`). Beyond a finite search
there is no proof, so the conjecture splits at the published bound:

* `H1` (searched range): `2732 < n <= 1.4 * 10^7` has `a n > 0`. Finite: for each `n` a search over
  the primes `p < n` and two primality tests on numbers below `n^2 + n`.
* `H2` (the open tail): `1.4 * 10^7 < n` has `a n > 0`. Nothing is known here.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA219023_conjecture_1_R1

/-- The searched range: every `n` with `2732 < n <= 1.4 * 10^7` has a prime `p < n` such that
`n^2 - n + p` and `n^2 + n - p` are both prime (OEIS A219023: the conjecture was verified for `n` up
to `1.4 * 10^7`). -/
def H1 : Prop :=
  ∀ n : ℕ, 2732 < n → n ≤ 14000000 → 0 < OeisA219023.a n

/-- The open tail: every `n > 1.4 * 10^7` has such a prime `p < n`. This range contains Oppermann's
conjecture, so no argument is known for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 14000000 < n → 0 < OeisA219023.a n

theorem main : H1 → H2 → type_of% @OeisA219023.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 14000000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA219023_conjecture_1_R1
