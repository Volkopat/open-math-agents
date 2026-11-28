import FormalConjectures.OEIS.«233566»

-- Reduction OeisA233566.conjecture_2.R1 of a prime p < n with p^2 * phi(n - p) - 1 prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# `p ^ 2 * phi(n - p) - 1` prime: the computed range and the open tail

The conjecture is that for every `n > 2` there is a prime `p < n` with `p ^ 2 * phi (n - p) - 1`
also prime, with `phi` Euler's totient. It is the companion of the count `a n` of A233566 in the
same entry, with one more factor `p`, and no table of witnesses accompanies it: the entry carries
Sun's table of `a(n)` for `n = 1..10000`, which settles nothing about this statement.

For a fixed `n` the statement is a finite search over the primes `p < n`, so every single `n` is
decided by computation (searching `p` upwards finds a witness; here every `3 <= n <= 10000` was
checked). What is open is a uniform argument, and no argument is known for a product of a prime
square with a totient.

Beyond a finite search there is no proof, so the conjecture splits at a bound that has been
searched in full:

* `H1` (searched range): `2 < n <= 10000` has a prime `p < n` with `p ^ 2 * phi (n - p) - 1`
  prime. Finite: for each `n` at most `pi n` numbers below `n ^ 3`.
* `H2` (the open tail): `10000 < n` has such a prime `p < n`. Nothing is known here: it contains
  the infinitude of primes of this shape, which is open.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA233566_conjecture_2_R1

/-- The searched range: every `n` with `2 < n <= 10000` has a prime `p < n` with
`p ^ 2 * phi (n - p) - 1` prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 10000 →
    ∃ p < n, p.Prime ∧ Nat.Prime (p ^ 2 * (n - p).totient - 1)

/-- The open tail: every `n > 10000` has such a prime `p < n`. Nothing is known here, so no
argument is available for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n →
    ∃ p < n, p.Prime ∧ Nat.Prime (p ^ 2 * (n - p).totient - 1)

theorem main : H1 → H2 → type_of% @OeisA233566.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA233566_conjecture_2_R1
