import FormalConjectures.OEIS.«53000»

-- Reduction OeisA53000.conjecture.R1 of $a(n) = (\text{smallest prime} > n^2) - n^2$
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The bound `a(n) <= 1 + phi(n)`: the tabulated range and the open tail

`a n` is the distance from `n ^ 2` to the next prime, the smallest prime strictly above `n ^ 2`
minus `n ^ 2`. Luo's conjecture is that `a n <= 1 + phi n` for every `n > 0`, which would improve
Oppermann's conjecture (`a n < n`): the gap to the next prime after `n ^ 2` would stay below the
number of integers up to `n` coprime to `n`.

For a fixed `n` the value is a finite search (sieve `n ^ 2`, `n ^ 2 + 1`, ... until a prime shows
up), so each single `n` is decided by computation; what is open is a uniform argument, and the
honest bound behind Legendre's conjecture is not known.

The OEIS entry A053000 carries a table of `a(n)` for `n = 0..10000` (b-file, T. D. Noe), and
together with `phi` from A000010 that table verifies `a(n) <= 1 + phi(n)` on `1 <= n <= 10000`.
Beyond a finite search no argument is known, so the conjecture splits at the end of the tabulated
range:

* `H1` (tabulated range): `0 < n <= 10000` has `a n <= 1 + phi n`. Finite: 10000 comparisons,
  each one a prime search below `n ^ 2 + 1 + phi n`.
* `H2` (the open tail): `10000 < n` has `a n <= 1 + phi n`. Nothing is known here; it contains
  the statement that there is always a prime between `n ^ 2` and `(n + 1) ^ 2` (Legendre), which
  is still open.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA53000_conjecture_R1

/-- The tabulated range: every `n` with `0 < n <= 10000` satisfies `a n <= 1 + phi n`
(OEIS A053000: b-file of `a(n)` for `n = 0..10000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 10000 → OeisA53000.a n ≤ 1 + n.totient

/-- The open tail: every `n > 10000` satisfies `a n <= 1 + phi n`. This range contains the (open)
statement that there is always a prime between `n ^ 2` and `(n + 1) ^ 2`, so no argument is known
for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → OeisA53000.a n ≤ 1 + n.totient

theorem main : H1 → H2 → type_of% @OeisA53000.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA53000_conjecture_R1
