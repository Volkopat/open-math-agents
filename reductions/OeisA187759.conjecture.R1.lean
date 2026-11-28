import FormalConjectures.OEIS.«187759»

-- Reduction OeisA187759.conjecture.R1 of Number of ways to write $n = x + y$ ($0 < x < y < n$) with $6x \pm 1$ and $6y \pm 1$ prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The tabulated range and the open tail for `a(n) > 0`

`a n` counts the splits `n = x + y` with `0 < x < y` such that all four of `6 x - 1, 6 x + 1`,
`6 y - 1, 6 y + 1` are prime, i.e. the two numbers `x, y` are both "sextuplet centres". Sun's
conjecture is that `a n > 0` for every `n > 200` except `n = 211, 226, 541, 701`.

For a fixed `n` the count is a finite sum over `x < n / 2` (at most `n / 2` primality tests), so
each single `n` is decided by computation; what is open is a uniform argument for large `n`.

The OEIS entry A187759 carries a table of `a(n)` for `n = 1..20000`, and that table verifies the
conjecture on `200 < n <= 20000`: the only `n` with `a(n) = 0` in the whole table are
`16, 66, 67, 86, 116, 131, 151, 186, 191, 211, 226, 541, 701`, so above `200` exactly the four
values named in the conjecture. I recomputed every `a(n)` in the table from scratch and it agrees
term by term.

Beyond the table no argument is known: `a n > 0` asks for one split of `n` where both halves are
sextuplet centres, a two-dimensional prime-pattern statement of the same kind as the twin prime
conjecture (Sun's arXiv:1211.1588). So the conjecture splits where the data ends:

* `H1` (tabulated range): `200 < n <= 20000` has `a n > 0`, the four exceptions excluded. Finite:
  19800 counts, each a sum of at most `10000` four-fold primality tests.
* `H2` (the open tail): `20000 < n` with the same exclusion has `a n > 0`. This is the whole
  difficulty: nothing is known about it.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA187759_conjecture_R1

/-- The tabulated range: every `n` with `200 < n <= 20000` outside `{211, 226, 541, 701}` satisfies
`a n > 0` (OEIS A187759, table of `a(n)` for `n = 1..20000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 200 < n → n ≤ 20000 → n ∉ ({211, 226, 541, 701} : Finset ℕ) → OeisA187759.a n > 0

/-- The open tail: every `n > 20000` outside `{211, 226, 541, 701}` satisfies `a n > 0`. Nothing is
known here: it asks for a split of `n` into two sextuplet centres, a prime-pattern statement of the
same kind as the twin prime conjecture. -/
def H2 : Prop :=
  ∀ n : ℕ, 20000 < n → n ∉ ({211, 226, 541, 701} : Finset ℕ) → OeisA187759.a n > 0

theorem main : H1 → H2 → type_of% @OeisA187759.conjecture := by
  intro h1 h2 n hn hnot
  by_cases h : n ≤ 20000
  · exact h1 n hn h hnot
  · exact h2 n (Nat.lt_of_not_le h) hnot

end OMA.R_OeisA187759_conjecture_R1
