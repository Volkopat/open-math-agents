import FormalConjectures.OEIS.«228552»

-- Reduction OeisA228552.conjecture.R1 of Square root of the absolute value of the determinant of the prime sum indicator matrix
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The tabulated range and the open tail for `a(n) > 0`

`a n` is the square root of the absolute value of `det M n`, where `M n` is the `n x n` matrix
whose `(i, j)`-entry is `1` when `i + j` is prime and `0` otherwise (`OeisA69191.a n = det M n`).
So `a n > 0` says exactly that `M n` is invertible over the rationals; Sun's conjecture is that
this holds for every `n > 15`. The zeros in the table are `n = 4` and `n = 9, 10, ..., 15`.

The OEIS entry A228552 carries Sun's table of `a(n)` for `n = 1..400`, and the entry A069191 the
matrix determinants up to `n = 500` (Alois P. Heinz). On the tabulated range the statement is a
finite computation: each `a n` is the integer square root of an explicit determinant of a `0/1`
matrix, so every single `n` is settled by arithmetic with no guesswork. I recomputed the
determinants independently modulo several primes (a nonzero residue proves `det M n != 0`, hence
`a n > 0`) for every `n` from `16` to `400`, and recomputed `|det M n|` exactly for `n <= 60`, all
in agreement with the b-file of A228552.

Beyond the table there is no argument at all: `a n > 0` is an assertion about the exact rank of a
matrix whose entries are decided by the primes up to `2 n`, and nothing in the literature
(nor in the OEIS entry) reduces it to a known result. So the conjecture splits where the data ends:

* `H1` (tabulated range): every `n` with `15 < n <= 400` has `a n > 0`. Finite: 385 determinants,
  all nonzero, the range of Sun's table in A228552.
* `H2` (the open tail): every `n > 400` has `a n > 0`. This is the whole difficulty: it is a rank
  statement about the prime-sum matrices for arbitrarily large `n`, and nothing is known about it.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA228552_conjecture_R1

/-- The tabulated range: every `n` with `15 < n <= 400` has `a n > 0`, i.e. the prime-sum
indicator matrix `M n` has nonzero determinant (OEIS A228552, table of `a(n)` for `n = 1..400`). -/
def H1 : Prop :=
  ∀ n : ℕ, 15 < n → n ≤ 400 → OeisA228552.a n > 0

/-- The open tail: every `n > 400` has `a n > 0`. Nothing is known here: it is the rank of the
prime-sum matrix `M n` for arbitrarily large `n`, and no argument (and no table) reaches it. -/
def H2 : Prop :=
  ∀ n : ℕ, 400 < n → OeisA228552.a n > 0

theorem main : H1 → H2 → type_of% @OeisA228552.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 400
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA228552_conjecture_R1
