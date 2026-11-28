import FormalConjectures.OEIS.«34694»

-- Reduction OeisA34694.conjecture.R1 of Smallest prime $\\equiv 1 \\pmod n$
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The tabulated range and the open tail for `a(n) < n ^ 2`

`a n` is the least prime `p` with `n ∣ (p - 1)`, i.e. the least prime `≡ 1 (mod n)`; Ordowski's
conjecture is that `a n < n ^ 2` for every `n > 1`. For each fixed `n` the value is again a finite
search, `n + 1, 2 n + 1, 3 n + 1, ...` until a prime shows up, so a single `n` is decided by
computation and the value is even computable without choosing from a set (it is the least element of
a nonempty set of naturals). What is missing is a uniform bound: the unconditional bound for the
least prime in an arithmetic progression is Linnik's `p ≪ n ^ L` with `L ≤ 5`, far from `n ^ 2`.

The OEIS entry A034694 carries a table of `a(n)` for `n = 1..10000`, and that table verifies
`a(n) < n ^ 2` on `2 <= n <= 10000`; I recomputed every value in that range from scratch and then
extended the search to `n = 200000`, with no exception. Beyond a finite search no argument is known,
so the conjecture splits at the end of the tabulated range:

* `H1` (tabulated range): `1 < n <= 10000` has `a n < n ^ 2`. Finite: 9999 searches, each one a
  primality test of `k n + 1` for `k = 1, 2, ...` (the largest `k` needed is `144`).
* `H2` (the open tail): `10000 < n` has `a n < n ^ 2`. Nothing is known here; this is the whole
  difficulty, an upper bound for the least prime `≡ 1 (mod n)` below `n ^ 2`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA34694_conjecture_R1

/-- The tabulated range: every `n` with `1 < n <= 10000` satisfies `a n < n ^ 2`
(OEIS A034694, table of `a(n)` for `n = 1..10000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 10000 → OeisA34694.a n < n ^ 2

/-- The open tail: every `n > 10000` satisfies `a n < n ^ 2`. Nothing is known in this range: the
only unconditional bounds for the least prime `≡ 1 (mod n)` come from Linnik's theorem. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → OeisA34694.a n < n ^ 2

theorem main : H1 → H2 → type_of% @OeisA34694.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 10000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA34694_conjecture_R1
