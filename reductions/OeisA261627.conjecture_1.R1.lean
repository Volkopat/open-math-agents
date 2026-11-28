import FormalConjectures.OEIS.«261627»

-- Reduction OeisA261627.conjecture_1.R1 of Primes $p$ such that $n - (p n' - 1)$ and $n + (p n' - 1)$ are both prime — conjecture 1
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Symmetric prime pairs around `n`: the searched range and the open tail

With `n' = 1` for odd `n` and `n' = 2` for even `n`, `a n` counts the primes `p` for which
`k = p * n' - 1` satisfies `k < n` and both `n - k` and `n + k` are prime. Sun's conjecture is that
`a n > 0` for every `n > 6`; it is stronger than Goldbach's conjecture and than Lemoine's.

For a fixed `n` the count is a finite search over the primes `p < n / n'`, so every single `n` is
decided by computation; what is open is a uniform argument, and a proof of the conjecture would give
Goldbach-type statements for all large `n`.

The OEIS entry A261627 records how far the computation was pushed: Sun verified it for `n` up to
`10^8`, Mauro Fiorentini extended that to `n` up to `10^9` (comment of Jul 05 2023), and Jud McCranie
to `n < 1.2 * 10^12` (Aug 26 2023). Beyond a finite search there is no proof, so the conjecture
splits at the published bound `10^9`:

* `H1` (searched range): `6 < n <= 10^9` has `a n > 0`. Finite: for each `n` a search over the
  primes below `n`, and two primality tests on numbers below `2 * 10^9`.
* `H2` (the open tail): `10^9 < n` has `a n > 0`. Nothing is known here.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, with no
upstream lemma, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA261627_conjecture_1_R1

/-- The searched range: every `n` with `6 < n <= 10^9` has a prime `p` with `p * n' - 1 < n` and
`n - (p * n' - 1)`, `n + (p * n' - 1)` both prime (OEIS A261627: verified for `n` up to `10^8` by
Sun, to `10^9` by Mauro Fiorentini in 2023, and to `1.2 * 10^12` by Jud McCranie in 2023). -/
def H1 : Prop :=
  ∀ n : ℕ, 6 < n → n ≤ 1000000000 → 0 < OeisA261627.a n

/-- The open tail: every `n > 10^9` has such a prime. This range contains Goldbach-type statements
for all large `n`, so no argument is known for it. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000000000 < n → 0 < OeisA261627.a n

theorem main : H1 → H2 → type_of% @OeisA261627.conjecture_1 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1000000000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA261627_conjecture_1_R1
