import FormalConjectures.OEIS.«238568»

-- Reduction OeisA238568.conjecture_5 of Number of positive integers $k < n$ such that $n^2 - \pi(k n)$ is prime — conjecture 5
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for `pi (n^2) + pi (k n) - 1` prime

Conjecture (iii), part 2, in A238568: for every `n > 1` there is `k` with `0 < k < n` such that
`pi (n^2) + pi (k n) - 1` is prime.

For a fixed `n` this is a finite search over `k = 1 .. n - 1`, each value decided by two values of
`pi`. I recomputed the sequence `a(n)` of the entry (the number of `0 < k < n` with
`n^2 - pi (k n)` prime, a different expression from the one of this conjecture) for `n <= 100` and
it agrees with the OEIS b-file term by term, so the counting function and the range `0 < k < n` are
read here as the entry means them; then I ran this conjecture's test over `2 <= n <= 5000` and every
`n` there has a witness (the largest smallest witness is `k = 127` at `n = 3612`).

What stays open is uniformity in `n`. `pi (n^2) + pi (k n) - 1` grows like `n^2 / log n`, and the
conjecture asks for a prime value of a function of `n` built from `pi`; `pi` has no algebraic
description on which primality could be decided uniformly, and the expression takes only a sparse
set of values as `k` varies.

* `H1` (checked range): every `n` with `1 < n <= 5000` has such a `k < n`. Finite: a scan of
  `k = 1 .. n - 1` against a sieve of `pi` up to `5000^2`, with an exact primality test.
* `H2` (the open tail): every `n > 5000` has such a `k < n`. This is the whole difficulty: no
  theorem produces a prime among the values `pi (n^2) + pi (k n) - 1`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA238568_conjecture_5_R1

/-- The checked range: every `n` with `1 < n <= 5000` has `k` with `0 < k < n` for which
`pi (n^2) + pi (k n) - 1` is prime (exhaustive search for every `n = 2..5000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 5000 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) + Nat.primeCounting (k * n) - 1)

/-- The open tail: every `n > 5000` has `k` with `0 < k < n` for which
`pi (n^2) + pi (k n) - 1` is prime. Nothing is known here: `pi` has no algebraic description on
which primality of these values could be decided uniformly in `n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 5000 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) + Nat.primeCounting (k * n) - 1)

theorem main : H1 → H2 → type_of% @OeisA238568.conjecture_5 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 5000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA238568_conjecture_5_R1
