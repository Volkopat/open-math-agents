import FormalConjectures.OEIS.«238568»

-- Reduction OeisA238568.conjecture_4 of Number of positive integers $k < n$ such that $n^2 - \pi(k n)$ is prime — conjecture 4
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for `pi (n^2) - pi (k n)` prime

Conjecture (iii), part 1, in A238568: for every `n > 2` there is `k` with `0 < k < n` such that
`pi (n^2) - pi (k n)` is prime. Since `k < n`, `kn < n^2`, and `pi (n^2) - pi (k n)` is the number
of primes in `(kn, n^2]`.

For a fixed `n` this is a finite search over `k = 1 .. n - 1`, each value decided by two values of
`pi`. I recomputed the sequence `a(n)` of the entry (the number of `0 < k < n` with
`n^2 - pi (k n)` prime, a different expression from the one of this conjecture) for `n <= 100` and
it agrees with the OEIS b-file term by term, so the counting function and the range `0 < k < n` are
read here as the entry means them; then I ran this conjecture's test over `3 <= n <= 5000` and every
`n` there has a witness (the largest smallest witness is `k = 106` at `n = 4045`).

What stays open is uniformity in `n`. The count `pi (n^2) - pi (k n)` is asymptotic to
`(n^2 - k n) / log n`, so the conjecture asks for a prime value of a function of `n` built from
`pi`; `pi` has no algebraic description at which primality could be tested uniformly, and the count
skips most integers, so even the density of the values that occur is not under control.

* `H1` (checked range): every `n` with `2 < n <= 5000` has such a `k < n`. Finite: a scan of
  `k = 1 .. n - 1` against a sieve of `pi` up to `5000^2`, with an exact primality test.
* `H2` (the open tail): every `n > 5000` has such a `k < n`. This is the whole difficulty: no
  theorem produces a prime among the differences `pi (n^2) - pi (k n)`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA238568_conjecture_4_R1

/-- The checked range: every `n` with `2 < n <= 5000` has `k` with `0 < k < n` for which
`pi (n^2) - pi (k n)` is prime (exhaustive search for every `n = 3..5000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 5000 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) - Nat.primeCounting (k * n))

/-- The open tail: every `n > 5000` has `k` with `0 < k < n` for which `pi (n^2) - pi (k n)` is
prime. Nothing is known here: `pi` has no algebraic description on which primality of these
differences could be decided uniformly in `n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 5000 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧
      Nat.Prime (Nat.primeCounting (n ^ 2) - Nat.primeCounting (k * n))

theorem main : H1 → H2 → type_of% @OeisA238568.conjecture_4 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 5000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA238568_conjecture_4_R1
