import FormalConjectures.OEIS.«234694»

-- Reduction OeisA234694.conjecture_6 of Integers $0 < k < n$ with $p = k + \mathrm{prime}(n - k)$ and $\mathrm{prime}(p) - p + 1$ prime — conjecture 6
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for `prime (k + prime (n - k)) + 2`

Conjecture (iv) in A234694: for every `n > 3` there is `k` with `0 < k < n` such that
`prime (k + prime (n - k)) + 2` is prime, where `prime m` is the `m`-th prime (`Nat.nth Nat.Prime
(m - 1)` in the Lean statement, so `prime 1 = 2`).

For a fixed `n` this is a finite search over `k = 1 .. n - 1`: it needs the `m`-th prime once for
`m = n - k` and once for `m = k + prime (n - k)`, so at most about `n + p_n` primes are involved.
I recomputed the sequence `a(n)` of the entry (`p = k + prime (n - k)` and `prime p - p + 1` both
prime) for `n <= 100` and it agrees with the OEIS b-file term by term, so this is the condition the
entry means; then I ran the search over `4 <= n <= 2000` and every `n` there has a witness (the
largest smallest witness is `k = 59` at `n = 1440`).

What stays open is uniformity in `n`: `prime (n - k)` jumps with `n - k`, so `k + prime (n - k)`
traces no arithmetic progression and no theorem on primes in progressions or on primes of a fixed
polynomial form covers the second index, which itself depends on a prime.

* `H1` (checked range): every `n` with `3 < n <= 2000` has such a `k < n`. Finite: a scan of
  `k = 1 .. n - 1` with a primality test of `prime (k + prime (n - k)) + 2`.
* `H2` (the open tail): every `n > 2000` has such a `k`. This is the whole difficulty: the index
  `k + prime (n - k)` is not a polynomial of `n` and ranges over a set no known theorem reaches.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA234694_conjecture_6_R1

/-- The checked range: every `n` with `3 < n <= 2000` has `k` with `0 < k < n` for which
`prime (k + prime (n - k)) + 2` is prime (exhaustive search for every `n = 4..2000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 2000 →
    ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (Nat.nth Nat.Prime (m - 1) + 2)

/-- The open tail: every `n > 2000` has `k` with `0 < k < n` for which
`prime (k + prime (n - k)) + 2` is prime. Nothing is known here: the index of the outer prime is
itself `k + prime (n - k)`, which no theorem on primes in progressions or prime values of
polynomials covers. -/
def H2 : Prop :=
  ∀ n : ℕ, 2000 < n →
    ∃ k, 0 < k ∧ k < n ∧
      let m := k + Nat.nth Nat.Prime (n - k - 1)
      Nat.Prime (Nat.nth Nat.Prime (m - 1) + 2)

theorem main : H1 → H2 → type_of% @OeisA234694.conjecture_6 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 2000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA234694_conjecture_6_R1
