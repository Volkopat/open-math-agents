import FormalConjectures.OEIS.«238281»

-- Reduction OeisA238281.conjecture_3 of Equal prime counts in adjacent intervals $(kn, (k+1)n)$ and $((k+1)n, (k+2)n)$ — conjecture 3
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for three equally populated consecutive intervals

Sun's conjecture (ii) in A238281: for every `n > 4` there is `k` with `0 < k < p_n` (where `p_n` is
the `n`-th prime) such that the intervals `(kn, (k+1)n)`, `((k+1)n, (k+2)n)` and
`((k+2)n, (k+3)n)` contain the same number of primes, i.e.
`pi ((k+1)n) - pi (kn)`, `pi ((k+2)n) - pi ((k+1)n)` and `pi ((k+3)n) - pi ((k+2)n)` are equal.
For `n >= 2` the endpoints `kn` are composite, so the half-open counts `pi ((k+1)n) - pi (kn)`
that the Lean statement uses are the counts of primes in the open intervals.

For a fixed `n` the condition is a finite search: at most `p_n - 1` values of `k`, each decided by
four values of `pi` at multiples of `n`. I recomputed the sequence `a(n)` of the entry (the number
of `0 < k < n` with the first two counts equal) for `n <= 200` and it agrees with the OEIS b-file
term by term, so this is the condition the entry means; then I ran the three-interval search over
`5 <= n <= 2000` and every `n` there has a witness (the largest smallest witness is `k = 3770` at
`n = 1785`, where `p_n = 15287`).

What stays open is uniformity in `n`. The prime number theorem fixes the size of each interval's
count only up to an error term larger than the differences between neighbouring intervals, and
nothing known forces three consecutive counts to coincide for every `n`; the condition is
self-similar in `n` in no obvious way.

* `H1` (checked range): every `n` with `4 < n <= 2000` has such a `k < p_n`. Finite: an exhaustive
  scan of `k = 1 .. p_n - 1` against a sieve of `pi` up to `(p_n + 3) n`.
* `H2` (the open tail): every `n > 2000` has such a `k < p_n`. This is the whole difficulty: no
  error term for `pi` on short intervals is small enough to produce an exact equality.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA238281_conjecture_3_R1

/-- The checked range: every `n` with `4 < n <= 2000` has `k` with `0 < k < p_n` for which the
prime counts in `(kn, (k+1)n)`, `((k+1)n, (k+2)n)` and `((k+2)n, (k+3)n)` are equal (exhaustive
search over `k < p_n` for every `n = 5..2000`, using a sieve for `pi` up to `(p_n + 3) n`). -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 2000 →
    ∃ k : ℕ, 0 < k ∧ k < Nat.nth Nat.Prime (n - 1) ∧
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) =
        Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) ∧
      Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) =
        Nat.primeCounting ((k + 3) * n) - Nat.primeCounting ((k + 2) * n)

/-- The open tail: every `n > 2000` has `k` with `0 < k < p_n` for which those three prime counts
are equal. Nothing is known here: the error term of the prime number theorem on intervals of
length `n` around `kn` exceeds the size of the differences that have to vanish. -/
def H2 : Prop :=
  ∀ n : ℕ, 2000 < n →
    ∃ k : ℕ, 0 < k ∧ k < Nat.nth Nat.Prime (n - 1) ∧
      Nat.primeCounting ((k + 1) * n) - Nat.primeCounting (k * n) =
        Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) ∧
      Nat.primeCounting ((k + 2) * n) - Nat.primeCounting ((k + 1) * n) =
        Nat.primeCounting ((k + 3) * n) - Nat.primeCounting ((k + 2) * n)

theorem main : H1 → H2 → type_of% @OeisA238281.conjecture_3 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 2000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA238281_conjecture_3_R1
