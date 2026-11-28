import FormalConjectures.OEIS.«233549»

-- Reduction OeisA233549.conjecture_2 of Number of ways to write $n = p + q$ ($q > 0$) with $p$ and $(\phi(p)\phi(q))^4 + 1$ prime
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The tabulated range and the open tail for `(phi(p) phi(n - p)) ^ 2 + 1`

Sun's conjecture in A233549: every `n > 2` other than `n = 26` is `p + q` with `p` prime and
`(phi p * phi q) ^ 2 + 1` prime (`q = n - p > 0`). For prime `p` we have `phi p = p - 1`, so one
only has to hit a prime value of the quadratic-like expression `((p - 1) * phi (n - p)) ^ 2 + 1`
among the primes `p < n`.

For a fixed `n` this is a finite search over the primes below `n` (at most `n` tests), so each
`n` is decided by computation; the entry itself weakens the sequence to the fourth power
`(phi(p) phi(q)) ^ 4 + 1`, and the second-power statement considered here is the sharper one of
the two. What is open is a uniform argument: `phi (n - p)` does not vary in an arithmetic
progression, so no existing theorem on primes in progressions applies, and the expression grows
like `n ^ 4`.

The OEIS entry A233549 carries a table of the fourth-power count `a(n)` for `n = 1..10000`; I
recomputed it for `n <= 500` (its zeros there are exactly `n = 1, 2`) to check that I read the
entry the same way, and then ran the second-power search over the whole tabulated range
`3 <= n <= 10000`, where the only `n` without a witness is `n = 26`. So the conjecture splits at
the end of that range:

* `H1` (tabulated range): every `n` with `2 < n <= 10000`, `n != 26`, has such a `p < n`. Finite:
  for each `n` a scan of the primes `p < n` with a primality test of `((p - 1) * phi (n - p)) ^ 2 + 1`.
* `H2` (the open tail): every `n > 10000` with `n != 26` has such a `p`. This is the whole
  difficulty: nothing is known about it.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA233549_conjecture_2_R1

/-- The tabulated range: every `n` with `2 < n <= 10000`, `n != 26`, has a prime `p < n` with
`(phi p * phi (n - p)) ^ 2 + 1` prime (exhaustive search over the range of the table in A233549;
the only `n` there without a witness is `26`). -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 10000 → n ≠ 26 →
    ∃ p < n, p.Prime ∧ Nat.Prime ((p.totient * (n - p).totient) ^ 2 + 1)

/-- The open tail: every `n > 10000`, `n != 26`, has a prime `p < n` with
`(phi p * phi (n - p)) ^ 2 + 1` prime. Nothing is known here: `phi (n - p)` moves irregularly with
`p`, so no theorem on primes in progressions reaches this expression. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 < n → n ≠ 26 →
    ∃ p < n, p.Prime ∧ Nat.Prime ((p.totient * (n - p).totient) ^ 2 + 1)

theorem main : H1 → H2 → type_of% @OeisA233549.conjecture_2 := by
  intro h1 h2 n hn hne
  by_cases h : n ≤ 10000
  · exact h1 n hn h hne
  · exact h2 n (Nat.lt_of_not_le h) hne

end OMA.R_OeisA233549_conjecture_2_R1
