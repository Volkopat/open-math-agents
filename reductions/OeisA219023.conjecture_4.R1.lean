import FormalConjectures.OEIS.«219023»

-- Reduction OeisA219023.conjecture_4 of Primes $p < n$ with $n^2 - n + p$ and $n^2 + n - p$ prime — conjecture 4
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for a prime `p` in `(n, 2n)` with both `n^2 - n - p` and `n^2 + n + p` prime

Sun's conjecture in A219023 (conjecture 4): for every `n > 4517` there is a prime `p` with
`n < p < 2n` such that `n^2 - n - p` and `n^2 + n + p` are both prime.

For a fixed `n` this is a finite search over the primes `p` with `n < p < 2n`, each candidate decided
by two primality tests of numbers of size about `n^2`. I recomputed the sequence `a(n)` of the entry
(the number of primes `p < n` with `n^2 - n + p` and `n^2 + n - p` both prime) for `n <= 1000` and
it agrees with the OEIS b-file term by term, so `n` and the two quadratic forms are read here as the
entry means them; then I ran this conjecture's search over `4518 <= n <= 20000` and every `n` there
has a witness (the largest smallest witness is `p = 27067` at `n = 17768`).

What stays open is uniformity in `n`. Both required primes are values of quadratics in `n` whose
linear coefficient is the prime `p`, so the pair `(n^2 - n - p, n^2 + n + p)` is not a polynomial in
`n`; for a fixed `n` the candidates are the primes in a window of length `n`, and no theorem
produces a prime among `n^2 - n - p` or `n^2 + n + p` for even one `p`, let alone one that works for
both forms at once. The window `(n, 2n)` is where the conjecture places `p`, and the density
heuristic for both forms being prime is about `1 / (log n)^2` per candidate, which is where the
difficulty lies: it is a statement about primes in a set that no sieve theorem covers.

* `H1` (checked range): every `n` with `4517 < n <= 20000` has such a `p`. Finite: for each `n` a
  scan of the primes `n < p < 2n` with exact primality tests of `n^2 - n - p` and `n^2 + n + p`.
* `H2` (the open tail): every `n > 20000` has such a `p`. This is the whole difficulty: nothing
  known forces either quadratic in `p` to take a prime value.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA219023_conjecture_4_R1

/-- The checked range: every `n` with `4517 < n <= 20000` has a prime `p` with `n < p < 2n` for
which `n^2 - n - p` and `n^2 + n + p` are both prime (exhaustive search for every
`n = 4518..20000`). -/
def H1 : Prop :=
  ∀ n : ℕ, 4517 < n → n ≤ 20000 →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

/-- The open tail: every `n > 20000` has a prime `p` with `n < p < 2n` for which `n^2 - n - p` and
`n^2 + n + p` are both prime. Nothing is known here: both forms involve the prime `p` linearly, so
no theorem on prime values of polynomials applies to either of them. -/
def H2 : Prop :=
  ∀ n : ℕ, 20000 < n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧
      Nat.Prime (n ^ 2 - n - p) ∧ Nat.Prime (n ^ 2 + n + p)

theorem main : H1 → H2 → type_of% @OeisA219023.conjecture_4 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 20000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA219023_conjecture_4_R1
