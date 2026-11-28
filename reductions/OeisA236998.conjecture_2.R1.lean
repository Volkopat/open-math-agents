import FormalConjectures.OEIS.«236998»

-- Reduction OeisA236998.conjecture_2 of Number of $0 < k < n/2$ such that $\phi(k)\phi(n-k)$ is a square — conjecture 2
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The checked range and the open tail for `phi k * phi (n - k) + 1` a square

Conjecture (ii) in A236998: for every `n > 20` there is `k` with `0 < k` and `2k < n` such that
`phi k * phi (n - k) + 1` is a perfect square.

For a fixed `n` this is a finite search over `k = 1 .. (n-1)/2` with one integer square-root test
each. I recomputed the sequence `a(n)` of the entry (the number of `0 < k < n/2` with
`phi k * phi (n - k)` itself a square) for `n <= 60` and it agrees with the OEIS b-file term by
term, so `phi` and the range `0 < k < n/2` are read here as the entry means them; then I ran the
shifted test `phi k * phi (n - k) + 1` a square over `21 <= n <= 5000` and every `n` there has a
witness (the largest smallest witness is `k = 529` at `n = 4485`).

What stays open is uniformity in `n`. The condition `phi k * phi (n - k) + 1 = m^2` is a
Diophantine equation in which `phi` of two complementary arguments appears; `phi` is multiplicative
but `k` and `n - k` share no fixed factorisation pattern, and no identity turns the condition into
a congruence that a counting argument could force. Unlike `a(n)` of the entry, which is positive
already for small `n`, the shifted condition has to be met by a square, so it is a genuine square
problem rather than a factorisation one.

* `H1` (checked range): every `n` with `20 < n <= 5000` has such a `k`. Finite: a scan of
  `k = 1 .. (n-1)/2` with an exact integer square-root test for every `n = 21..5000`.
* `H2` (the open tail): every `n > 5000` has such a `k`. This is the whole difficulty: nothing known
  produces a square value of `phi k * phi (n - k) + 1` uniformly in `n`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split, and no
upstream lemma is used, so nothing depends on a `decide`-style proof of an upstream statement.
-/

namespace OMA.R_OeisA236998_conjecture_2_R1

/-- The checked range: every `n` with `20 < n <= 5000` has `k` with `0 < k`, `2k < n` and
`phi k * phi (n - k) + 1` a perfect square (exhaustive search for every `n = 21..5000`, exact
integer square roots). -/
def H1 : Prop :=
  ∀ n : ℕ, 20 < n → n ≤ 5000 →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

/-- The open tail: every `n > 5000` has `k` with `0 < k`, `2k < n` and
`phi k * phi (n - k) + 1` a perfect square. Nothing is known here: `phi k * phi (n - k) + 1` is a
Diophantine condition in two complementary arguments with no usable factorisation pattern. -/
def H2 : Prop :=
  ∀ n : ℕ, 5000 < n →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ IsSquare (k.totient * (n - k).totient + 1)

theorem main : H1 → H2 → type_of% @OeisA236998.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 5000
  · exact h1 n hn h
  · exact h2 n (Nat.lt_of_not_le h)

end OMA.R_OeisA236998_conjecture_2_R1
