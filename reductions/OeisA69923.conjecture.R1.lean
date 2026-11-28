import FormalConjectures.OEIS.«69923»

-- Reduction OeisA69923.conjecture.R1 of Number of primes $p$ such that $2^n \le p \le 2^n + \mathrm{prime}(n)$
-- Credit: @eltociear
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Primes in the interval [2^n, 2^n + p_n]: the computed range and the open range

The theorem asks whether, for every `n > 0`, the interval `[2 ^ n, 2 ^ n + p_n]` contains at least
one prime, where `p_n` is the `n`-th prime. In the notation of the file that is `1 ≤ a n` for every
`n > 0`, `a n` being the number of primes in the interval.

The OEIS comment on A069923 records the range in which the answer is known: the claim is checked up
to `n = 250`. Above that nothing is known, and the interval is far too short for the prime number
theorem to say anything (its length is `p_n`, of order `n log n`, while the numbers involved have
`n log 2` digits), so the tail is the open part.

* `H1` (computed): at least one prime for every `1 ≤ n ≤ 250`. This is the finite verification
  reported in the OEIS entry. It is a bounded, decidable claim: each instance needs the primality of
  a handful of explicit numbers around `2 ^ n`, which is a finite check for each `n`.
* `H2`: the open part, at least one prime for every `n > 250`.

Neither hypothesis mentions the target, the other one, or `main`; `main` is the case split.
-/

namespace OMA.R_OeisA69923_conjecture_R1

/-- The part checked in the OEIS entry: `1 ≤ n ≤ 250`. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 250 → 1 ≤ OeisA69923.a n

/-- The open part: `250 < n`. -/
def H2 : Prop :=
  ∀ n : ℕ, 250 < n → 1 ≤ OeisA69923.a n

theorem main : H1 → H2 → type_of% @OeisA69923.conjecture := by
  intro h1 h2 n hn
  by_cases h : n ≤ 250
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_OeisA69923_conjecture_R1
