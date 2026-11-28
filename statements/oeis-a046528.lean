import Mathlib

/-!
# OEIS A046528: products of distinct Mersenne primes and σ = τ^(a/b)

Source: https://oeis.org/A046528
`A046528` lists the products of distinct Mersenne primes (1, 3, 7, 21, 31, …), a supersequence
of A051281 (`σ(n)` a power of `τ(n)`). Conjecture: these are exactly the `n` with
`σ(n) = τ(n)^(a/b)` for integers `a, b ≥ 1` (e.g. `σ(93) = 128 = 4^(7/2)`).

Conventions. `σ(n) = τ(n)^(a/b)` is stated as `σ(n)^b = τ(n)^a`. A product of distinct
Mersenne primes is `∏_{q ∈ S} q` for a finite set `S` of primes of the form `2^k - 1`
(the empty product gives `1`). `n ≥ 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a046528

/-- `n` is a product of distinct Mersenne primes. -/
def IsProdDistinctMersenne (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ ∃ k : ℕ, q = 2 ^ k - 1) ∧ ∏ q ∈ S, q = n

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (IsProdDistinctMersenne n ↔
        ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ (∑ d ∈ n.divisors, d) ^ b = n.divisors.card ^ a) := by
  sorry

end OMA.S_oeis_a046528
