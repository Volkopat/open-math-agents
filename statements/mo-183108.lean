import Mathlib

/-!
# MathOverflow 183108: does `binomial(2n, n) ≡ 2 (mod p)` hold for a prime `p = 2n(n-1) + 1`?

Source: https://mathoverflow.net/questions/183108
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question: are there any primes of the form `p = 2n(n-1) + 1`, with integer `n ≥ 1`, such that
`binomial(2n, n) ≡ 2 (mod p)`? None exists with `p ≤ 2·10^10` (an answer extends the search to
`n ≤ 10^6`), and the asker's heuristic gives probability below `5·10^-6` that one exists.

We state the expected (negative) answer: no such prime exists. A disproof of `main` exhibits one.

Conventions: `n : ℕ` with `n ≥ 1` as in the source (`n = 1` gives `p = 1`, not prime);
`2n(n-1)` uses natural subtraction, exact since `n ≥ 1`. The congruence is `Nat.ModEq`.
-/

namespace OMA.S_mo_183108

/-- No `n ≥ 1` makes `p = 2n(n-1) + 1` prime with `binomial(2n, n) ≡ 2 (mod p)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (2 * n * (n - 1) + 1).Prime →
    ¬ (Nat.choose (2 * n) n ≡ 2 [MOD 2 * n * (n - 1) + 1]) := by
  sorry

end OMA.S_mo_183108
