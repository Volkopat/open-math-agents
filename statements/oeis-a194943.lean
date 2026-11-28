import Mathlib

/-!
# OEIS A194943: Granville–Pomerance lower bound for least primes in progressions

Source: https://oeis.org/A194943
`a n` is the greatest `d` such that `d n + b` is the least prime in the progression
`k n + b` for some `0 < b < n` with `gcd(b, n) = 1`. Granville and Pomerance conjecture
`a(n) ≫ log(n)² φ(n)/n`.

Conventions. For `n ≥ 2` and `b` coprime to `n`, `leastPrime n b` is the least prime of the
form `k n + b` (`k ≥ 0`; it exists by Dirichlet's theorem) and `a n` is the maximum of
`(leastPrime n b - b)/n` over `0 < b < n` coprime to `n`. `≫` means: some `c > 0` has
`a n ≥ c log(n)² φ(n)/n` for all large `n`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a194943

open Filter Real

/-- The least prime `≡ b (mod n)` of the form `k n + b`, `k ≥ 0`. -/
noncomputable def leastPrime (n b : ℕ) : ℕ := sInf {p | p.Prime ∧ b ≤ p ∧ n ∣ p - b}

/-- A194943. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun b => 0 < b ∧ Nat.Coprime b n).sup
    fun b => (leastPrime n b - b) / n

theorem main :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * log n ^ 2 * (n.totient : ℝ) / n ≤ a n := by
  sorry

end OMA.S_oeis_a194943
