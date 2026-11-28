import Mathlib

/-!
# OEIS A076614: power sums of initial primes, 160 is the only repeat

Source: https://oeis.org/A076614
Numbers of the form `2^k + 3^k + ⋯ + p_n^k` (`k, n ≥ 1`). Conjecture: `160` is the only number
that appears twice: `2 + 3 + ⋯ + 31 = 160 = 2³ + 3³ + 5³`.

Conventions. `S k n = ∑_{i < n} p_{i+1}^k` with `p_1 = 2`. "Appears twice" means `S k n = S k' n'`
for two different pairs `(k, n) ≠ (k', n')`; `main` says that this happens only with value `160`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a076614

/-- `S k n = 2^k + 3^k + ⋯ + p_n^k`. -/
noncomputable def S (k n : ℕ) : ℕ := ∑ i ∈ Finset.range n, Nat.nth Nat.Prime i ^ k

theorem main :
    ∀ k n k' n' : ℕ, 1 ≤ k → 1 ≤ n → 1 ≤ k' → 1 ≤ n' → (k, n) ≠ (k', n') →
      S k n = S k' n' → S k n = 160 := by
  sorry

end OMA.S_oeis_a076614
