import Mathlib

/-!
# Sorli's conjecture on odd perfect numbers

Source: https://math.stackexchange.com/questions/833507
If `N = q^k n²` is an odd perfect number in Eulerian form (`q` prime, `q ≡ k ≡ 1 (mod 4)`,
`gcd(q, n) = 1`), Sorli's conjecture asserts `k = 1`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_833507

theorem main :
    ∀ N q k n : ℕ, Odd N → Nat.Perfect N → q.Prime → q % 4 = 1 → k % 4 = 1 →
      Nat.Coprime q n → N = q ^ k * n ^ 2 → k = 1 := by
  sorry

end OMA.S_mse_833507
