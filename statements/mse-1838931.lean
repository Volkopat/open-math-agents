import Mathlib

/-!
# Primes congruent to factorials

Source: https://math.stackexchange.com/questions/1838931
Conjecture (asker, corrected form): for every prime `p > 5` there is a prime `q < p` with
`q ≡ m! (mod p)` for some `2 < m < p`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mse_1838931

theorem main :
    ∀ p : ℕ, p.Prime → 5 < p →
      ∃ q m : ℕ, q.Prime ∧ q < p ∧ 2 < m ∧ m < p ∧ q ≡ m.factorial [MOD p] := by
  sorry

end OMA.S_mse_1838931
