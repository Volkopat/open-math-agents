import Mathlib

/-!
# Conjectured weighted geometric mean inequality for three positive reals

Source: https://math.stackexchange.com/questions/1955917/i-conjecture-3aabbcc-frac1abc-ge-aabb-frac1abbbcc
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: For all positive real numbers `a, b, c > 0`,
`3 (a^a b^b c^c)^(1 / (a + b + c)) ≥ (a^a b^b)^(1 / (a + b)) + (b^b c^c)^(1 / (b + c)) + (c^c a^a)^(1 / (c + a))`.
-/

namespace OMA.S_mse_1955917

theorem main :
    ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      3 * (a ^ a * b ^ b * c ^ c) ^ (1 / (a + b + c)) ≥
        (a ^ a * b ^ b) ^ (1 / (a + b)) +
        (b ^ b * c ^ c) ^ (1 / (b + c)) +
        (c ^ c * a ^ a) ^ (1 / (c + a)) := by
  sorry

end OMA.S_mse_1955917
