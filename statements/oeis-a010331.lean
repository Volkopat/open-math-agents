import Mathlib

/-!
# A010331: Numbers expressible as C(m, 5) + C(n, 5) in at least 2 ways

Source: https://oeis.org/A010331
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
No additional solutions to `C(m₁, 5) + C(n₁, 5) = C(m₂, 5) + C(n₂, 5)` exist beyond those
with `n ≤ m ≤ 25000`. That is, there are no two distinct pairs `(m₁, n₁)` and `(m₂, n₂)`
with `4 ≤ n₁ ≤ m₁`, `4 ≤ n₂ ≤ m₂`, and `m₁ > 25000` having the same sum `C(m, 5) + C(n, 5)`.

Conventions:
- A summand `C(n, 5) = 0` is allowed (the first term `252 = C(10, 5) + 0 = C(9, 5) + C(9, 5)`
  uses it); `n = 4` is its single representative. We restrict to `4 ≤ n ≤ m`, so
  `m ↦ Nat.choose m 5` is injective on the allowed range.
-/

namespace OMA.S_oeis_a010331

theorem main :
    ∀ m₁ n₁ m₂ n₂ : ℕ,
      4 ≤ n₁ → n₁ ≤ m₁ → 4 ≤ n₂ → n₂ ≤ m₂ →
      m₁ > 25000 → (m₁, n₁) ≠ (m₂, n₂) →
      Nat.choose m₁ 5 + Nat.choose n₁ 5 ≠ Nat.choose m₂ 5 + Nat.choose n₂ 5 := by
  sorry

end OMA.S_oeis_a010331
