import Mathlib

/-!
# A098530: Solid partitions of n+1 shrinkable to a solid partition of n in k ways

Source: https://oeis.org/A098530
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

T(n, k) counts solid partitions of n+1 that can be shrunk in k ways to a solid partition of n
by removing 1 element from it.
Conjecture: The first column T(n, 1) equals the beheaded A007426, i.e. tau_4(n+1).
-/

namespace OMA.S_oeis_a098530

def IsSolidPartition (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  S.card = n ∧
  ∀ a b c d a' b' c' d', (a, b, c, d) ∈ S →
    a' ≤ a → b' ≤ b → c' ≤ c → d' ≤ d → (a', b', c', d') ∈ S

noncomputable def numShrinkings (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  Set.ncard {T : Finset (ℕ × ℕ × ℕ × ℕ) | IsSolidPartition n T ∧ T ⊆ S}

noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {S : Finset (ℕ × ℕ × ℕ × ℕ) | IsSolidPartition (n + 1) S ∧ numShrinkings n S = k}

noncomputable def tau4 (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ |
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
    t.1 * t.2.1 * t.2.2.1 * t.2.2.2 = n}

theorem main :
    ∀ n : ℕ, 1 ≤ n → T n 1 = tau4 (n + 1) := by
  sorry

end OMA.S_oeis_a098530
