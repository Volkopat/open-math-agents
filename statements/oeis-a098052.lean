import Mathlib

/-!
# A098052: Solid partitions of n extendable to a solid partition of n+1 in k+3 ways

Source: https://oeis.org/A098052
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

T(n, k) counts the solid partitions of n that can be extended to a solid partition of n+1
in exactly k+3 ways (k >= 1).
Conjecture: The first column T(n, 1) (solid partitions extendable in 4 ways) equals
A007426(n) = tau_4(n), the number of ordered 4-factorizations of n.
-/

namespace OMA.S_oeis_a098052

def IsSolidPartition (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)) : Prop :=
  S.card = n ∧
  ∀ a b c d a' b' c' d', (a, b, c, d) ∈ S →
    a' ≤ a → b' ≤ b → c' ≤ c → d' ≤ d → (a', b', c', d') ∈ S

noncomputable def numExtensions (n : ℕ) (S : Finset (ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  Set.ncard {T : Finset (ℕ × ℕ × ℕ × ℕ) | IsSolidPartition (n + 1) T ∧ S ⊆ T}

noncomputable def T (n k : ℕ) : ℕ :=
  Set.ncard {S : Finset (ℕ × ℕ × ℕ × ℕ) | IsSolidPartition n S ∧ numExtensions n S = k + 3}

noncomputable def tau4 (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ × ℕ |
    0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2.1 ∧ 0 < t.2.2.2 ∧
    t.1 * t.2.1 * t.2.2.1 * t.2.2.2 = n}

theorem main :
    ∀ n : ℕ, 1 ≤ n → T n 1 = tau4 n := by
  sorry

end OMA.S_oeis_a098052
