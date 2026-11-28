import Mathlib

/-!
# OEIS A036913: sparsely totient numbers are Zumkeller

Source: https://oeis.org/A036913
Sparsely totient numbers: `n` such that `m > n` implies `φ(m) > φ(n)`
(2, 6, 12, 18, 30, …). Conjecture: except for `2` and `18`, all terms are Zumkeller numbers
(A083207): the divisors of `n` can be partitioned into two sets with equal sums.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a036913

/-- `n` is sparsely totient. -/
def IsSparselyTotient (n : ℕ) : Prop := 1 ≤ n ∧ ∀ m : ℕ, n < m → n.totient < m.totient

/-- `n` is a Zumkeller number. -/
def IsZumkeller (n : ℕ) : Prop :=
  ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d

theorem main :
    ∀ n : ℕ, IsSparselyTotient n → n ≠ 2 → n ≠ 18 → IsZumkeller n := by
  sorry

end OMA.S_oeis_a036913
