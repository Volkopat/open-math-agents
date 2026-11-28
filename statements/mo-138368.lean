import Mathlib

/-!
# Tarski monster group with prime 5

Source: https://mathoverflow.net/questions/138368
Does a Tarski monster group for the prime `5` exist, i.e. an infinite group every nontrivial
proper subgroup of which has order `5`? (Olshanskii constructed them for all primes
`p > 10^75`; for `p = 2, 3` they do not exist.) `main` states that one exists.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_138368

theorem main :
    ∃ (G : Type) (_ : Group G), Infinite G ∧
      ∀ H : Subgroup G, H ≠ ⊥ → H ≠ ⊤ → Nat.card H = 5 := by
  sorry

end OMA.S_mo_138368
