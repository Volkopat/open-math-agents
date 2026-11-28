import Mathlib

/-!
# Nontrivial finite group with trivial group homologies?

Source: https://mathoverflow.net/questions/52552
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Chris Gerig, MathOverflow): does there exist a positive integer `N` such that if `G` is
a finite group with `⊕_{i=1}^{N} H_i(G) = 0` then `G = {1}`?

Conventions:
* `H_i(G)` is integral group homology, `H_i(G; ℤ)` with trivial action (Mathlib's
  `groupHomology` of the trivial representation `ℤ`).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_52552

theorem main :
    ∃ N : ℕ, 0 < N ∧ ∀ (G : Type) [Group G] [Finite G],
      (∀ i : ℕ, 1 ≤ i → i ≤ N → Subsingleton (groupHomology (Rep.trivial ℤ G ℤ) i)) →
        Subsingleton G := by
  sorry

end OMA.S_mo_52552
