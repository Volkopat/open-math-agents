import Mathlib

/-!
# A group-theoretic perspective on Frankl's union closed problem

Source: https://mathoverflow.net/questions/154025
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (MathOverflow): given a finite group `G`, is there an element of prime power order which
is contained in at most half the subgroups of `G`?

Conventions:
* `G` is nontrivial (for the trivial group the only element has order `1` and lies in every
  subgroup; Frankl's conjecture likewise excludes the one-element lattice). Elements of prime
  power order are taken with order `p^k`, `k ≥ 1`, i.e. nonidentity elements of prime power
  order, matching the join irreducibles of the subgroup lattice.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_154025

theorem main :
    ∀ (G : Type) [Group G] [Finite G], Nontrivial G →
      ∃ g : G, (∃ p k : ℕ, p.Prime ∧ 1 ≤ k ∧ orderOf g = p ^ k) ∧
        2 * Nat.card {H : Subgroup G // g ∈ H} ≤ Nat.card (Subgroup G) := by
  sorry

end OMA.S_mo_154025
