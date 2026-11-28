import Mathlib

/-!
# Frankl's conjecture for infinite lattices

Source: https://mathoverflow.net/questions/473997
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Frankl's union-closed sets conjecture is equivalent to: in every nontrivial finite lattice `L`
there is a nonempty meet-irreducible ideal `I ∈ 𝓜(𝓘(L))` with `|I| ≤ |L ∖ I|`. The question asks
whether the following generalization has a counterexample:

  In any nontrivial lattice `L` satisfying the descending chain condition, there exists a
  nonempty meet-irreducible ideal `I ∈ 𝓜(𝓘(L))` such that `|I| ≤ |L ∖ I|`.

`main` states this generalization (the question's other, chain-based variant is not included).

Conventions:
* Nontrivial means `|L| ≥ 2` (`Nontrivial L`). The descending chain condition is
  `WellFoundedLT L` (no infinite strictly descending chain).
* Ideals are Mathlib's `Order.Ideal L`: nonempty, directed lower sets, i.e. nonempty lower sets
  closed under binary joins. They form a lattice; (finitely) meet-irreducible is `InfIrred`
  (not the top ideal, and `I = J ⊓ K` forces `I = J` or `I = K`).
* Sizes are cardinalities, `Cardinal.mk`.
-/

namespace OMA.S_mo_473997

/-- The descending-chain-condition generalization of Frankl's conjecture to lattices. -/
theorem main : ∀ (L : Type) [Lattice L] [WellFoundedLT L] [Nontrivial L],
    ∃ I : Order.Ideal L, InfIrred I ∧
      Cardinal.mk (I : Set L) ≤ Cardinal.mk ((I : Set L)ᶜ : Set L) := by
  sorry

end OMA.S_mo_473997
