import Mathlib

/-!
# Does there exist a Jónsson algebra on ℵω?

Source: https://en.wikipedia.org/wiki/Jónsson_cardinal
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Wikipedia, list of unsolved problems in set theory): does there exist a Jónsson
algebra on `ℵ_ω`, i.e. is `ℵ_ω` not a Jónsson cardinal?

Conventions:
* A Jónsson algebra on a set of cardinality `κ` is an algebra with countably many finitary
  operations having no proper subalgebra of cardinality `κ`. As is standard, such an algebra
  exists iff there is `f : [κ]^{<ω} → κ` such that every subset `H` of cardinality `κ` satisfies
  `f[[H]^{<ω}] = κ` (equivalently, `κ` is not a Jónsson cardinal). We state the latter form,
  with `[X]^{<ω}` the finite subsets of a set `X` of cardinality `ℵ_ω`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_does_there_exist_a_jonsson_algebra_on

theorem main :
    ∃ (X : Type) (f : Finset X → X), Cardinal.mk X = Cardinal.aleph Ordinal.omega0 ∧
      ∀ H : Set X, Cardinal.mk H = Cardinal.aleph Ordinal.omega0 →
        ∀ x : X, ∃ s : Finset X, (s : Set X) ⊆ H ∧ f s = x := by
  sorry

end OMA.S_wp_does_there_exist_a_jonsson_algebra_on
