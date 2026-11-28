import Mathlib

/-!
# Ramsey properties of Cayley graphs

Source: https://www.openproblemgarden.org/op/ramsey_properties_of_cayley_graphs
Credit: @ishaanzee

**Conjecture** (N. Alon). There exists a fixed constant `c` so that every abelian group `G` has a
subset `S ⊆ G` with `-S = S` so that the Cayley graph `Cayley(G, S)` has no clique or independent
set of size `> c log |G|`.

Formalization:
* Groups are finite abelian groups (written additively). The trivial group is excluded
  (`|G| ≥ 2`): there `c log |G| = 0` while a single vertex is a clique of size `1`, so the
  statement is meant for nontrivial groups.
* `Cayley(G, S)` has vertex set `G`, with distinct `x`, `y` adjacent when `x - y ∈ S`
  (`SimpleGraph.fromRel` symmetrizes and drops loops; with `-S = S` the relation is already
  symmetric).
* No clique and no independent set has more than `c log |G|` vertices (natural logarithm; the
  choice of base only changes `c`).
-/

namespace OMA.S_opg_ramsey_properties_of_cayley_graphs

/-- The Cayley graph of the additive group `G` with connection set `S`. -/
def cayley {G : Type*} [AddCommGroup G] (S : Set G) : SimpleGraph G :=
  SimpleGraph.fromRel fun x y => x - y ∈ S

/-- **Alon's conjecture.** -/
theorem main : ∃ c : ℝ, ∀ (G : Type) [AddCommGroup G] [Fintype G], 2 ≤ Fintype.card G →
    ∃ S : Set G, (∀ s ∈ S, -s ∈ S) ∧
      (∀ t : Finset G, (cayley S).IsClique (t : Set G) →
        (t.card : ℝ) ≤ c * Real.log (Fintype.card G)) ∧
      (∀ t : Finset G, (cayley S).IsIndepSet (t : Set G) →
        (t.card : ℝ) ≤ c * Real.log (Fintype.card G)) := by
  sorry

end OMA.S_opg_ramsey_properties_of_cayley_graphs
