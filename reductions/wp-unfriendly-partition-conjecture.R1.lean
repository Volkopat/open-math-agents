import OMAStatements.S_wp_unfriendly_partition_conjecture
import Mathlib

/-!
Classical slice of the unfriendly partition conjecture.

H1 is the classical locally finite case: every graph in which each vertex has finitely many
neighbours has an unfriendly partition (for finite graphs, minimise the number of monochromatic
edges and flip a bad vertex; for infinite locally finite graphs, pass to the limit by Tychonoff
compactness of `V → Bool`). This is a known theorem, not progress on the conjecture.

H2 is the open rest: countable graphs having at least one vertex of infinite degree.
-/

namespace OMA.R_wp_unfriendly_partition_conjecture_R1

open OMA.S_wp_unfriendly_partition_conjecture SimpleGraph

/-- Every locally finite graph has an unfriendly 2-partition. -/
def H1 : Prop :=
  ∀ (V : Type) (G : SimpleGraph V), (∀ v, (G.neighborSet v).Finite) →
    ∃ f : V → Bool, IsUnfriendlyPartition G f

/-- Open rest: countable graphs with some vertex of infinite degree. -/
def H2 : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V), (∃ v, (G.neighborSet v).Infinite) →
    ∃ f : V → Bool, IsUnfriendlyPartition G f

theorem main : H1 → H2 → type_of% @OMA.S_wp_unfriendly_partition_conjecture.main := by
  intro h1 h2 V _ G
  by_cases h : ∀ v, (G.neighborSet v).Finite
  · exact h1 V G h
  · obtain ⟨v, hv⟩ := not_forall.1 h
    exact h2 V G ⟨v, hv⟩

end OMA.R_wp_unfriendly_partition_conjecture_R1
