import OMAReductions.R_wp_unfriendly_partition_conjecture_R1
import Mathlib

/-!
# Aharoni-Milner-Prikry slice of the countable unfriendly partition conjecture

By Aharoni, Milner, and Prikry (1990), every graph in which only finitely many vertices have
infinite degree admits an unfriendly 2-partition (`H1`). This isolates the open countable
unfriendly partition conjecture to countable graphs having infinitely many vertices of infinite
degree (`H2`).
-/

-- Credit: @qu1r0ra

namespace OMA.R_wp_unfriendly_partition_conjecture_R1_H2_R1

open OMA.S_wp_unfriendly_partition_conjecture SimpleGraph

/-- Aharoni-Milner-Prikry (1990): every countable graph with finitely many vertices of infinite
degree admits an unfriendly 2-partition. -/
def H1 : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V),
    ({v : V | (G.neighborSet v).Infinite} : Set V).Finite →
      ∃ f : V → Bool, IsUnfriendlyPartition G f

/-- Open core: countable graphs having infinitely many vertices of infinite degree. -/
def H2 : Prop :=
  ∀ (V : Type) [Countable V] (G : SimpleGraph V),
    ({v : V | (G.neighborSet v).Infinite} : Set V).Infinite →
      ∃ f : V → Bool, IsUnfriendlyPartition G f

theorem main : H1 → H2 → OMA.R_wp_unfriendly_partition_conjecture_R1.H2 := by
  intro hFin hInf V _ G _
  by_cases h : ({v : V | (G.neighborSet v).Infinite} : Set V).Finite
  · exact hFin V G h
  · exact hInf V G h

end OMA.R_wp_unfriendly_partition_conjecture_R1_H2_R1
