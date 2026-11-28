import FormalConjectures.ErdosProblems.«881»
import Mathlib

/-! Reduction Erdos881.erdos_881.R1. Erdos asked whether every minimal asymptotic additive basis A
of order k (no infinite B inside A can be removed keeping a basis of order k) has an infinite
B inside A with A minus B an asymptotic basis of order k + 1. H1 is the case of order at most
one. No set of naturals is an asymptotic basis of order 0, and an asymptotic basis of order 1 is
a cofinite set A: removing B, the multiples of 3 above the threshold, leaves every large number
prime to 3, and every large n is a sum of two such numbers (residues 1 + 2, 2 + 2 and 1 + 1 for n
congruent to 0, 1 and 2 mod 3). H2 is the open rest: minimal bases of order at least 2. -/

namespace OMA.R_Erdos881_erdos_881_R1

/-- Minimal asymptotic bases of order at most one. -/
def H1 : Prop :=
  ∀ (k : ℕ) (A : Set ℕ), Erdos881.IsMinimalAsymptoticAddBasisOfOrder k A → k ≤ 1 →
    ∃ (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder (k + 1)

/-- The open core: minimal asymptotic bases of order at least two. -/
def H2 : Prop :=
  ∀ (k : ℕ) (A : Set ℕ), Erdos881.IsMinimalAsymptoticAddBasisOfOrder k A → 2 ≤ k →
    ∃ (B : Set ℕ), B ⊆ A ∧ B.Infinite ∧ (A \ B).IsAsymptoticAddBasisOfOrder (k + 1)

theorem main : H1 → H2 → type_of% @Erdos881.erdos_881 := by
  intro h1 h2 k A hA
  rcases Nat.lt_or_ge k 2 with hk | hk
  · exact h1 k A hA (by omega)
  · exact h2 k A hA hk

end OMA.R_Erdos881_erdos_881_R1
