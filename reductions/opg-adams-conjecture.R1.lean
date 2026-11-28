import OMAStatements.S_opg_adams_conjecture
import Mathlib

/-!
Reduction opg-adams-conjecture.R1: Ádám's conjecture for tournaments, split by degrees.

H1 is the case of tournaments having a vertex of in-degree 1 or out-degree 1 that lies on a
directed cycle. Reversing its unique in-arc (out-arc) turns it into a source (sink); then every
cycle of the new tournament is a cycle of the old one, and the old cycles through that vertex are
lost, so the number of cycles drops. This is an easy known case, not progress on the conjecture.
H2 is the open remainder: non-transitive tournaments in which no vertex lying on a directed cycle
has in-degree 1 or out-degree 1 (for instance all strong tournaments of minimum semidegree 2).
-/

namespace OMA.R_opg_adams_conjecture_R1

open OMA.S_opg_adams_conjecture (cycles reverse)

/-- Ádám's conjecture for tournaments with a vertex of in- or out-degree one on a cycle. -/
def H1 : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Prop),
    (∀ i, ¬ adj i i) → (∀ i j, i ≠ j → (adj i j ↔ ¬ adj j i)) →
    ¬ (∀ x y z, adj x y → adj y z → adj x z) →
    (∃ b, (∃ C ∈ cycles adj, ∃ p ∈ C, p.1 = b) ∧
      ((∃ a, ∀ x, adj x b ↔ x = a) ∨ (∃ c, ∀ y, adj b y ↔ y = c))) →
    ∃ a b, adj a b ∧ (cycles (reverse adj a b)).ncard < (cycles adj).ncard

/-- The open remainder: no vertex on a directed cycle has in-degree 1 or out-degree 1. -/
def H2 : Prop :=
  ∀ (n : ℕ) (adj : Fin n → Fin n → Prop),
    (∀ i, ¬ adj i i) → (∀ i j, i ≠ j → (adj i j ↔ ¬ adj j i)) →
    ¬ (∀ x y z, adj x y → adj y z → adj x z) →
    ¬ (∃ b, (∃ C ∈ cycles adj, ∃ p ∈ C, p.1 = b) ∧
      ((∃ a, ∀ x, adj x b ↔ x = a) ∨ (∃ c, ∀ y, adj b y ↔ y = c))) →
    ∃ a b, adj a b ∧ (cycles (reverse adj a b)).ncard < (cycles adj).ncard

theorem main : H1 → H2 → type_of% @OMA.S_opg_adams_conjecture.main := by
  intro h1 h2 n adj hirr htour hnt
  by_cases h : ∃ b, (∃ C ∈ cycles adj, ∃ p ∈ C, p.1 = b) ∧
      ((∃ a, ∀ x, adj x b ↔ x = a) ∨ (∃ c, ∀ y, adj b y ↔ y = c))
  · exact h1 n adj hirr htour hnt h
  · exact h2 n adj hirr htour hnt h

end OMA.R_opg_adams_conjecture_R1
