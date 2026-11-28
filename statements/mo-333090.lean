import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Squarefree

/-!
# Which moduli admit an irrational with coprime base-k prefixes?

Source: apple, MathOverflow 333090, June 2, 2019 (CC BY-SA 4.0).
https://mathoverflow.net/questions/333090/

A unit residue has a directed edge labeled d to its next unit residue
after appending the digit d. The condition tests whether two differently
labeled edges from one vertex both stay in its strongly connected component.
All vertices, labels and vertex subsets in the test are finite.
-/

namespace OMA.S_mo_333090

def edge (k M : ℕ) (s : Fin M) (d : Fin k) (t : Fin M) : Prop :=
  s.val.Coprime M ∧ t.val.Coprime M ∧ (k*s.val+d.val)%M = t.val

def reaches (k M : ℕ) (s t : Fin M) : Prop :=
  ∀ S : Finset (Fin M), s ∈ S →
    (∀ u ∈ S, ∀ d : Fin k, ∀ v : Fin M, edge k M u d v → v ∈ S) → t ∈ S

def branching (k M : ℕ) : Prop :=
  ∃ (s u v : Fin M) (d e : Fin k), d ≠ e ∧
    edge k M s d u ∧ reaches k M u s ∧ edge k M s e v ∧ reaches k M v s

theorem main : ∀ k M : ℕ, 2 < k → ¬ Squarefree (k-1) → 0 < M →
    ((∃ x : ℝ, 0 < x ∧ Irrational x ∧
      ∀ n : ℕ, 0 < n → (⌊(k:ℝ)^n*x⌋₊).Coprime M) ↔ branching k M) := by
  sorry

end OMA.S_mo_333090
