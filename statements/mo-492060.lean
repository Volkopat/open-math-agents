import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Card

/-!
# An intersecting covering family and the Steiner-system conjecture

The source asks whether the three stated hypotheses force a Steiner system
S(k-1,k,2n-1). A block is a k-subset of the ground set. Its labels here start
at zero, which only relabels the ground set.

Source: https://mathoverflow.net/questions/492060
Credit: @LDJAI
-/

namespace OMA.S_mo_492060

abbrev Family (v : ℕ) := Finset (Finset (Fin v))

def admissible (n k : ℕ) (F : Family (2*n-1)) : Prop :=
  (∀ B ∈ F, B.card=k) ∧
  (∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty) ∧
  (∀ X : Finset (Fin (2*n-1)), X.card=2*n-k → ∃ B ∈ F, B ⊆ X) ∧
  (∀ x : Fin (2*n-1), ∃ B ∈ F, x ∈ B)

def steiner {v : ℕ} (k : ℕ) (F : Family v) : Prop :=
  ∀ X : Finset (Fin v), X.card=k-1 → ∃! B : Finset (Fin v), B ∈ F ∧ X ⊆ B

theorem main : ∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n-1 →
    ∀ F : Family (2*n-1), admissible n k F → steiner k F := by
  sorry

end OMA.S_mo_492060
