import Mathlib

/-!
# A strengthening of the union-closed sets conjecture

Fabius Wiesner asks whether every finite union-closed family with more than
one member has a nonempty difference of two members that is contained in at
least half the family. The theorem states this conjecture.

Source: https://mathoverflow.net/questions/480370
Lean statement by @jacklarmer.
-/

namespace OMA.S_mo_480370

universe u

theorem main :
    ∀ (α : Type u) [DecidableEq α] (F : Finset (Finset α)),
      1 < F.card →
      (∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) →
      ∃ A ∈ F, ∃ B ∈ F, (A \ B).Nonempty ∧
        F.card ≤ 2 * (F.filter (fun C => (A \ B) ⊆ C)).card := by
  sorry

end OMA.S_mo_480370
