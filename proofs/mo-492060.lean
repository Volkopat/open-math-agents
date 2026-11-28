import OMAStatements.S_mo_492060
import Mathlib
-- Credit: @ptc-prover-bot

/-!
Disproof for n = 4, k = 3 (ground set of 7 points). Take the Fano plane on 0, ..., 6 with lines
012, 034, 056, 135, 146, 236, 245 and delete the line 012. The six remaining lines are 3-sets,
meet pairwise (any two Fano lines meet), cover every point, and every 5-set contains one of them:
its complement is a pair, at most 5 of the 7 Fano lines meet that pair, so at least 2 lines avoid
it and at least one of them survives. But the pair 01 lies in no remaining line, so the family is
not a Steiner system S(2, 3, 7). All checks are finite and done by decide.
-/

namespace MO492060Disproof

open OMA.S_mo_492060

/-- The Fano plane without the line 012. -/
def F : Family (2 * 4 - 1) :=
  {{0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

theorem F_card : ∀ B ∈ F, B.card = 3 := by decide +kernel

theorem F_inter : ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty := by decide +kernel

theorem F_cover5 : ∀ X : Finset (Fin (2 * 4 - 1)), X.card = 2 * 4 - 3 → ∃ B ∈ F, B ⊆ X := by
  decide +kernel

theorem F_points : ∀ x : Fin (2 * 4 - 1), ∃ B ∈ F, x ∈ B := by decide +kernel

theorem F_adm : admissible 4 3 F := ⟨F_card, F_inter, F_cover5, F_points⟩

theorem F_pair : ∀ B ∈ F, ¬ ({0, 1} : Finset (Fin (2 * 4 - 1))) ⊆ B := by decide +kernel

theorem not_steiner : ¬ steiner 3 F := by
  intro h
  obtain ⟨B, ⟨hB, hX⟩, _⟩ := h {0, 1} (by decide)
  exact F_pair B hB hX

theorem not_main : ¬ (∀ (n k : ℕ), 1 ≤ n → 1 ≤ k → k ≤ n - 1 →
    ∀ F : Family (2 * n - 1), admissible n k F → steiner k F) := by
  intro h
  exact not_steiner (h 4 3 (by norm_num) (by norm_num) (by norm_num) F F_adm)

end MO492060Disproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_492060.main) := MO492060Disproof.not_main

