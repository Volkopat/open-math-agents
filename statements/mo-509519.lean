import Mathlib

/-!
# Isolation of record prime gaps beyond 3

Source: https://mathoverflow.net/questions/509519 (CC BY-SA).
Credit: @KIRKR101
-/

namespace OMA.S_mo_509519

noncomputable def gap (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 1) - Nat.nth Nat.Prime i

def IsRecord (i : ℕ) : Prop := ∀ j < i, gap j < gap i

theorem main : ∀ i : ℕ, 3 < Nat.nth Nat.Prime i →
    ¬ (IsRecord i ∧ IsRecord (i + 1)) := by
  sorry

end OMA.S_mo_509519
