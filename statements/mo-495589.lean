import Mathlib.Data.Rat.Defs

/-! Source: https://mathoverflow.net/questions/495589 -/

namespace OMA.S_mo_495589

/-- The term at source index n + 1, using the defining sum recurrence. -/
def weighted (k l : ℕ) : ℕ → ℚ
  | 0 => l
  | n + 1 => (n + 1 : ℚ) * (weighted k l n + (weighted k l n) ^ k) / (n + 2 : ℚ)

/-- The first nonintegral term has the positive source index n. -/
def firstFailure (k l n : ℕ) : Prop :=
  0 < n ∧ (weighted k l (n - 1)).den ≠ 1 ∧
    ∀ j : ℕ, 0 < j → j < n → (weighted k l (j - 1)).den = 1

theorem main :
    (∀ k l : ℕ,
      (firstFailure k l 3 ↔
        (k % 2 = 1 ∧ (l % 3 = 1 ∨ l % 3 = 2)) ∨ (k % 2 = 0 ∧ l % 3 = 1)) ∧
      (firstFailure k l 5 ↔
        (k % 4 = 1 ∧ (l % 15 = 3 ∨ l % 15 = 6 ∨ l % 15 = 9 ∨ l % 15 = 12)) ∨
        (k % 4 = 0 ∧ (l % 15 = 3 ∨ l % 15 = 6 ∨ l % 15 = 8 ∨ l % 15 = 11)))) ∧
    (∀ B : ℕ, ∃ k l n : ℕ, B < n ∧ firstFailure k l n) := by
  sorry

end OMA.S_mo_495589
