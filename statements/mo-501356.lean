import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Defs

/-! Source: https://mathoverflow.net/questions/501356 -/

namespace OMA.S_mo_501356

noncomputable def squareIndexPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k ^ 2 - 1)

theorem main :
    (∀ n : ℕ, 3286 < n → ∃ i j k m : ℕ,
      0 < i ∧ 0 < j ∧ 0 < k ∧ 0 < m ∧
      2 * n = squareIndexPrime i + squareIndexPrime j + squareIndexPrime k + squareIndexPrime m) ∧
    (∀ n : ℕ, 3200 < n → ∃ i j k m : ℕ,
      0 < m ∧ m ≤ k ∧ k ≤ j ∧ j ≤ i ∧
      2 * n + 1 = squareIndexPrime i + squareIndexPrime j + squareIndexPrime k + 2 * squareIndexPrime m) := by
  sorry

end OMA.S_mo_501356
