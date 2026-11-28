import Mathlib

/-!
# MathOverflow 434155

Source: https://mathoverflow.net/questions/434155
-/

namespace OMA.S_mo_434155

open Finset

theorem main : ∀ (n : ℕ) (lam : Fin (n + 1) → ℕ), Antitone lam →
      Nat.card {mu : Fin n → ℕ // ∀ i, lam i.succ ≤ mu i ∧ mu i ≤ lam i.castSucc} =
        ∏ i : Fin n, (lam i.castSucc - lam i.succ + 1) := by
  sorry

end OMA.S_mo_434155
