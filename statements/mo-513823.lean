import Mathlib.Data.Fin.Basic

/-! Source: https://mathoverflow.net/questions/513823 -/

namespace OMA.S_mo_513823

theorem main : ∀ n : ℕ, 0 < n → ∀ op : Fin n → Fin n → Fin n,
    (∀ a b, op a b = op b a) →
    (∀ a b c, op (op a b) c = op (op a c) (op b c)) →
    (n - 1) / 2 = 0 ∨ ∃ a b : Fin n, a ≠ b ∧
      ∃ x y : Fin ((n - 1) / 2) → Fin n,
        Function.Injective x ∧ Function.Injective y ∧
        ∀ i, x i ≠ b ∧ y i ≠ a ∧ op a (x i) = op b (y i) := by
  sorry

end OMA.S_mo_513823
