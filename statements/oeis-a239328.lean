import Mathlib

/-!
# Prime counts between consecutive multiples

Source: https://oeis.org/A239328 (Zhi-Wei Sun)
Credit: @pyaf
-/

namespace OMA.S_oeis_a239328

/-- A239328, indexed from 1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun p =>
    p.Prime ∧ (Nat.primeCounting (p * n) - Nat.primeCounting ((p - 1) * n)).Prime).card

theorem main :
    (∀ n : ℕ, 3 < n → 0 < a n) ∧
    (∀ n : ℕ, 4 < n → ∃ p < n, Nat.Prime p ∧
      (Nat.primeCounting ((p + 1) * n) - Nat.primeCounting (p * n)).Prime) := by
  sorry

end OMA.S_oeis_a239328
