import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# OEIS A322921

Source: https://oeis.org/A322921 (Emanuele Munarini)

Count unordered Goldbach decompositions by choosing the smaller prime.
Every three consecutive even integers contain one multiple of six.
The conjecture says its count is at least the count for either other integer.
-/

namespace OMA.S_oeis_a322921

def decompositions (n : ℕ) : ℕ :=
  ((Finset.range (n / 2 + 1)).filter fun p => Nat.Prime p ∧ Nat.Prime (n - p)).card

theorem main : ∀ n : ℕ, 48 ≤ n → Even n → ∀ i j : Fin 3,
    6 ∣ n + 2 * i.val → decompositions (n + 2 * j.val) ≤ decompositions (n + 2 * i.val) := by
  sorry

end OMA.S_oeis_a322921
