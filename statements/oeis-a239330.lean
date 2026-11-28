import Mathlib

/-!
# Prime counts in intervals centered at half a prime multiple

Source: https://oeis.org/A239330 (Zhi-Wei Sun)
Credit: @pyaf
-/

namespace OMA.S_oeis_a239330

/-- A239330, indexed from 1. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n).filter fun p =>
    p.Prime ∧ (Nat.primeCounting (n * (p + 1) / 2) -
      Nat.primeCounting (n * (p - 1) / 2)).Prime).card

theorem main :
    (∀ n : ℕ, 3 < n → 0 < a n) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ n ∈ ([4, 5, 17] : List ℕ))) := by
  sorry

end OMA.S_oeis_a239330
