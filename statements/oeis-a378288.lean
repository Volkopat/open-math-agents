import Mathlib

/-!
# A378288: Prime decimal concatenations of Mersenne numbers

Source: https://oeis.org/A378288
Formalization: @pyaf

Both row indices k and entries j start at 1.
-/

namespace OMA.S_oeis_a378288

def concatenation (k j : ℕ) : ℕ :=
  let right := 2 ^ j - 1
  (2 ^ k - 1) * 10 ^ (Nat.digits 10 right).length + right

theorem main : (∀ k : ℕ, 0 < k → {j : ℕ | 0 < j ∧ (concatenation k j).Prime}.Infinite) ∧
    (∀ j : ℕ, 0 < j → ¬ 4 ∣ j → {k : ℕ | 0 < k ∧ (concatenation k j).Prime}.Infinite) := by
  sorry

end OMA.S_oeis_a378288
