import Mathlib

/-!
# Prime factors of the totient quotient of a Mersenne number

Question by joro on MathOverflow (CC BY-SA), https://mathoverflow.net/questions/496788.
Credit: @KIRKR101
-/

namespace OMA.S_mo_496788

theorem main : ∀ B : ℕ, ∃ n p q : ℕ,
    0 < n ∧ Squarefree n ∧ B < p ∧ Nat.Prime p ∧
    Nat.totient (2 ^ n - 1) = n * q ∧ p ∣ q ∧ ¬ p ^ 2 ∣ q := by
  sorry

end OMA.S_mo_496788
