import Mathlib

/-!
# Arranging 1, …, 2n in a prime-sum circle

Source: https://arxiv.org/abs/1804.07104, Conjecture 1 (Hong-Bin Chen, Hung-Lin Fu and Jun-Yi Guo)
Credit: @pyaf

For n ≥ 2 the integers 1, 2, …, 2n can be arranged in a circle so that the
sum of any two adjacent numbers is prime; equivalently the prime sum graph
G₂ₙ has a Hamilton cycle. Position k holds the number a(k) + 1, and
finRotate sends each position to the next one around the circle.
-/

namespace OMA.S_arxiv_1804_07104

theorem main : ∀ n : ℕ, 2 ≤ n → ∃ a : Fin (2 * n) ≃ Fin (2 * n),
    ∀ k : Fin (2 * n), ((a k).val + 1 + ((a (finRotate (2 * n) k)).val + 1)).Prime := by
  sorry

end OMA.S_arxiv_1804_07104
