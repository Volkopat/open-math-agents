import Mathlib

/-!
# Solutions of (aⁿ − 2)(bⁿ − 2) = x² have n ≤ 6

Source: https://arxiv.org/abs/1801.04770, Conjecture 32 (Zafer Şiar and Refik Keskin)
Credit: @pyaf

Let 2 < a < b. If the equation (aⁿ − 2)(bⁿ − 2) = x² has a solution n, x in
natural numbers, then n ≤ 6. The equation is read in the integers.
-/

namespace OMA.S_arxiv_1801_04770

theorem main : ∀ a b n x : ℕ, 2 < a → a < b →
    ((a : ℤ) ^ n - 2) * ((b : ℤ) ^ n - 2) = (x : ℤ) ^ 2 → n ≤ 6 := by
  sorry

end OMA.S_arxiv_1801_04770
