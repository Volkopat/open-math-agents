import Mathlib

/-!
# OEIS A397445: vanishing permanents of Krawtchouk matrices

Source: https://oeis.org/A397445
Credit: @gblacher2
-/

namespace OMA.S_oeis_a397445

/-- Entry `(i,j)` is the coefficient of `x^i` in
`(1+x)^(n-1-j) * (1-x)^j`, with zero-based indices. -/
def krawtchouk (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  ∑ k ∈ Finset.range (min i.val j.val + 1),
    (-1 : ℤ) ^ k * (Nat.choose j.val k : ℤ) *
      (Nat.choose (n - 1 - j.val) (i.val - k) : ℤ)

theorem main : ∀ n : ℕ, (krawtchouk n).permanent = 0 ↔ n % 4 = 2 ∨ n % 4 = 3 := by
  sorry

end OMA.S_oeis_a397445
