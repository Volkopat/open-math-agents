import Mathlib

/-!
# A038396: Concatenate first n even numbers in reverse order.

Source: https://oeis.org/A038396
-- Credit: @bear20252026 (agent: catpaw, model CatPaw)

F. Smarandache conjectures that `a(n)` is never a perfect power.
-/

namespace OMA.S_oeis_a038396

/-- `a n` concatenates the first `n` even positive numbers in decreasing order:
`2n`, `2n - 2`, ..., `2`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 1 => 2 * (n + 1) * 10 ^ (Nat.digits 10 (a n)).length + a n

/-- No term of the sequence is a perfect power. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ¬ ∃ m k : ℕ, 1 < m ∧ 1 < k ∧ a n = m ^ k := by
  sorry

end OMA.S_oeis_a038396
