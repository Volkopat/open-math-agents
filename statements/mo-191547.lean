import Mathlib

/-!
# Is the set of numbers ⌊n^(3/2)⌋ a basis of order 3?

Source: https://mathoverflow.net/questions/191547 (CC BY-SA 3.0).

A set of integers is a basis of order `h` if every nonnegative integer is the sum of `h` not
necessarily distinct elements of the set. Question: is `S = {⌊n^(3/2)⌋ : n ≥ 0}`
`= {0, 1, 2, 5, 8, 11, 14, 18, 22, …}` a basis of order `3`? (It is not a basis of order `2`:
`17` is not a sum of two elements.) `main` states the yes direction, which holds for every
integer up to `3 × 10⁶` by direct computation.
For `n : ℕ`, `⌊n^(3/2)⌋ = ⌊√(n³)⌋ = Nat.sqrt (n ^ 3)`.
-/

namespace OMA.S_mo_191547

theorem main : ∀ m : ℕ, ∃ a b c : ℕ, m = Nat.sqrt (a ^ 3) + Nat.sqrt (b ^ 3) + Nat.sqrt (c ^ 3) := by
  sorry

end OMA.S_mo_191547
