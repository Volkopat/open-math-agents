import Mathlib

/-!
# A300448: Number of the integers 4^k*m with k >= 0 and m = 1, 2, 5 such that n^2 - 4^k*m can be written as the sum of two squares.

Source: https://oeis.org/A300448
Credit: @azmiozgen

Conjectures (Zhi-Wei Sun, from the entry):
1. a(n) > 0 for all n > 0.
2. Each positive square n^2 can be written as 4^k*m + x^2 + y^2 with k, x, y nonnegative integers and
   m among 1, 5, 17.
3. For each n = 1, 2, 3, ... we can write n^2 as 4^k*m + x^2 + y^2 with k, x, y nonnegative integers and
   m among 1, 5, 65.

Formalization notes:
* Sums of two squares use nonnegative integers. Conjecture 1 says some 4^k m with m ∈ {1, 2, 5} has
  n^2 - 4^k m a sum of two squares, stated as n^2 = 4^k m + x^2 + y^2.
* Controls (computed): all three conjectures hold for 1 ≤ n < 3000.
-/

namespace OMA.S_oeis_a300448



/-- The conjectures of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 2, 5} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2) ∧
      (∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 5, 17} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2) ∧
      ∀ n : ℕ, 0 < n → ∃ m ∈ ({1, 5, 65} : Finset ℕ), ∃ k x y : ℕ, 4 ^ k * m ≤ n ^ 2 ∧ n ^ 2 = 4 ^ k * m + x ^ 2 + y ^ 2 := by
  sorry

end OMA.S_oeis_a300448
