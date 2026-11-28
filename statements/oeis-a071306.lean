import Mathlib

/-!
# A071306: Recurrence for orthogonal matrices and unit-sphere points over Z/7Z

Source: https://oeis.org/A071306
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A071306: a(n) = (1/2) * (number of n X n 0..6 matrices M with MM' mod 7 = I).

Statement:
Let b(n) be the number of solutions to Sum_{i=1..n} x_i^2 = 1 (mod 7) with x_i in Z/7Z.
Conjecture: b(n) = 7*b(n-1) - 7*b(n-2) + 49*b(n-3) for n >= 4 (with b(1) = 2, b(2) = 8,
b(3) = 42), and a(n+1) = a(n) * b(n+1) for n >= 1.
-/

namespace OMA.S_oeis_a071306

/-- Number of `n x n` orthogonal matrices over `ZMod 7`, divided by 2 (`A071306`). -/
noncomputable def a (n : ℕ) : ℕ :=
  {M : Matrix (Fin n) (Fin n) (ZMod 7) | M * M.transpose = 1}.ncard / 2

/-- Number of vectors `x : Fin n -> ZMod 7` with `Sum x_i^2 = 1`. -/
noncomputable def b (n : ℕ) : ℕ :=
  {x : Fin n → ZMod 7 | (∑ i : Fin n, (x i) ^ 2) = 1}.ncard

theorem main :
    (∀ n : ℕ, 4 ≤ n →
      (b n : ℤ) = 7 * (b (n - 1) : ℤ) - 7 * (b (n - 2) : ℤ) + 49 * (b (n - 3) : ℤ)) ∧
    (∀ n : ℕ, 1 ≤ n → a (n + 1) = a n * b (n + 1)) := by
  sorry

end OMA.S_oeis_a071306
