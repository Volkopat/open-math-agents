import Mathlib

/-!
# A071304: Recurrence for orthogonal matrices over Z/5Z via unit-sphere points

Source: https://oeis.org/A071304
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A071304: a(n) = (1/2) * (number of n X n 0..4 matrices M with MM' mod 5 = I).

Statement:
Let b(n) be the number of solutions to Sum_{i=1..n} x_i^2 = 1 (mod 5) with x_i in Z/5Z.
Conjecture: a(n+1) = a(n) * b(n+1) for n >= 1.
-/

namespace OMA.S_oeis_a071304

/-- Number of `n x n` orthogonal matrices over `ZMod 5`, divided by 2 (`A071304`). -/
noncomputable def a (n : ℕ) : ℕ :=
  {M : Matrix (Fin n) (Fin n) (ZMod 5) | M * M.transpose = 1}.ncard / 2

/-- Number of vectors `x : Fin n -> ZMod 5` with `Sum x_i^2 = 1`. -/
noncomputable def b (n : ℕ) : ℕ :=
  {x : Fin n → ZMod 5 | (∑ i : Fin n, (x i) ^ 2) = 1}.ncard

theorem main :
    ∀ n : ℕ, 1 ≤ n → a (n + 1) = a n * b (n + 1) := by
  sorry

end OMA.S_oeis_a071304
