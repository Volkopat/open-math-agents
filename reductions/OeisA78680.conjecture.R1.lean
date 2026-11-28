import FormalConjectures.OEIS.«78680»

-- Reduction OeisA78680.conjecture.R1 of Smallest $m > 0$ such that $n \cdot 2^m + 1$ is prime
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is a conjunction of two independent claims about the sequence `a`: the single
-- value at `n = 2 ^ 16`, and the non-vanishing on the whole finite range `1 <= n < 2 ^ 16`.

namespace OMA.R_OeisA78680_conjecture_R1

/-- The conjectured first zero of the sequence: `a (2 ^ 16) = 0`. -/
def H1 : Prop := OeisA78680.a (2 ^ 16) = 0

/-- The sequence does not vanish anywhere in the finite range `1 <= n < 2 ^ 16`, i.e. the first
zero is not before `2 ^ 16`. -/
def H2 : Prop := ∀ n : ℕ, 1 ≤ n ∧ n < 2 ^ 16 → OeisA78680.a n ≠ 0

theorem main : H1 → H2 → type_of% @OeisA78680.conjecture := by
  intro h1 h2
  exact ⟨h1, h2⟩

end OMA.R_OeisA78680_conjecture_R1
