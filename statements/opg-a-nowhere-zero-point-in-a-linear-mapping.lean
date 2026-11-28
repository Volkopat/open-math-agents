import Mathlib

/-!
# A nowhere-zero point in a linear mapping

Source: https://www.openproblemgarden.org/op/a_nowhere_zero_point_in_a_linear_mapping
Credit: @Mapika

Conjecture (Jaeger). If $\mathbb F$ is a finite field with at least 4 elements and $A$ is an
invertible $n \times n$ matrix with entries in $\mathbb F$, then there are column vectors
$x, y \in \mathbb F^n$ which have no coordinates equal to zero such that $Ax = y$.

The source records that Alon and Tarsi resolved the conjecture for all fields not of prime
order, and that Yu verified it over $\mathbb Z_p$ for small $n$; the open case is that of prime
fields. The page also states a second, stronger conjecture of DeVos (every invertible matrix over
$\mathbb Z_p$ is $(k+2, p-k)$-choosable); that is a separate problem and is not stated here.
No statement of Jaeger's conjecture was found in formal-conjectures.

Conventions:
* A finite field is a type `F` with `[Field F] [Fintype F]`; "at least 4 elements" is
  `4 ≤ Fintype.card F`. The bound matters: over `ZMod 2` the matrix `!![1, 1; 0, 1]` and over
  `ZMod 3` the matrix `!![1, 1; 1, -1]` are invertible and have no nowhere-zero point.
* `n` ranges over all natural numbers, as in the source (`n = 0` is trivially true).
* "Invertible" is `IsUnit A.det`, which for square matrices over a field is the same as
  `IsUnit A`.
* Column vectors in $\mathbb F^n$ are functions `Fin n → F`, and $Ax$ is `A.mulVec x`.
-/

namespace OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping

/-- **Jaeger's conjecture** on nowhere-zero points of invertible linear maps over finite fields
with at least four elements. -/
theorem main : ∀ (F : Type) [Field F] [Fintype F], 4 ≤ Fintype.card F →
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
      ∃ x y : Fin n → F, (∀ i, x i ≠ 0) ∧ (∀ i, y i ≠ 0) ∧ A.mulVec x = y := by
  sorry

end OMA.S_opg_a_nowhere_zero_point_in_a_linear_mapping
