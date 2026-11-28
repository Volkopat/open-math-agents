import Mathlib

/-!
# A question on products of linear combinations of complex matrices

Source: https://mathoverflow.net/questions/445970
Credit: @ivillar

Status: false as stated. Counterexample with `n = 1`, `d = 2`: `A₁ = E₁₂` and `B₁ = E₁₁` (matrix
units). Then `(x A₁)(x A₁)† = |x|² E₁₁ = (x B₁)(x B₁)†` for every `x`, but every product `Σ B₁`
has zero second column, so `A₁ ≠ Σ B₁`. (The hypothesis only gives a unitary acting on the
right: `A_i = B_i U`.) The statement is kept as the target of a disproof.

Suppose that $A_1, \dots , A_n, B_1, \dots , B_n \in \Bbb C^{d \times d}$ and that, for every
$x \in \mathbb{C}^n$, the following holds
$$\left( \sum_i x_i A_i \right) \left( \sum_i x_i A_i \right)^{\dagger} =
\left( \sum_i x_i B_i \right) \left( \sum_i x_i B_i \right)^{\dagger}$$
where $\dagger$ denotes the adjoint (i.e., transpose conjugate) of a matrix. Is it true that
there exists a unitary matrix $\Sigma \in {\rm U}(d, \mathbb{C})$ such that $A_i = \Sigma B_i$
for all $i$?

Formalization notes:
* The matrices are families `A B : Fin n → Matrix (Fin d) (Fin d) ℂ`, the adjoint is the
  conjugate transpose, and `Σ` ranges over `Matrix.unitaryGroup (Fin d) ℂ`.
-/

namespace OMA.S_mo_445970

open Matrix

theorem main : ∀ (n d : ℕ) (A B : Fin n → Matrix (Fin d) (Fin d) ℂ),
    (∀ x : Fin n → ℂ, (∑ i, x i • A i) * (∑ i, x i • A i)ᴴ =
      (∑ i, x i • B i) * (∑ i, x i • B i)ᴴ) →
    ∃ U ∈ Matrix.unitaryGroup (Fin d) ℂ, ∀ i, A i = U * B i := by
  sorry

end OMA.S_mo_445970
