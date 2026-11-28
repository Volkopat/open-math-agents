import Mathlib

/-!
# Orthonormal bases with small coordinate suprema

Source: akshaykr, https://mathoverflow.net/questions/156854 (CC BY-SA 3.0).
Credit: @connoranderson.

Columns of B are a real orthonormal basis precisely when BᵀB=I on their
span. Their orthogonal projector is BBᵀ. Its ith column has squared
Euclidean norm equal to the squared norm of row i of B, so leverage is
exactly the source's γ(U). Cost is the sum of squared column sup norms.
The lower bound and the universal factor d hold for every basis.

The best factor uniform over all ambient dimensions is exactly d. For
each positive d and η, finitely many orthonormal bases can be stacked and
normalized to form a single frame such that every orthonormal basis of
its column space has cost at least (1−η)dγ(U). A finite spherical net
gives a block with a row near each unit vector. In particular no bound
polynomial in log d can hold in the generality asked.
-/

namespace OMA.S_mo_156854
open Matrix
open scoped NNReal
noncomputable def coordPeak {ι κ : Type*} [Fintype ι] (B : Matrix ι κ ℝ) (j : κ) : ℝ :=
  ((Finset.univ : Finset ι).sup (fun i => ‖B i j‖₊^2) : ℝ≥0)
noncomputable def cost {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix ι κ ℝ) : ℝ :=
  ∑ j,coordPeak B j
noncomputable def leverage {ι κ : Type*} [Fintype ι] [Fintype κ] (B : Matrix ι κ ℝ) : ℝ :=
  ((Finset.univ : Finset ι).sup (fun i => ∑ j,‖B i j‖₊^2) : ℝ≥0)

theorem main :
    (∀ (ι κ : Type*) [Fintype ι] [Fintype κ] (B : Matrix ι κ ℝ),
      leverage B ≤ cost B ∧ cost B ≤ Fintype.card κ * leverage B) ∧
    (∀ (ι κ : Type*) [Fintype ι] [Fintype κ] [DecidableEq κ] (B : Matrix ι κ ℝ),
      Bᵀ*B=1 → ∀ i, ∑ l,((B*Bᵀ) l i)^2 = ∑ j,B i j^2) ∧
    ∀ d : ℕ, 0<d → ∀ η : ℝ, 0<η → ∃ t : ℕ, 0<t ∧
      ∃ B : Matrix (Fin t × Fin d) (Fin d) ℝ, Bᵀ*B=1 ∧ 0<leverage B ∧
        ∀ W : Matrix (Fin t × Fin d) (Fin d) ℝ, Wᵀ*W=1 →
          LinearMap.range W.mulVecLin = LinearMap.range B.mulVecLin →
          (1-η)*(d:ℝ)*leverage B ≤ cost W := by
  sorry
end OMA.S_mo_156854
