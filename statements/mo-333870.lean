import Mathlib

/-!
# MathOverflow 333870

Source: https://mathoverflow.net/questions/333870
-/

namespace OMA.S_mo_333870

open scoped InnerProductSpace RealInnerProductSpace BigOperators
open InnerProductSpace Matrix

noncomputable def schurMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  let z := A *ᵥ WithLp.ofLp y
  A - (WithLp.ofLp y ⬝ᵥ z)⁻¹ • Matrix.vecMulVec z z

theorem main : ∀ (n : ℕ) (A : Matrix (Fin (n+2)) (Fin (n+2)) ℝ) (hA : A.PosDef)
      (y : EuclideanSpace ℝ (Fin (n+2))), ‖y‖=1 →
      ∃ hM : (schurMatrix A y).toEuclideanLin.IsSymmetric,
        (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA.1).eigenvalues
            (by simp [finrank_euclideanSpace]) (Fin.last (n+1)) ≤
          hM.eigenvalues (by simp [finrank_euclideanSpace]) (Fin.castSucc (Fin.last n)) := by
  sorry

end OMA.S_mo_333870
