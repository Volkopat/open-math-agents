import Mathlib

/-!
# MathOverflow 92798

Source: https://mathoverflow.net/questions/92798
-/

namespace OMA.S_mo_92798

open Matrix InnerProductSpace
open scoped InnerProductSpace RealInnerProductSpace BigOperators

noncomputable def jacobiMatrix {n : ℕ} (d : Fin n → ℝ) (b : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i=j then d i else if i.val+1=j.val ∨ j.val+1=i.val then b else 0

noncomputable def smallestEigenvalue {n : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ}
    (hA : A.IsHermitian) : ℝ :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
    (by simp [finrank_euclideanSpace]) (Fin.last n)

theorem main : ∀ (n : ℕ) (a c : Fin (n+1) → ℝ) (b : ℝ), b<0 →
      (∀ i, 0<a i ∧ 0<c i) → (∃ i, ∀ j, a i<c j) →
      0 < (jacobiMatrix c b - jacobiMatrix a b).trace →
      ∀ (hJ : (jacobiMatrix a b).PosDef) (hL : (jacobiMatrix c b).PosDef),
        smallestEigenvalue hJ.1 < smallestEigenvalue hL.1 := by
  sorry

end OMA.S_mo_92798
