import OMAStatements.S_mo_151738
import Mathlib

/-!
# MathOverflow 151738: a diagonalisable block upper triangular matrix need not be block diagonal

Counterexample with two blocks of size one: `M = !![1, 1; 0, -1]`.

* It is block upper triangular, and the diagonal blocks `[1]` and `[-1]` square to the identity.
* It is diagonalisable: with `P = !![1, 1; 0, -2]` (inverse `Q = !![1, 1/2; 0, -1/2]`) we have
  `M * P = P * diag(1, -1)`.
* But the off-diagonal block entry `M₀₁ = 1` is not zero.
-/

namespace OMA.S_mo_151738

/-- The index type: two blocks of size one. -/
abbrev Idx := Σ _ : Fin 2, Fin 1

/-- `M = !![1, 1; 0, -1]`. -/
noncomputable def Mx : Matrix Idx Idx ℂ := fun x y => if y.1 < x.1 then 0 else if x.1 = 1 then -1 else 1

/-- `P = !![1, 1; 0, -2]`, whose columns are eigenvectors of `M`. -/
noncomputable def Px : Matrix Idx Idx ℂ := fun x y => if x.1 = 0 then 1 else if y.1 = 1 then -2 else 0

/-- `Q = !![1, 1/2; 0, -1/2]`, the inverse of `P`. -/
noncomputable def Qx : Matrix Idx Idx ℂ := fun x y =>
  if x.1 = 0 then (if y.1 = 0 then 1 else 1 / 2) else if y.1 = 1 then -1 / 2 else 0

/-- The eigenvalues `1, -1`. -/
noncomputable def dx : Idx → ℂ := fun x => if x.1 = 0 then 1 else -1

lemma PQ : Px * Qx = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain rfl : a = b := Subsingleton.elim a b
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Px, Qx] <;> norm_num

lemma MP : Mx * Px = Px * Matrix.diagonal dx := by
  ext ⟨i, a⟩ ⟨j, b⟩
  obtain rfl : a = b := Subsingleton.elim a b
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Fintype.sum_sigma]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, Mx, Px, dx, Matrix.diagonal_apply] <;>
    (try norm_num) <;> (try exact Subsingleton.elim _ _)

end OMA.S_mo_151738

open OMA.S_mo_151738 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_151738.main) := by
  intro h
  have hP : IsUnit Px := (Matrix.isUnit_iff_isUnit_det Px).mpr
    (isUnit_iff_exists_inv.mpr ⟨Qx.det, by rw [← Matrix.det_mul, PQ, Matrix.det_one]⟩)
  have key := h 2 (fun _ => 1) Mx
    (fun x y hxy => by simp [Mx, hxy])
    (fun i => ⟨2, by norm_num, by
      ext a b
      fin_cases i <;> simp [pow_two, Matrix.mul_apply, Mx, Matrix.one_apply] <;>
        exact Subsingleton.elim _ _⟩)
    ⟨Px, dx, hP, by
      rw [mul_assoc, MP, ← mul_assoc,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP), one_mul]⟩
    ⟨0, 0⟩ ⟨1, 0⟩ (by simp)
  simp [Mx] at key
