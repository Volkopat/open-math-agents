import OMAStatements.S_mo_444295
import Mathlib

-- Problem: mo-444295, if all maximal minors of an integer matrix A lie in {0, 1, -1}, do all
-- maximal minors of the tensor square of A lie in {0, 1, -1}?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For A = [1 0 0 1 1 -1; 0 1 0 1 1 0; 0 0 1 0 -1 1] every 3 x 3 minor is 0, 1 or -1, but
-- the 9 x 9 minor of the tensor square on the columns 22, 19, 2, 6, 1, 26, 12, 31, 34 is 2.
-- The minor is evaluated through an explicit factorization L * U with L lower triangular
-- (diagonal product 2) and U upper triangular with unit diagonal.

-- Kernel-check the finite matrix equality and triangularity directly over Fin9.
-- Original LU counterexample and credit are preserved.
namespace MO444295

open OMA.S_mo_444295

def A : Matrix (Fin 3) (Fin 6) ℤ :=
  !![1, 0, 0, 1, 1, -1; 0, 1, 0, 1, 1, 0; 0, 0, 1, 0, -1, 1]

theorem minors : ∀ a b d : Fin 6,
    smallDet (A 0 a * A 1 b * A 2 d - A 0 a * A 1 d * A 2 b - A 0 b * A 1 a * A 2 d +
      A 0 b * A 1 d * A 2 a + A 0 d * A 1 a * A 2 b - A 0 d * A 1 b * A 2 a) := by
  unfold smallDet
  decide +kernel

theorem hA : ∀ e : Fin 3 ↪ Fin 6, smallDet (A.submatrix id e).det := by
  intro e
  rw [Matrix.det_fin_three]
  exact minors (e 0) (e 1) (e 2)

def cf : Fin 9 → Fin 36 := ![22, 19, 2, 6, 1, 26, 12, 31, 34]

theorem cf_inj : Function.Injective cf := by decide +kernel

def c : Fin (3 * 3) ↪ Fin (6 * 6) := ⟨cf, cf_inj⟩

def L : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0;
    -1, 0, 1, 0, 0, 0, 0, 0, 0;
    1, 0, 0, 1, 0, 0, 0, 0, 0;
    1, 1, 0, 0, -1, 0, 0, 0, 0;
    -1, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, -1, 0, 0, -2]

def U : Matrix (Fin 9) (Fin 9) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 1, 0, 0, 1, 0, 0, -1, 0;
    0, 0, 1, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 1, 0, 0, -1, -1;
    0, 0, 0, 0, 0, 1, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 1, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 0, 1]

theorem sub_eq : (tensorSquare A).submatrix id c = L * U := by
  decide +kernel

theorem detL : L.det = 2 := by
  have h : L.IsLowerTriangular := by decide +kernel
  rw [Matrix.det_of_isLowerTriangular L h]
  decide +kernel

theorem detU : U.det = 1 := by
  have h : U.IsUpperTriangular := by decide +kernel
  rw [Matrix.det_of_isUpperTriangular h]
  decide +kernel

theorem det_eq : ((tensorSquare A).submatrix id c).det = 2 := by
  rw [sub_eq, Matrix.det_mul, detL, detU]
  norm_num

end MO444295

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_444295.main) := by
  intro h
  have key : OMA.S_mo_444295.smallDet
      ((OMA.S_mo_444295.tensorSquare MO444295.A).submatrix id MO444295.c).det :=
    h 3 6 (by norm_num) MO444295.A MO444295.hA MO444295.c
  rw [MO444295.det_eq] at key
  unfold OMA.S_mo_444295.smallDet at key
  omega
