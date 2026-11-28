import OMAStatements.S_mo_231913
import Mathlib

-- Problem: mo-231913, is a block Toeplitz matrix (C_{i-j}) positive semidefinite when C_0 is
-- positive semidefinite, C_{-l} = C_l^* and |C_l| <= |C_0| (Hilbert-Schmidt norms)?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. Take p = 3 and 1 x 1 blocks C_0 = 1, C_1 = C_{-1} = 1, C_2 = C_{-2} = -1. The Toeplitz
-- matrix is [1 1 -1; 1 1 1; -1 1 1], and for x = (1, -1, 1) the quadratic form x^* M x equals
-- 3 + 2 (-1 - 1 - 1) = -3 < 0.

open Matrix
open scoped ComplexOrder

namespace MO231913

open OMA.S_mo_231913

def c (l : ℤ) : ℤ := if l.natAbs = 2 then -1 else if l.natAbs ≤ 1 then 1 else 0

theorem hc0 : c 0 = 1 := by decide

theorem hc1 : c 1 = 1 := by decide

theorem hcm1 : c (-1) = 1 := by decide

theorem hc2 : c 2 = -1 := by decide

theorem hcm2 : c (-2) = -1 := by decide

theorem hneg (l : ℤ) : c (-l) = c l := by
  unfold c
  rw [Int.natAbs_neg]

theorem hc3 (l : ℤ) : c l = -1 ∨ c l = 1 ∨ c l = 0 := by
  unfold c
  split_ifs <;> simp

def C (l : ℤ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => ((c l : ℤ) : ℂ)

theorem C_zero : C 0 = 1 := by
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst hij
  simp [C, hc0]

theorem hyp1 : (C 0).PosSemidef := by
  rw [C_zero]
  exact Matrix.PosSemidef.one

theorem hyp2 : ∀ l : ℤ, C (-l) = (C l)ᴴ := by
  intro l
  ext i j
  simp [C, Matrix.conjTranspose_apply, hneg l]

theorem hyp3 : ∀ l : ℤ, -((3 : ℕ) : ℤ) < l → l < ((3 : ℕ) : ℤ) →
    hsNormSq (C l) ≤ hsNormSq (C 0) := by
  have e0 : hsNormSq (C 0) = 1 := by
    simp [hsNormSq, C, hc0]
  intro l _ _
  rw [e0]
  rcases hc3 l with h | h | h <;> simp [hsNormSq, C, h]

theorem value : star (fun a : Fin 3 × Fin 1 => ((![1, -1, 1] : Fin 3 → ℂ) a.1)) ⬝ᵥ
    (blockToeplitz 3 1 C *ᵥ (fun a : Fin 3 × Fin 1 => ((![1, -1, 1] : Fin 3 → ℂ) a.1))) =
      -3 := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_three, blockToeplitz,
    C, hc0, hc1, hcm1, hc2, hcm2]
  norm_num

end MO231913

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_231913.main) := by
  intro h
  have hpsd := h 3 1 MO231913.C MO231913.hyp1 MO231913.hyp2 MO231913.hyp3
  have h1 := hpsd.dotProduct_mulVec_nonneg
    (fun a : Fin 3 × Fin 1 => ((![1, -1, 1] : Fin 3 → ℂ) a.1))
  rw [MO231913.value] at h1
  have h2 := (Complex.le_def.mp h1).1
  norm_num at h2
