import Mathlib.Data.Matrix.Block
import Mathlib.Data.Complex.Basic

/-!
MathOverflow 311259, eigenvalues of a square block matrix.
Source: https://mathoverflow.net/questions/311259/eigenvalues-of-a-square-block-matrix

The proposed absence of defective eigenvalues is stated as complex diagonalizability
for the real endpoint-damped block family. The source also asks ancillary questions
about determinants and spectral bounds; this statement addresses its principal claim.
-/

open Matrix

namespace OMA.S_mo_311259

def Diagonalizable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : Prop :=
  ∃ (P Q : Matrix ι ι ℂ) (e : ι → ℂ),
    P * Q = 1 ∧ Q * P = 1 ∧ M = P * diagonal e * Q

def endpointMatrix (d : ℕ) (a : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  diagonal fun i => if i.val = 0 ∨ i.val + 1 = d then -a else 0

def blockMatrix (d : ℕ) (a : ℝ) (B : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) ℂ :=
  (fromBlocks (endpointMatrix d a) B (-B) 0).map Complex.ofReal

def claim : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ a : ℝ, 0 < a →
    ∀ B : Matrix (Fin d) (Fin d) ℝ, Diagonalizable (blockMatrix d a B)

theorem main : claim := by sorry

end OMA.S_mo_311259
