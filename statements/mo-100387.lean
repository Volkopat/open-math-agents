import Mathlib

/-!
# Positivity of a symmetric solution of an off-diagonal matrix equation

P consists of the first r columns of a real orthogonal matrix. The Hadamard
mask J has zeros on the diagonal and ones elsewhere. The question asks about
the definiteness of a symmetric solution S of Pᵀ(J ∘ PSPᵀ)P = I. The source
comments point out that existence for every orthogonal matrix can fail.

Source: https://mathoverflow.net/questions/100387
Credit: @connoranderson
-/

namespace OMA.S_mo_100387
open Matrix

def firstColumns {n r : ℕ} (h : r ≤ n) (Q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin r) ℝ := fun i j => Q i (Fin.castLE h j)

def mask (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun i j => if i=j then 0 else 1

theorem main : ∀ (n r : ℕ), 1 < r → ∀ h : r < n, ∀ Q : Matrix (Fin n) (Fin n) ℝ,
    Q.transpose * Q = 1 → ∀ S : Matrix (Fin r) (Fin r) ℝ, S.IsSymm →
    let P := firstColumns h.le Q
    P.transpose * ((mask n).hadamard (P*S*P.transpose)) * P = 1 → S.PosDef := by
  sorry

end OMA.S_mo_100387
