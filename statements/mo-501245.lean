import Mathlib

/-!
# A block-tridiagonal characteristic polynomial

Source: https://mathoverflow.net/questions/501245 . For n+1 blocks, `index k n`
indexes their consecutive groups of k coordinates. The new block has diagonal A,
upper off-diagonal B, lower off-diagonal Bᵀ, and zero entries further away.
The pivot recurrence runs in the rational function field ℝ(X). The result
includes nonsingularity of all its pivots. See also Fred Hucht's source comment
pointing to D. K. Salkuyeh's recurrence for block-tridiagonal determinants.

Credit: @connoranderson
-/

namespace OMA.S_mo_501245
open Matrix Polynomial

abbrev K := FractionRing ℝ[X]

abbrev index (k : ℕ) : ℕ → Type
  | 0 => Fin k
  | n+1 => index k n ⊕ Fin k

instance indexFintype (k : ℕ) : (n : ℕ) → Fintype (index k n)
  | 0 => inferInstanceAs (Fintype (Fin k))
  | n+1 => let _ := indexFintype k n; inferInstanceAs (Fintype (index k n ⊕ Fin k))

instance indexDecidableEq (k : ℕ) : (n : ℕ) → DecidableEq (index k n)
  | 0 => inferInstanceAs (DecidableEq (Fin k))
  | n+1 => let _ := indexDecidableEq k n; inferInstanceAs (DecidableEq (index k n ⊕ Fin k))

def border {R : Type*} [Zero R] {k : ℕ} (B : Matrix (Fin k) (Fin k) R) :
    (n : ℕ) → Matrix (index k n) (Fin k) R
  | 0 => B
  | n+1 => fromRows (0 : Matrix (index k n) (Fin k) R) B

noncomputable def tridiagonal {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) :
    (n : ℕ) → Matrix (index k n) (index k n) ℝ
  | 0 => A
  | n+1 => fromBlocks (tridiagonal A B n) (border B n) (border B n).transpose A

noncomputable def constant : ℝ →+* K := (algebraMap ℝ[X] K).comp Polynomial.C

noncomputable def pencil {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) : Matrix ι ι K :=
  A.charmatrix.map (algebraMap ℝ[X] K)

noncomputable def pivot {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℝ) : ℕ → Matrix (Fin k) (Fin k) K
  | 0 => pencil A
  | n+1 => pencil A - (B.map constant).transpose * (pivot A B n)⁻¹ * B.map constant

theorem main : ∀ k : ℕ, 0<k → ∀ A B : Matrix (Fin k) (Fin k) ℝ, A.IsSymm → ∀ n : ℕ,
    (pivot A B n).det ≠ 0 ∧
    algebraMap ℝ[X] K (tridiagonal A B n).charpoly =
      ∏ j ∈ Finset.range (n+1), (pivot A B j).det := by
  sorry

end OMA.S_mo_501245
