import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Matrix-optimal factors need not be tensor-optimal

Source: https://mathoverflow.net/questions/256897/doubt-on-the-best-low-rank-approximation-of-a-symmetric-tensor
Credit: @etaubman.

An order-h tensor is represented by its coefficients indexed by Fin h -> Fin n.
The Frobenius distance is the square root of the sum of squared coefficients.
Full column rank is expressed by linear independence of the columns.
-/

namespace OMA.S_mo_256897

noncomputable def tensor {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ) (h : ℕ)
    (a : Fin h → Fin n) : ℝ :=
  ∑ j, ∏ r, M (a r) j

noncomputable def squaredError {n k l : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (N : Matrix (Fin n) (Fin l) ℝ) (h : ℕ) : ℝ :=
  ∑ a : Fin h → Fin n, (tensor M h a - tensor N h a) ^ 2

noncomputable def error {n k l : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (N : Matrix (Fin n) (Fin l) ℝ) (h : ℕ) : ℝ :=
  Real.sqrt (squaredError M N h)

def FullColumnRank {n k : ℕ} (M : Matrix (Fin n) (Fin k) ℝ) : Prop :=
  LinearIndependent ℝ (fun j => fun i => M i j)

def Minimizes {n k l : ℕ} (M : Matrix (Fin n) (Fin k) ℝ)
    (N : Matrix (Fin n) (Fin l) ℝ) (h : ℕ) : Prop :=
  ∀ N' : Matrix (Fin n) (Fin l) ℝ, FullColumnRank N' → error M N h ≤ error M N' h

def claim : Prop :=
  ∀ (n k l : ℕ), k < n → l < k →
    ∀ (M : Matrix (Fin n) (Fin k) ℝ) (N : Matrix (Fin n) (Fin l) ℝ),
      FullColumnRank M → FullColumnRank N → Minimizes M N 2 →
      ∀ h : ℕ, 2 < h → Minimizes M N h

theorem main : claim := by
  sorry

end OMA.S_mo_256897
