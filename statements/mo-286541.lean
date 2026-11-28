import Mathlib

/-!
# A quotient of two Hankel determinants

Source: Johann Cigler, https://mathoverflow.net/questions/286541 (CC BY-SA 3.0).
Credit: @connoranderson

Rows and columns run from 0 through n inclusive. We use the cross-multiplied
polynomial identity discussed by Richard Stanley in the comments. At k = 1
and n > 0 both determinants vanish and their literal quotient is undefined.
-/

namespace OMA.S_mo_286541

def binomialMoment (k m : ℕ) : ℚ := (k * m).choose m

def fussCatalan (k m : ℕ) : ℚ := binomialMoment k m / (((k : ℚ) - 1) * m + 1)

def hankel (s : ℕ → ℚ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  Matrix.of fun i j => s (i.val + j.val)

theorem main : ∀ k : ℕ, 0 < k → ∀ n : ℕ,
    (hankel (binomialMoment k) n).det = (k : ℚ)^n * (hankel (fussCatalan k) n).det := by
  sorry

end OMA.S_mo_286541
