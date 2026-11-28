import Mathlib

/-!
# Inverse row sums of the stretched Riordan triangle A115524

Column j of A115524 has generating polynomial
(-x)^j + (x*(-x)^j + x^(j+1))/2 - x^(2*j+2).
Thus row zero has just the diagonal entry 1. Every positive row r has
diagonal sign (-1)^r and its opposite at one earlier column: r-1 for
odd r and r/2-1 for even r. The zero-based triangle A115526 is the
ordinary lower-triangular inverse, so its row r is obtained from the
inverse of the leading (r+1)-by-(r+1) block.

https://oeis.org/A115526 · https://oeis.org/A115524 · https://oeis.org/A023416
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a115526

def earlier (r : ℕ) : ℕ := if r % 2 = 0 then r/2 - 1 else r - 1

def earlierCol {n : ℕ} (i : Fin (n+1)) : Fin (n+1) :=
  ⟨earlier i.val, by have h := i.isLt; unfold earlier; split <;> omega⟩

def sign (r : ℕ) : ℚ := if r % 2 = 0 then 1 else -1

def corner (n : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℚ :=
  Matrix.of fun i j =>
    (if j = i then sign i.val else 0) -
    (if 0 < i.val then (if j = earlierCol i then sign i.val else 0) else 0)

def zeros (m : ℕ) : ℕ := ((2 : ℕ).digits m).count 0

theorem main : ∀ n : ℕ,
    (∑ j : Fin (n+1), (corner n)⁻¹ (Fin.last n) j) = (zeros (n+2) : ℚ) := by
  sorry

end OMA.S_oeis_a115526
