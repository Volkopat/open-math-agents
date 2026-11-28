import Mathlib

/-!
# Characteristic polynomials of stride-and-reflection matrices

Johann Cigler's four conjectures in the final edit of
https://mathoverflow.net/questions/355011 .

Here `charpoly` is monic, i.e. det(XI-G). Cigler uses det(G-XI), so the
signs from his dimensions are absorbed. The path polynomial is his F, and
the looped-path polynomial is his a with the monic normalization.
The hypotheses in the two subtractive cases require a nonnegative matrix
size, as in the source.

Credit: @connoranderson
-/

namespace OMA.S_mo_355011
open Polynomial

def strideMatrix (N h : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => if i.val+h=j.val ∨ j.val+h=i.val ∨ i.val+j.val+1=h then 1 else 0

noncomputable def pathPoly : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | k+2 => X * pathPoly (k+1) - pathPoly k

noncomputable def loopPoly : ℕ → ℤ[X]
  | 0 => 1
  | k+1 => pathPoly (k+1) - pathPoly k

theorem main : ∀ m k j : ℕ, j ≤ m →
    (strideMatrix (2*m*k+j) (2*m)).charpoly = pathPoly (2*k)^(m-j)*pathPoly (2*k+1)^j ∧
    (j ≤ 2*m*k → (strideMatrix (2*m*k-j) (2*m)).charpoly = pathPoly (2*k)^(m-j)*pathPoly (2*k-1)^j) ∧
    (strideMatrix ((2*m+1)*k+j) (2*m+1)).charpoly =
      loopPoly k * pathPoly (2*k)^(m-j)*pathPoly (2*k+1)^j ∧
    (j ≤ (2*m+1)*k → (strideMatrix ((2*m+1)*k-j) (2*m+1)).charpoly =
      loopPoly k * pathPoly (2*k)^(m-j)*pathPoly (2*k-1)^j) := by
  sorry

end OMA.S_mo_355011
