import Mathlib

/-!
# Nonsingularity of the signed root-of-unity matrix

Source: Binzhou Xia, https://mathoverflow.net/questions/143764 (CC BY-SA 3.0).
Credit: @connoranderson.

Boolean coordinates encode the independent signs, with true representing -1.
Finite indices are the zero-based exponents in the question.
-/

namespace OMA.S_mo_143764

def sign {R : Type*} [Ring R] (b : Bool) : R := if b then -1 else 1

def signedMatrix {R : Type*} [CommRing R] {n : ℕ} (ζ : R) (α β : Fin n → Bool) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => (sign (α i) : R)^j.val * (sign (β j) : R)^i.val * ζ^(i.val*j.val)

theorem main : ∀ (n : ℕ), 0<n → ∀ ζ : ℂ, IsPrimitiveRoot ζ (2*n) →
    ∀ α β : Fin n → Bool, (signedMatrix ζ α β).det ≠ 0 := by
  sorry

end OMA.S_mo_143764
