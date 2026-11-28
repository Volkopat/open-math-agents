import Mathlib

/-!
# Cigler's continued-fraction identity for Hankel determinants

Source: Johann Cigler, https://mathoverflow.net/questions/120323 (CC BY-SA 3.0).
Credit: @connoranderson.

The three equations below give the continued fraction by multiplication
with its denominators. Each denominator has constant coefficient one.
The determinant is indexed by matrix size, so the convention for the
negative determinant indices on the right is the empty determinant.
-/

namespace OMA.S_mo_120323
open PowerSeries

noncomputable def hankel {R : Type*} [CommRing R] (f : PowerSeries R) (N : ℕ) : R :=
  (Matrix.of fun i j : Fin N => coeff (i.val+j.val) f).det

theorem main : ∀ (R : Type*) [CommRing R] (m n : ℕ) (a b : R)
    (g w v f : PowerSeries R),
    (1-X^2*g)*w=1 →
    (1-C b*X^(m+2)*w)*v=1 →
    (1-C a*X^(m+2)*v)*f=1 →
    hankel f (m+n+2) = (-1 : R)^((m+1).choose 2)*a^(m+n+1)*b^n*hankel g (n-1) := by
  sorry

end OMA.S_mo_120323
