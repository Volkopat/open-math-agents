import Mathlib

/-!
# OEIS A359559

The Hermitian Toeplitz determinant, its order-six recurrence, and the ordinary
and exponential generating functions. Sela Fried proves the determinant
formula in https://oeis.org/A359559/a359559.pdf, Corollary 1. Corollary 2
gives the generating functions, including the exponential generating function
corrected in the OEIS entry on January 28, 2026.
-/

open scoped BigOperators Matrix

namespace OMA.S_oeis_a359559

/-- The entry at the indicated zero-based row and column indices. -/
noncomputable def entry (i j : ℕ) : ℂ :=
  if i = j then 1
  else if i < j then Complex.I * ((j : ℂ) - i + 1)
  else -Complex.I * ((i : ℂ) - j + 1)

/-- The Hermitian Toeplitz matrix with first row 1, 2i, 3i, and so on. -/
noncomputable def toeplitz (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => entry i.val j.val

/-- A359559, with the empty determinant equal to one. -/
noncomputable def a (n : ℕ) : ℂ := (toeplitz n).det

/-- The ordinary generating function. -/
noncomputable def ogf : PowerSeries ℂ := PowerSeries.mk a

/-- The exponential generating function. -/
noncomputable def egf : PowerSeries ℂ :=
  PowerSeries.mk fun n => a n / (n.factorial : ℂ)

/-- The Toeplitz determinant formula, recurrence, and both generating-function identities. -/
theorem main :
    (∀ n : ℕ,
      a n = (((n:ℂ)^2+(4+Complex.I)*(n:ℂ)+4+4*Complex.I)/8)*(1+Complex.I)^n +
        (((n:ℂ)^2+(4-Complex.I)*(n:ℂ)+4-4*Complex.I)/8)*(1-Complex.I)^n) ∧
    (∀ n : ℕ, 5 < n →
      a n = 6*a (n-1) - 18*a (n-2) + 32*a (n-3) -
        36*a (n-4) + 24*a (n-5) - 8*a (n-6)) ∧
    (let X : PowerSeries ℂ := PowerSeries.X;
      ogf = (1-5*X+9*X^2-12*X^3+10*X^4-4*X^5)*(((1-2*X+2*X^2)^3)⁻¹)) ∧
    (let X : PowerSeries ℂ := PowerSeries.X;
      egf = PowerSeries.C (1/2 : ℂ)*PowerSeries.exp ℂ*(X+1)*
        (2*PowerSeries.cos ℂ-(X+2)*PowerSeries.sin ℂ)) := by
  sorry

end OMA.S_oeis_a359559
