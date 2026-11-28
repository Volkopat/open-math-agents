import Mathlib

/-!
# A186335, the central-binomial transform of Paul Barry

With length marked by z and the binomial index by y, one step contributes
z + z² + y z². In a word of k steps of total length n, choose j unmarked
double steps, then n-k-j marked double steps among the remaining positions.
This gives precisely C(k,j) C(k-j,n-k-j) from the defining double sum.
Replacing y^i by C(2i,i) gives A186335. The assertion is R. J. Mathar's
recurrence of February 13, 2015, starting at n = 4.

Source: https://oeis.org/A186335
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a186335

open Polynomial Finset

noncomputable def stepPoly : Polynomial ℚ[X] :=
  (1 + Polynomial.C (1 + (Polynomial.X : ℚ[X])) * Polynomial.X) * Polynomial.X

noncomputable def profile (n : ℕ) : ℚ[X] :=
  (∑ k ∈ range (n+1), stepPoly^k).coeff n

noncomputable def moment (b : ℕ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun j => b j • LinearMap.id

noncomputable def sequence (n : ℕ) : ℚ :=
  moment (fun j => (j.centralBinom : ℚ)) (profile n)

theorem main : ∀ m : ℕ,
    let n := (m : ℚ) + 4
    n * sequence (m+4) + (1-2*n) * sequence (m+3) + 5*(1-n) * sequence (m+2)
      + 3*(2*n-3) * sequence (m+1) + 5*(n-2) * sequence m = 0 := by
  sorry

end OMA.S_oeis_a186335
