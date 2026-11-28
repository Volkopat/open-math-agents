import Mathlib

/-!
# A186334, the Catalan transform of Paul Barry

With length marked by z and the binomial index by y, one step contributes
z + z² + y z². In a word of k steps of total length n, choose j unmarked
double steps, then n-k-j marked double steps among the remaining positions.
This gives precisely C(k,j) C(k-j,n-k-j) from the defining double sum.
Replacing y^i by the i-th Catalan number gives A186334. The assertion is
R. J. Mathar's recurrence of November 7, 2014, starting at n = 4.

Source: https://oeis.org/A186334
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a186334

open Polynomial Finset

noncomputable def stepPoly : Polynomial ℚ[X] :=
  (1 + Polynomial.C (1 + (Polynomial.X : ℚ[X])) * Polynomial.X) * Polynomial.X

noncomputable def profile (n : ℕ) : ℚ[X] :=
  (∑ k ∈ range (n+1), stepPoly^k).coeff n

noncomputable def moment (b : ℕ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun j => b j • LinearMap.id

noncomputable def sequence (n : ℕ) : ℚ :=
  moment (fun j => (catalan j : ℚ)) (profile n)

theorem main : ∀ m : ℕ,
    let n := (m : ℚ) + 4
    (n+2) * sequence (m+4) + 2*(-n-1) * sequence (m+3) + (4-5*n) * sequence (m+2)
      + 2*(3*n-4) * sequence (m+1) + 5*(n-2) * sequence m = 0 := by
  sorry

end OMA.S_oeis_a186334
