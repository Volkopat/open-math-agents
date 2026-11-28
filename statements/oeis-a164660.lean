import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Defs

/-!
# OEIS A164660, definite integrals of the first-kind Chebyshev polynomials

The rational row sum in Wolfdieter Lang's entry is the integral over [0,1].
Each monomial x^j contributes its coefficient divided by j+1. The numerator
is taken in lowest terms, as for the OEIS numerator/denominator pair.
The second conjecture is Anthony Browne's 2016 product. A003557 is n divided
by its largest squarefree divisor, the product of its distinct prime factors.
Sources: https://oeis.org/A164660, https://oeis.org/A164661, https://oeis.org/A003557
Credit: @KoaOkano
-/

open Polynomial

namespace OMA.S_oeis_a164660

noncomputable def moment : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun j => ((j:ℚ)+1)⁻¹ • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

noncomputable def r (n : ℕ) : ℚ := moment (Chebyshev.T ℚ (n:ℤ))

def radical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

def browneProduct (n : ℕ) : ℤ :=
  ∏ k ∈ Finset.Ioc 0 n, (1 - 2 * (((k^n / n : ℕ):ℤ) - (((k^n-1) / n : ℕ):ℤ)))

theorem main :
    (r 0 = 1 ∧ ∀ n : ℕ, 0 < n → r n =
      if Even n then -1 / (((n:ℚ)-1)*((n:ℚ)+1))
      else (-1:ℚ)^((n-1)/2) / (2*(2*(((n-1)/4:ℕ):ℚ)+1))) ∧
    ∀ n : ℕ, 0 < n → (r (n+1)).num = browneProduct n ∧
      browneProduct n = (-1:ℤ)^(n / radical n) := by
  sorry

end OMA.S_oeis_a164660
