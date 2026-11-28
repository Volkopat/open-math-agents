import Mathlib

/-!
OEIS A084091: Expansion of Sum_{k>=0} x^2^k/(1+x^2^k+x^2^(k+1)).

With G(x) = x/(1+x+x^2), the coefficient of x^n (n >= 1) in Sum_{k>=0} G(x^(2^k)) is
Sum_{k>=0, 2^k | n} [x^(n/2^k)] G(x); only k <= n contribute.

Conjecture (Ralf Stephan, 2015): the Dirichlet g.f. is L(chi_2(3), s)/(1 - 2^(-s)), where
chi_2(3) is the nontrivial Dirichlet character modulo 3, i.e. for n >= 1
a(n) = Sum_{d*e = n, e a power of 2} chi(d), with chi(d) = 1, -1, 0 for d = 1, 2, 0 (mod 3).
-/

namespace OMA.S_oeis_a084091

open PowerSeries in
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (∑ k ∈ Finset.range (n + 1),
          if 2 ^ k ∣ n then
            coeff (n / 2 ^ k) (X * (1 + X + X ^ 2 : PowerSeries ℚ)⁻¹)
          else 0) =
        ∑ d ∈ n.divisors,
          (if (n / d).primeFactors ⊆ {2} then
            (if d % 3 = 1 then (1 : ℚ) else if d % 3 = 2 then -1 else 0)
          else 0) := by
  sorry

end OMA.S_oeis_a084091
