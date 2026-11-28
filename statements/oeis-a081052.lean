import Mathlib

/-!
# A081052: Difference of Stirling numbers of the first kind

Source: https://oeis.org/A081052
Credit: @ivillar

The entry has offset 0 and data 0, 1, -4, 17, -85, 499, -3388, ... Its PARI program prints
stirling(n,2) - stirling(n,3) for n = 1, 2, 3, ..., and its e.g.f. (1+x)^(-1) * (log(1+x) - log(1+x)^2/2)
is the derivative of log(1+x)^2/2 - log(1+x)^3/6. Both say that the listed term a(n) (offset 0) is
s(n+1,2) - s(n+1,3), where s(n,m) is the signed Stirling number of the first kind; the name formula
a(n) = s(n,2) - s(n,3) counts the same terms from 1. Below, s(n,m) = (-1)^(n+m) * c(n,m), where
c(n,m) = Nat.stirlingFirst n m is the unsigned Stirling number of the first kind.

Conjecture (R. J. Mathar, Nov 24 2012):
a(n) +3*(n-1)*a(n-1) +(3*n^2-9*n+7)*a(n-2) +(n-2)^3*a(n-3)=0.
It is stated for n ≥ 3 (all indices at least the offset 0), over the integers.
-/

namespace OMA.S_oeis_a081052

/-- The signed Stirling number of the first kind s(n,m). -/
def s (n m : ℕ) : ℤ := (-1) ^ (n + m) * (Nat.stirlingFirst n m : ℤ)

/-- The listed term a(n) (offset 0): s(n+1,2) - s(n+1,3). -/
def a (n : ℕ) : ℤ := s (n + 1) 2 - s (n + 1) 3

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    a n + 3 * ((n : ℤ) - 1) * a (n - 1) + (3 * (n : ℤ) ^ 2 - 9 * n + 7) * a (n - 2) +
      ((n : ℤ) - 2) ^ 3 * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081052
