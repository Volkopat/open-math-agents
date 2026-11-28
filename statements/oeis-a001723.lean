import Mathlib

/-!
# A001723: Mathar's recurrence for the generalized Stirling numbers [n+8,8]_5

Source: https://oeis.org/A001723
Credit: @ivillar

A001723 (offset 0) lists the generalized Stirling numbers [n+8,8]_5;
data 1, 26, 485, 8175, 134449, 2231012, ... The entry gives the formula
a(n) = Sum_{k=0..n} (-1)^(n+k)*binomial(3+k, 3)*5^k*Stirling1(n+3, k+3)
with the signed Stirling numbers of the first kind.

Conjecture (R. J. Mathar, Jul 20 2026): the sequence is D-finite with recurrence
a(n) + 2*(-2*n-11)*a(n-1) + (6*n^2+60*n+151)*a(n-2) - (2*n+9)*(2*n^2+18*n+41)*a(n-3)
+ (n+4)^4*a(n-4) = 0.

Formalization: a(n) is defined by the entry's formula. Since Stirling1(n+3, k+3) has sign
(-1)^(n-k), the product (-1)^(n+k)*Stirling1(n+3, k+3) is the unsigned Stirling number of the
first kind, Mathlib's `Nat.stirlingFirst (n+3) (k+3)`. The recurrence is stated for every n ≥ 4,
the range in which a(n-4) is defined.
-/

namespace OMA.S_oeis_a001723

/-- a(n) = ∑_{k=0}^{n} binomial(k+3, 3) 5^k c(n+3, k+3), with c the unsigned Stirling numbers of
the first kind. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    ((k + 3).choose 3 : ℤ) * 5 ^ k * (Nat.stirlingFirst (n + 3) (k + 3) : ℤ)

/-- Mathar's conjectured recurrence. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + 2 * (-2 * (n : ℤ) - 11) * a (n - 1) + (6 * (n : ℤ) ^ 2 + 60 * n + 151) * a (n - 2) -
      (2 * (n : ℤ) + 9) * (2 * (n : ℤ) ^ 2 + 18 * n + 41) * a (n - 3) +
      ((n : ℤ) + 4) ^ 4 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a001723
