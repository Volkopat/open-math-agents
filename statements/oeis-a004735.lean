import Mathlib

/-!
# A004735: Denominator of average distance traveled by n-dimensional fly.

Source: https://oeis.org/A004735 (and https://oeis.org/A001803)
Credit: @agchua

Ralf Stephan (Mar 10 2004), in the formula section of A004735:
  a(2n) = A001803(n) (conjectured). - Ralf Stephan, Mar 10 2004
A004735 has offset 1, so the claim is stated for n >= 1.

Definition of A004735, from its comments and PARI program (Michel Marcus, May 24 2013): the
average distance is d(n) = 2*n!!/(n+1)!! for odd n and (1/Pi)*4*n!!/(n+1)!! for even n, and
a(n) = denominator(d(n)) for odd n, a(n) = denominator(Pi*d(n)) for even n, computed as
  denominator(eo*prod(i=0, floor((n-1)/2), n-2*i)/prod(i=0, floor(n/2), n+1-2*i))
with eo = 2 for odd n and eo = 4 for even n. Below `d n` is this rational number (for n >= 1,
where (n - 1) / 2 in the natural numbers is floor((n-1)/2)); it reproduces the listed terms
1, 3, 4, 15, 8, 35, 64, 315, ...
A001803 (offset 0): Numerators in expansion of (1 - x)^(-3/2); its formula section gives
a(n) = numerator((2*n+1)*binomial(2*n,n)/(4^n)) (Johannes W. Meijer), which is used below.
-/

namespace OMA.S_oeis_a004735

/-- eo * Product_{i=0..floor((n-1)/2)} (n - 2i) / Product_{i=0..floor(n/2)} (n + 1 - 2i),
with eo = 2 for odd n and eo = 4 for even n (the PARI program of A004735). -/
def d (n : ℕ) : ℚ :=
  (if n % 2 = 1 then 2 else 4) * (∏ i ∈ Finset.range ((n - 1) / 2 + 1), ((n : ℚ) - 2 * i)) /
    ∏ i ∈ Finset.range (n / 2 + 1), ((n : ℚ) + 1 - 2 * i)

/-- A004735(n) = denominator(d(n)). -/
def a (n : ℕ) : ℕ := (d n).den

/-- A001803(n) = numerator((2n+1) binomial(2n,n)/4^n). -/
def A001803 (n : ℕ) : ℤ := (((2 * n + 1) * (Nat.choose (2 * n) n) : ℚ) / 4 ^ n).num

/-- Stephan's conjecture: a(2n) = A001803(n) for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a (2 * n) : ℤ) = A001803 n := by
  sorry

end OMA.S_oeis_a004735
