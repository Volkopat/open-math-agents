import Mathlib

/-!
# A143902: Rectangular array R by antidiagonals: R(m,n) = number of black squares.

Source: https://oeis.org/A143902
Credit: @agchua

Comment line of A143902 (Clark Kimberling, Sep 04 2008), verbatim:
  Antidiagonal sums: (2,4,10,16,28,40,60,80,...)=A006584 (conjectured).
Offset 1,5: the array starts at R(1,1). Formula line of A143902: R(m,n)=Floor(mn/2).
The k-th antidiagonal (k >= 1) consists of the entries R(m, k+1-m) for m = 1..k, and its
sums are 0, 2, 4, 10, 16, 28, ... for k = 1, 2, 3, ...; the listed values 2, 4, 10, 16, ...
are A006584(3), A006584(4), ... (A006584 has offset 0 and data 0,0,0,2,4,10,16,28,...).
So the conjecture says: the sum of the k-th antidiagonal is A006584(k+1), for every k >= 1
(k = 1 gives 0 = A006584(2)).
A006584 is defined by its name line: If n mod 2 = 0 then n*(n^2-4)/12 else n*(n^2-1)/12.
Below it is written in natural numbers; for the arguments n >= 2 used here no subtraction is
truncated and the divisions are exact.
-/

namespace OMA.S_oeis_a143902

/-- A143902: R(m,n) = floor(m*n/2). -/
def R (m n : ℕ) : ℕ := m * n / 2

/-- A006584: if n mod 2 = 0 then n*(n^2-4)/12 else n*(n^2-1)/12. -/
def A006584 (n : ℕ) : ℕ :=
  if n % 2 = 0 then n * (n ^ 2 - 4) / 12 else n * (n ^ 2 - 1) / 12

/-- The sum of the k-th antidiagonal of R is A006584(k+1). -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∑ m ∈ Finset.Icc 1 k, R m (k + 1 - m) = A006584 (k + 1) := by
  sorry

end OMA.S_oeis_a143902
