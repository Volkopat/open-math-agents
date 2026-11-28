import Mathlib

/-!
# A129695: Laguerre transform of the Jacobsthal numbers.

Source: https://oeis.org/A129695
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A129695 (R. J. Mathar, Feb 23 2015):
a(n) +(-4*n+3)*a(n-1) +(6*n^2-16*n+9)*a(n-2) -(4*n-7)*(n-2)^2*a(n-3) +(n-2)^2*(n-3)^2*a(n-4)=0.

Conventions:
* The sequence has offset 0 (data 0, 1, 5, 30, 221, 1936, 19587, 223924, ...).
* The Laguerre transform is the one given by the first formula of the entry (and by its Maple
  program): a(n) = Sum_{k=0..n} C(n,k)*n!*A001045(k)/k!.
* A001045 is the Jacobsthal sequence, `J` below: J(0) = 0, J(1) = 1 and
  J(n) = J(n-1) + 2*J(n-2) (0, 1, 1, 3, 5, 11, 21, ...).
* Each term C(n,k)*n!*J(k)/k! is formed in `ℚ` so that the division by k! is exact; a(n) is
  defined as a rational number (it is an integer, since k! divides n! for k <= n).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3, n-4 are at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a129695

/-- A001045, the Jacobsthal numbers: J(0) = 0, J(1) = 1, J(n) = J(n-1) + 2*J(n-2). -/
def J : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => J (n + 1) + 2 * J n

/-- A129695 (offset 0): a(n) = Sum_{k=0..n} C(n,k)*n!*A001045(k)/k!. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℚ) * (n.factorial : ℚ) * (J k : ℚ) / (k.factorial : ℚ)

/-- For every `n ≥ 4`, a(n) + (-4*n+3)*a(n-1) + (6*n^2-16*n+9)*a(n-2)
- (4*n-7)*(n-2)^2*a(n-3) + (n-2)^2*(n-3)^2*a(n-4) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    a n + (-4 * (n : ℚ) + 3) * a (n - 1) + (6 * (n : ℚ) ^ 2 - 16 * (n : ℚ) + 9) * a (n - 2)
      - (4 * (n : ℚ) - 7) * ((n : ℚ) - 2) ^ 2 * a (n - 3)
      + ((n : ℚ) - 2) ^ 2 * ((n : ℚ) - 3) ^ 2 * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a129695
