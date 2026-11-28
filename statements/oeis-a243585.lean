import Mathlib

/-!
# A243585: Expansion of x*log'(C(C(x)-1)-1), C(x) = (1-sqrt(1-4*x))/(2*x).

Source: https://oeis.org/A243585
Credit: @agchua

R. J. Mathar (Jun 14 2016), in the formula section of A243585, verbatim:
  Conjecture D-finite with recurrence: 2*n*(2*n-1)*(3*n-5)*a(n) +(-123*n^3+328*n^2-249*n+60)*a(n-1)
  +50*(n-1)*(2*n-3)*(3*n-2)*a(n-2)=0.
Offset 0. Definition: the explicit formula of the entry (its first formula line, and its Maxima
program), a(n) = Sum_{k=0..n} binomial(2*k,k)*binomial(2*n,n-k), is used below. The recurrence is
stated over the integers for every n >= 2, the range in which all three indices are terms.
-/

namespace OMA.S_oeis_a243585

/-- A243585: a(n) = Sum_{k=0..n} binomial(2k,k) * binomial(2n,n-k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), Nat.choose (2 * k) k * Nat.choose (2 * n) (n - k)

/-- Mathar's conjectured recurrence, for every n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    2 * (n : ℤ) * (2 * n - 1) * (3 * n - 5) * a n
      + (-123 * (n : ℤ) ^ 3 + 328 * n ^ 2 - 249 * n + 60) * a (n - 1)
      + 50 * ((n : ℤ) - 1) * (2 * n - 3) * (3 * n - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a243585
