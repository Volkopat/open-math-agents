import Mathlib

/-!
# A225887: a(n) = A212205(2*n + 1).

Source: https://oeis.org/A225887
Credit: @vivanpoddar

The sequence (offset 0) is 1, 4, 18, 86, 426, 2162, 11166, 58438, ... The entry records that the g.f.
satisfies A(x) = 1 + x*A(x)*(5 - A(x)*(1 - 6*x)), that is a(0) = 1, a(1) = 4 and
a(n+2) = 5*a(n+1) - Sum_{k=0..n+1} a(k)*a(n+1-k) + 6*Sum_{k=0..n} a(k)*a(n-k). This recursion is used
here as the definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar, May 23 2014) reads
(n+1)*a(n) + 3*(-4*n-1)*a(n-1) + (37*n-20)*a(n-2) + 6*(-n+2)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a225887

/-- A225887 (offset 0): the coefficients of the series A with A = 1 + x*A*(5 - A*(1 - 6*x)). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | (n + 2) => 5 * a (n + 1) - ∑ k : Fin (n + 2), a k * a (n + 1 - k)
      + 6 * ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A225887. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-4 * (n : ℤ) - 1) * a (n - 1) + (37 * (n : ℤ) - 20) * a (n - 2)
      + 6 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a225887
