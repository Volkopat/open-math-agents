import Mathlib

/-!
# A157002: Transform of Catalan numbers whose Hankel transform gives the Somos-4 sequence.

Source: https://oeis.org/A157002
Credit: @vivanpoddar

The sequence (offset 0) is 1, 0, 1, 2, 6, 17, 51, 156, 488, ... The entry gives the g.f.
(1 - sqrt(1 - 4*x*(1 - x^2)))/(2*x*(1+x)), that is the power series A with
x*(1+x)*A^2 - A + (1-x) = 0; equivalently a(0) = 1, a(1) = 0 and
a(n+2) = Sum_{k=0..n+1} a(k)*a(n+1-k) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used here as the
definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 19 2014) reads
(n+1)*a(n) + 3*(-n+1)*a(n-1) + 2*(-2*n+1)*a(n-2) + 2*(2*n-7)*a(n-3) + 2*(2*n-7)*a(n-4) = 0.
It involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a157002

/-- A157002 (offset 0): a(0) = 1, a(1) = 0,
a(n+2) = Sum_{k=0..n+1} a(k)*a(n+1-k) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | (n + 2) => ∑ k : Fin (n + 2), a k * a (n + 1 - k) + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A157002. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + 2 * (-2 * (n : ℤ) + 1) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 7) * a (n - 3) + 2 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a157002
