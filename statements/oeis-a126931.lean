import Mathlib

/-!
# A126931: a(n) = A127359(n+1)/2 - A127359(n).

Source: https://oeis.org/A126931
Credit: @vivanpoddar

The sequence (offset 0) is 1, 3, 10, 33, 110, 366, 1220, 4065, ... The entry gives the g.f.
2/(1 - 6*x + sqrt(1 - 4*x^2)) (E. Deutsch, May 02 2011), that is the power series A with A(0) = 1 and
x*(10*x - 3)*A^2 - (1 - 6*x)*A + 1 = 0; equivalently a(0) = 1, a(1) = 3 and
a(n+2) = 6*a(n+1) - 3*Sum_{k=0..n+1} a(k)*a(n+1-k) + 10*Sum_{k=0..n} a(k)*a(n-k). This recursion is
used here as the definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 26 2012) reads
3*(n+1)*a(n) + 10*(-n-1)*a(n-1) + 12*(-n+2)*a(n-2) + 40*(n-2)*a(n-3) = 0.
It involves a(n-3), so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a126931

/-- A126931 (offset 0): a(0) = 1, a(1) = 3,
a(n+2) = 6*a(n+1) - 3*Sum_{k=0..n+1} a(k)*a(n+1-k) + 10*Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 3
  | (n + 2) => 6 * a (n + 1) - 3 * ∑ k : Fin (n + 2), a k * a (n + 1 - k)
      + 10 * ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A126931. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    3 * ((n : ℤ) + 1) * a n + 10 * (-(n : ℤ) - 1) * a (n - 1) + 12 * (-(n : ℤ) + 2) * a (n - 2)
      + 40 * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a126931
