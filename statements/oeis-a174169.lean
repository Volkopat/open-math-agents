import Mathlib

/-!
# A174169: A generalized Chebyshev transform of the Motzkin numbers A001006.

Source: https://oeis.org/A174169
Credit: @vivanpoddar

The sequence (offset 0) is 1, 1, -1, -2, 0, 0, -3, 1, 8, 1, 1, 26, ... The entry records that the g.f.
satisfies A(x) = (1 + x^2*A(x)^2) / (1 - x + 3*x^2) (S. Manyama, Oct 17 2025), that is
a(0) = 1, a(1) = 1 and a(n+2) = a(n+1) - 3*a(n) + Sum_{k=0..n} a(k)*a(n-k). This recursion is used
here as the definition (it reproduces the data of the entry).

The conjecture (R. J. Mathar, Sep 30 2012) reads
(n+2)*a(n) - (2*n+1)*a(n-1) + 3*(n-1)*a(n-2) + 3*(5-2*n)*a(n-3) + 9*(n-4)*a(n-4) = 0.
It involves a(n-4), so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a174169

/-- A174169 (offset 0): a(0) = 1, a(1) = 1, a(n+2) = a(n+1) - 3*a(n) + Sum_{k=0..n} a(k)*a(n-k). -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | (n + 2) => a (n + 1) - 3 * a n + ∑ k : Fin (n + 1), a k * a (n - k)

/-- Mathar's conjectured recurrence for A174169. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 2) * a n - (2 * (n : ℤ) + 1) * a (n - 1) + 3 * ((n : ℤ) - 1) * a (n - 2)
      + 3 * (5 - 2 * (n : ℤ)) * a (n - 3) + 9 * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a174169
