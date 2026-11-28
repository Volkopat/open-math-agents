import Mathlib

/-!
# A187916: a(n) = C(n) if n is odd, else C(n) - C(n/2); C(n) are Catalan numbers

Source: https://oeis.org/A187916
Credit: @ivillar

Gary W. Adamson's sequence (offset 1): a(n) = C(n) for odd n and a(n) = C(n) - C(n/2) for even
n, where C(n) are the Catalan numbers (data 1, 1, 5, 12, 42, ...). The values are integers.

Conjecture (R. J. Mathar, Jul 21 2015):
  -(n-2)*(n+2)*(n+1)*a(n) +8*(n+1)*(n^2-3*n+1)*a(n-1) +4*(-3*n^3+18*n^2-22*n+2)*a(n-2)
  -32*(n-2)*(n^2-3*n+1)*a(n-3) +16*(2*n-7)*(n-3)*(2*n-3)*a(n-4) = 0,
stated for every n ≥ 5 (all indices at least the offset 1), in ℤ.
-/

namespace OMA.S_oeis_a187916

/-- a(n) = C(n) if n is odd, else C(n) - C(n/2), with C = Mathlib's `catalan` (offset 1). -/
def a (n : ℕ) : ℤ := if n % 2 = 1 then (catalan n : ℤ) else (catalan n : ℤ) - catalan (n / 2)

/-- Mathar's conjecture, for every n ≥ 5 (so that a(n-4) is defined). -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    -((n : ℤ) - 2) * ((n : ℤ) + 2) * ((n : ℤ) + 1) * a n
      + 8 * ((n : ℤ) + 1) * ((n : ℤ) ^ 2 - 3 * n + 1) * a (n - 1)
      + 4 * (-3 * (n : ℤ) ^ 3 + 18 * (n : ℤ) ^ 2 - 22 * n + 2) * a (n - 2)
      - 32 * ((n : ℤ) - 2) * ((n : ℤ) ^ 2 - 3 * n + 1) * a (n - 3)
      + 16 * (2 * (n : ℤ) - 7) * ((n : ℤ) - 3) * (2 * (n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a187916
