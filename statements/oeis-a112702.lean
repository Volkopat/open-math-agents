import Mathlib

/-!
# A112702: Partial sum of Catalan numbers A000108 multiplied by powers of 8

Source: https://oeis.org/A112702
Credit: @sntntHb

`a(n) = Sum_{k=0..n} 8^k * A000108(k)`, offset 0.

Formalizes R. J. Mathar's conjectured recurrence (OEIS A112702, Jun 08 2016):
`(n+1)*a(n) + 3*(-11*n+5)*a(n-1) + 16*(2*n-1)*a(n-2) = 0`, stated for every `n >= 2`.
-/

namespace OMA.S_oeis_a112702

/-- A112702: `a(n) = Sum_{k=0..n} 8^k * catalan k`. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), 8 ^ k * catalan k

/-- Mathar's conjectured second-order recurrence, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) +
        3 * (-11 * (n : ℤ) + 5) * (a (n - 1) : ℤ) +
        16 * (2 * (n : ℤ) - 1) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a112702
