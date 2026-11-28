import Mathlib

/-!
# A152601: a(n) = Sum_{k=0..n} C(n+k,2k)*A000108(k)*3^k*2^(n-k)

Source: https://oeis.org/A152601
Credit: @sntntHb

Offset 0. Formalizes R. J. Mathar's conjectured recurrence (OEIS A152601, Nov 24 2012):
`(n+1)*a(n) + 8*(-2*n+1)*a(n-1) + 4*(n-2)*a(n-2) = 0`, stated for every `n >= 2`.
-/

namespace OMA.S_oeis_a152601

/-- A152601: `a(n) = Sum_{k=0..n} choose (n+k) (2k) * catalan k * 3^k * 2^(n-k)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), Nat.choose (n + k) (2 * k) * catalan k * 3 ^ k * 2 ^ (n - k)

/-- Mathar's conjectured second-order recurrence, for every `n >= 2`. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * (a n : ℤ) +
        8 * (-2 * (n : ℤ) + 1) * (a (n - 1) : ℤ) +
        4 * ((n : ℤ) - 2) * (a (n - 2) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a152601
