import Mathlib

/-!
# A059304: a(n) = 2^n * (2*n)! / (n!)^2

Source: https://oeis.org/A059304
Credit: @AkiRA-COM-FP

Formalizes Peter Bala's OEIS A059304 identity: for every `n >= 0`,
`a(n) = Sum_{0 <= j, k <= n} binomial(n, j) * binomial(n, k) * binomial(j + k, n)`.
-/

namespace OMA.S_oeis_a059304

/-- The OEIS sequence A059304: `a(n) = 2^n * (2*n)! / (n!)^2`. -/
def a (n : ℕ) : ℕ :=
  2 ^ n * (2 * n).factorial / (n.factorial ^ 2)

/-- For all `n >= 0`, `a(n) = Sum_{0 <= j, k <= n} C(n, j) * C(n, k) * C(j + k, n)`. -/
theorem main :
    ∀ n : ℕ,
      a n = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        Nat.choose n j * Nat.choose n k * Nat.choose (j + k) n := by
  sorry

end OMA.S_oeis_a059304
