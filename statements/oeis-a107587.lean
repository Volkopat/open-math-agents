import Mathlib

/-!
# A107587: Number of Motzkin n-paths with an even number of up steps

Source: https://oeis.org/A107587
Credit: @sntntHb

The sequence (offset 0: `1, 1, 1, 1, 3, 11, 31, 71, 155, 379, ...`) counts Motzkin paths of
length `n` with an even number of up steps. The entry gives the formula
`a(n) = Sum_{k=0..floor(n/2)} binomial(n, 2*k) * A000108(k) * ((k+1) mod 2)`
(choose the `2k` positions of the up and down steps, a Dyck word on them, and keep `k` even),
which we use as the definition; Mathlib's `catalan` is A000108.
The entry records two conjectures (R. J. Mathar, Feb 20 2015; checked for `n = 0..800` by
Gennady Eremin, Jan 25 2021):
1. `n*(n+2)*a(n) + (-5*n^2-n+3)*a(n-1) + (10*n^2-16*n+3)*a(n-2) + (-10*n^2+34*n-27)*a(n-3)
   - (11*n-5)*(n-3)*a(n-4) + 15*(n-3)*(n-4)*a(n-5) = 0`;
2. `n*(n-2)*(n+2)*a(n) - (2*n-1)*(2*n^2-2*n-3)*a(n-1) + 3*(n-1)*(2*n^2-4*n+1)*a(n-2)
   - 2*(n-1)*(n-2)*(2*n-3)*a(n-3) - 15*(n-1)*(n-2)*(n-3)*a(n-4) = 0`.

`main` is their conjunction, each stated where all its terms are defined (offset 0): the first
for `n ≥ 5`, the second for `n ≥ 4`. The identities are stated over `ℤ`.
-/

namespace OMA.S_oeis_a107587

/-- `a n = ∑_{k=0}^{⌊n/2⌋} binomial(n, 2k) * catalan k * ((k+1) mod 2)` (OEIS A107587). -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n / 2 + 1), Nat.choose n (2 * k) * catalan k * ((k + 1) % 2)

/-- R. J. Mathar's two conjectured recurrences for OEIS A107587. -/
theorem main :
    (∀ n : ℕ, 5 ≤ n →
      (n : ℤ) * ((n : ℤ) + 2) * (a n : ℤ) + (-5 * (n : ℤ) ^ 2 - n + 3) * (a (n - 1) : ℤ) +
        (10 * (n : ℤ) ^ 2 - 16 * n + 3) * (a (n - 2) : ℤ) +
        (-10 * (n : ℤ) ^ 2 + 34 * n - 27) * (a (n - 3) : ℤ) -
        (11 * (n : ℤ) - 5) * ((n : ℤ) - 3) * (a (n - 4) : ℤ) +
        15 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * (a (n - 5) : ℤ) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (n : ℤ) * ((n : ℤ) - 2) * ((n : ℤ) + 2) * (a n : ℤ) -
        (2 * (n : ℤ) - 1) * (2 * (n : ℤ) ^ 2 - 2 * n - 3) * (a (n - 1) : ℤ) +
        3 * ((n : ℤ) - 1) * (2 * (n : ℤ) ^ 2 - 4 * n + 1) * (a (n - 2) : ℤ) -
        2 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 * (n : ℤ) - 3) * (a (n - 3) : ℤ) -
        15 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (a (n - 4) : ℤ) = 0) := by
  sorry

end OMA.S_oeis_a107587
