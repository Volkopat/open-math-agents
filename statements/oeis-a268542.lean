import Mathlib

/-!
# A268542: The diagonal of the rational function 1/(1 - x - y - x y - x z - y z).

Source: https://oeis.org/A268542
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A268542 (R. J. Mathar,
Mar 11 2016):
2*n^2*(21*n-37)*a(n) -32*(7*n-3)*(3*n^2-7*n+3)*a(n-1) +(-1281*n^3+4819*n^2-5610*n+1920)*a(n-2)
-3*(3*n-5)*(21*n-16)*(3*n-7)*a(n-3) = 0.

Conventions:
* The sequence has offset 0 (data 1, 4, 42, 520, 7090, 102144, ...). The diagonal is rendered
  through the explicit binomial sum given in the FORMULA section of the entry
  (Seiichi Manyama, Feb 15 2026):
  a(n) = Sum_{k=0..n} binomial(n,k) * binomial(n+k,k) * binomial(2*k,n).
  Binomial coefficients are `Nat.choose`, the sum over k = 0..n is `Finset.range (n + 1)`,
  and the terms are cast to `ℤ`.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which the indices n, n-1, n-2, n-3 are all at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a268542

/-- A268542 (offset 0): a(n) = Sum_{k=0..n} binomial(n,k)*binomial(n+k,k)*binomial(2k,n). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℤ) * ((n + k).choose k : ℤ) * ((2 * k).choose n : ℤ)

/-- For every `n ≥ 3`,
2*n^2*(21*n-37)*a(n) - 32*(7*n-3)*(3*n^2-7*n+3)*a(n-1)
+ (-1281*n^3+4819*n^2-5610*n+1920)*a(n-2) - 3*(3*n-5)*(21*n-16)*(3*n-7)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℤ) ^ 2 * (21 * (n : ℤ) - 37) * a n
      - 32 * (7 * (n : ℤ) - 3) * (3 * (n : ℤ) ^ 2 - 7 * (n : ℤ) + 3) * a (n - 1)
      + (-1281 * (n : ℤ) ^ 3 + 4819 * (n : ℤ) ^ 2 - 5610 * (n : ℤ) + 1920) * a (n - 2)
      - 3 * (3 * (n : ℤ) - 5) * (21 * (n : ℤ) - 16) * (3 * (n : ℤ) - 7) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a268542
