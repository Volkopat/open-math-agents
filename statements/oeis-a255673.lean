import Mathlib

/-!
# A255673: Coefficients of A(x), which satisfies: A(x) = 1 + x*A(x)^3 + x^2*A(x)^6.

Source: https://oeis.org/A255673
Credit: @Harsha0912

Conjectures (formula section of A255673), both stated:
* a(n+1) = Sum_{j=0..3*n+4} binomial(j,2*j-5*n-7) * binomial(3*n+4,j) / (3*n+4)
  (Vladimir Kruchinin, Mar 09 2013).
* a(n) = 1/(3*n+1) * Sum_{k=0..n} (-1)^k * binomial(3*n+1, k) * binomial(6*n+2-2*k, n-k).

Conventions:
* Offset 0: a(n) is the coefficient of x^n in the power series A over the rationals with
  A = 1 + x*A^3 + x^2*A^6 (this equation determines A uniquely; it forces A(0) = 1). The
  statement quantifies over every such A.
* n ranges over all n >= 0 in both formulas (no range is given in the source).
* binomial(j, m) is 0 when m < 0, as is standard on OEIS; it is also 0 when m > j.
* Both formulas are stated in the rationals.
-/

namespace OMA.S_oeis_a255673

open PowerSeries

/-- `binomial(j, m)` for an integer lower index `m`, which is `0` when `m < 0`. -/
def binomZ (j : ℕ) (m : ℤ) : ℚ := if 0 ≤ m then (j.choose m.toNat : ℚ) else 0

/-- Both conjectured closed forms for the coefficients of `A = 1 + x A^3 + x^2 A^6`. -/
theorem main : ∀ A : PowerSeries ℚ, A = 1 + X * A ^ 3 + X ^ 2 * A ^ 6 →
    (∀ n : ℕ, coeff (n + 1) A =
      (∑ j ∈ Finset.range (3 * n + 5),
        binomZ j (2 * (j : ℤ) - 5 * n - 7) * ((3 * n + 4).choose j : ℚ)) / (3 * n + 4)) ∧
    (∀ n : ℕ, coeff n A =
      1 / (3 * n + 1 : ℚ) * ∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ k * ((3 * n + 1).choose k : ℚ) * ((6 * n + 2 - 2 * k).choose (n - k) : ℚ)) := by
  sorry

end OMA.S_oeis_a255673
