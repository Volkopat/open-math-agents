import Mathlib

/-!
# A144636: Column 1 of triangle in A144633

Source: https://oeis.org/A144636

Offset 0; data 0, 1, -1, 2, -5, 10, 35, -910, 11935, -134750, ...
The e.g.f. A(x) = sum a(n) x^n/n! is the series reversion of x + x^2/2! + x^3/3!,
equivalently the solution with A(0) = 0 of A(x)^3 + 3*A(x)^2 + 6*A(x) = 6*x
(both stated in the entry by Peter Bala, Feb 16 2026).

Conjecture (Peter Bala, Feb 16 2026): 6^(n-1)*a(n)/n! is odd iff n is a power of 2.

Not part of the target: the remark that (1/6)*A(6*x) is an integral series satisfying
6*y^3 + 3*y^2 + y = x (it follows directly from the algebraic equation).

Formalized: A is any power series over ℚ with zero constant term satisfying
A^3 + 3*A^2 + 6*A = 6*X (this determines A uniquely, and it exists), and
a(n) = n! * coeff n A. The conjecture is read for n ≥ 1 (a(0) = 0 makes n = 0 meaningless
since 6^(n-1) is not defined there); being odd means being equal to an odd integer.
-/

namespace OMA.S_oeis_a144636

open PowerSeries

theorem main : ∀ A : PowerSeries ℚ, constantCoeff A = 0 →
    A ^ 3 + 3 * A ^ 2 + 6 * A = 6 * X →
    ∀ n : ℕ, 1 ≤ n →
      ((∃ m : ℤ, Odd m ∧
          (6 : ℚ) ^ (n - 1) * ((n.factorial : ℚ) * coeff n A) / (n.factorial : ℚ) = m) ↔
        ∃ k : ℕ, n = 2 ^ k) := by
  sorry

end OMA.S_oeis_a144636
