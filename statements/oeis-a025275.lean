import Mathlib

/-!
# A025275: Mathar's recurrence

Source: https://oeis.org/A025275
Credit: @ivillar

Status: known result. The entry records that the conjectured recurrence is true for n >= 5, with a proof through the
g.f. equation A(x)^2 - A(x) = -x + x^2 - x^3 + 2*x^4.

A025275 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-1)*a(1) for n >= 5, with initial values 1, 0, 1, 0;
data 1, 0, 1, 0, 0, 1, 2, 4, 10, 24, 56, 133, ...

Conjecture (R. J. Mathar, May 30 2014):
n*a(n) + 2*(-2*n+3)*a(n-1) + 4*(n-3)*a(n-2) + 2*(-2*n+9)*a(n-3) + 8*(n-6)*a(n-4) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-1} a(k)*a(n-k) for n ≥ 5; these conditions determine a(n)
for all n ≥ 1. The sequence has offset 1 and a(0) is not constrained, so the recurrence, which involves
a(n-4), is stated for n ≥ 5, where every index is at least 1; it is checked by the data, for
example at n = 5: (5)*(0) + (-14)*(0) + (8)*(1) + (-2)*(0) + (-8)*(1) = 0.
-/

namespace OMA.S_oeis_a025275

/-- Mathar's conjectured recurrence for A025275, for n ≥ 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    a 2 = 0 →
    a 3 = 1 →
    a 4 = 0 →
    (∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * a n + (6 - 4 * (n : ℚ)) * a (n - 1) +
        (-12 + 4 * (n : ℚ)) * a (n - 2) + (18 - 4 * (n : ℚ)) * a (n - 3) +
        (-48 + 8 * (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025275
