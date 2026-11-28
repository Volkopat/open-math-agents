import Mathlib

/-!
# A025273: Mathar's recurrence

Source: https://oeis.org/A025273
Credit: @ivillar

Status: known result. The entry records that the conjecture follows from a differential equation satisfied by the
g.f. (Robert Israel, Nov 02 2016).

A025273 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-1)*a(1) for n >= 5, starting 1, 0, 1, 1;
data 1, 0, 1, 1, 2, 5, 12, 29, 72, 182, 466, 1207, ...

Conjecture (R. J. Mathar, Nov 24 2012):
(with offset 0 instead of 1) (n+1)*a(n) + 2*(-2*n+1)*a(n-1) + 4*(n-2)*a(n-2) + 2*(-2*n+7)*a(n-3)
+ 4*(n-5)*a(n-4) = 0. With the offset 1 of the entry, which is used here, this reads
n*a(n) + 2*(-2*n+3)*a(n-1) + 4*(n-3)*a(n-2) + 2*(-2*n+9)*a(n-3) + 4*(n-6)*a(n-4) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-1} a(k)*a(n-k) for n ≥ 5; these conditions determine a(n)
for all n ≥ 1. The sequence has offset 1 and a(0) is not constrained, so the recurrence, which involves
a(n-4), is stated for n ≥ 5, where every index is at least 1; it is checked by the data, for
example at n = 5: (5)*(2) + (-14)*(1) + (8)*(1) + (-2)*(0) + (-4)*(1) = 0.
-/

namespace OMA.S_oeis_a025273

/-- Mathar's conjectured recurrence for A025273, for n ≥ 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    a 2 = 0 →
    a 3 = 1 →
    a 4 = 1 →
    (∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * a n + (6 - 4 * (n : ℚ)) * a (n - 1) +
        (-12 + 4 * (n : ℚ)) * a (n - 2) + (18 - 4 * (n : ℚ)) * a (n - 3) +
        (-24 + 4 * (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025273
