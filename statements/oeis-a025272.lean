import Mathlib

/-!
# A025272: Mathar's recurrence

Source: https://oeis.org/A025272
Credit: @ivillar

Status: known result. The entry also records the recurrence n*a(n) = 2*(2*n-3)*a(n-1) - 2*(2*n-9)*a(n-3) - 4*(n-6)*a(n-4)
(Vaclav Kotesovec, Jan 25 2015); the conjectured recurrence is that recurrence at n plus 5 times
that recurrence at n-1.

A025272 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-1)*a(1) for n >= 5, with initial values 1, 1, 1, 2;
data 1, 1, 1, 2, 6, 17, 50, 150, 458, 1420, 4460, 14165, ...

Conjecture (R. J. Mathar, Nov 21 2014):
n*a(n) + (n+1)*a(n-1) + 10*(-2*n+5)*a(n-2) + 2*(2*n-9)*a(n-3) + 2*(12*n-67)*a(n-4) + 20*(n-7)*a(n-5) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-1} a(k)*a(n-k) for n ≥ 5; these conditions determine a(n)
for all n ≥ 1. The sequence has offset 1 and a(0) is not constrained, so the recurrence, which involves
a(n-5), is stated for n ≥ 6, where every index is at least 1; it is checked by the data, for
example at n = 6: (6)*(17) + (7)*(6) + (-70)*(2) + (6)*(1) + (10)*(1) + (-20)*(1) = 0.
-/

namespace OMA.S_oeis_a025272

/-- Mathar's conjectured recurrence for A025272, for n ≥ 6. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    a 2 = 1 →
    a 3 = 1 →
    a 4 = 2 →
    (∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) →
    ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)) * a n + (1 + (n : ℚ)) * a (n - 1) +
        (50 - 20 * (n : ℚ)) * a (n - 2) + (-18 + 4 * (n : ℚ)) * a (n - 3) +
        (-134 + 24 * (n : ℚ)) * a (n - 4) + (-140 + 20 * (n : ℚ)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a025272
