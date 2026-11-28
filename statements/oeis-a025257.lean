import Mathlib

/-!
# A025257: Mathar's recurrence

Source: https://oeis.org/A025257
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A025257 (offset 1): a(n) = (1/3)*s(n+3), where s = A025256, the sequence with s(n) = s(1)*s(n-1) + s(2)*s(n-2) + ... +
s(n-3)*s(3) for n >= 4 and initial terms 1, 1, 3, 3;
data 1, 2, 6, 14, 35, 97, 264, 727, 2059, 5876, 16893, 49085, ...

Conjecture (R. J. Mathar, Feb 25 2015):
(n+3)*a(n) + (-2*n-3)*a(n-1) - n*a(n-2) + 5*(-2*n+3)*a(n-3) + (n-3)*a(n-4) = 0.

Formalization: s is any sequence ℕ → ℚ with the initial values and the defining recurrence of
A025256, written as s(n) = Sum_{k=1..n-3} s(k)*s(n-k) for n ≥ 4 (these determine s(n) for all n ≥ 1), and
a is any sequence with a(n) = s(n+3)/3 for n ≥ 1. The sequence has offset 1 and a(0) is not
constrained, so the recurrence, which involves a(n-4), is stated for n ≥ 5; it is checked by the
data, for example at n = 5: (8)*(35) + (-13)*(14) + (-5)*(6) + (-35)*(2) + (2)*(1) = 0.
-/

namespace OMA.S_oeis_a025257

/-- Mathar's conjectured recurrence for A025257, for n ≥ 5. -/
theorem main : ∀ s : ℕ → ℚ, s 1 = 1 →
    s 2 = 1 →
    s 3 = 3 →
    (∀ n : ℕ, 4 ≤ n → s n = ∑ k ∈ Finset.Icc 1 (n - 3), s k * s (n - k)) →
    ∀ a : ℕ → ℚ, (∀ n : ℕ, 1 ≤ n → a n = s (n + 3) / 3) →
    ∀ n : ℕ, 5 ≤ n →
      (3 + (n : ℚ)) * a n + (-3 - 2 * (n : ℚ)) * a (n - 1) +
        (-(n : ℚ)) * a (n - 2) + (15 - 10 * (n : ℚ)) * a (n - 3) +
        (-3 + (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025257
