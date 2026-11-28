import Mathlib

/-!
# A025269: Mathar's recurrence

Source: https://oeis.org/A025269
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there.

A025269 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-1)*a(1) for n >= 5, with initial values 2, 1, 1, 1;
data 2, 1, 1, 1, 6, 27, 122, 555, 2530, 11564, 52994, 243467, ...

Conjecture (R. J. Mathar, Nov 21 2014):
n*a(n) + 4*(-2*n+3)*a(n-1) + 12*(n-3)*a(n-2) + 6*(2*n-9)*a(n-3) + 16*(n-6)*a(n-4) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n - 1} a(k)*a(n-k) for n ≥ 5; these conditions determine a(n)
for all n ≥ 1. The sequence has offset 1 and a(0) is not constrained, so the recurrence, which involves
a(n-4), is stated for n ≥ 5, where every index is at least 1; it is checked by the data, for
example at n = 5: (5)*(6) + (-28)*(1) + (24)*(1) + (6)*(1) + (-16)*(2) = 0.
-/

namespace OMA.S_oeis_a025269

/-- Mathar's conjectured recurrence for A025269, for n ≥ 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 2 →
    a 2 = 1 →
    a 3 = 1 →
    a 4 = 1 →
    (∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * a n + (12 - 8 * (n : ℚ)) * a (n - 1) +
        (-36 + 12 * (n : ℚ)) * a (n - 2) + (-54 + 12 * (n : ℚ)) * a (n - 3) +
        (-96 + 16 * (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025269
