import Mathlib

/-!
# A025270: Mathar's recurrence

Source: https://oeis.org/A025270
Credit: @ivillar

Status: known result. The entry records that the conjectured recurrence follows from the generating function, for
n >= 5 (Eiver Rodríguez, Nov 04 2026).

A025270 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-1)*a(1) for n >= 5, with initial values 1, 2, 1, 1;
data 1, 2, 1, 1, 6, 17, 60, 201, 688, 2370, 8218, 28703, ...

Conjecture (R. J. Mathar, Nov 21 2014):
n*a(n) + 2*(-2*n+3)*a(n-1) + 4*(-n+3)*a(n-2) + 6*(2*n-9)*a(n-3) + 20*(n-6)*a(n-4) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-1} a(k)*a(n-k) for n ≥ 5; these conditions determine a(n)
for all n ≥ 1. The sequence has offset 1 and a(0) is not constrained, so the recurrence, which involves
a(n-4), is stated for n ≥ 5, where every index is at least 1; it is checked by the data, for
example at n = 5: (5)*(6) + (-14)*(1) + (-8)*(1) + (6)*(2) + (-20)*(1) = 0.
-/

namespace OMA.S_oeis_a025270

/-- Mathar's conjectured recurrence for A025270, for n ≥ 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    a 2 = 2 →
    a 3 = 1 →
    a 4 = 1 →
    (∀ n : ℕ, 5 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 1), a k * a (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * a n + (6 - 4 * (n : ℚ)) * a (n - 1) +
        (12 - 4 * (n : ℚ)) * a (n - 2) + (-54 + 12 * (n : ℚ)) * a (n - 3) +
        (-120 + 20 * (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025270
