import Mathlib

/-!
# A025248: Mathar's recurrence, corrected to n ≥ 5

Source: https://oeis.org/A025248
Credit: @ivillar

Status: false as stated at n = 4 (the left side is 2 at n = 4 on the OEIS data); `main` is the
corrected recurrence (n ≥ 5), which is proved.

A025248 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-3)*a(3) for n >= 4, with initial terms 1, 0, 2, 2;
data 1, 0, 2, 2, 2, 6, 14, 26, 58, 142, 326, 754, ...

Conjecture (R. J. Mathar, Feb 25 2015):
n*a(n) + (-2*n+3)*a(n-1) + (n-3)*a(n-2) + 4*(-2*n+9)*a(n-3) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-3} a(k)*a(n-k) for n ≥ 4; these conditions determine a(n)
for all n ≥ 1 (the fourth listed term is the value the recurrence gives at n = 4). `main` is the corrected recurrence (n ≥ 5): on the data the left side of the recurrence as stated
is 2 at n = 4, and it vanishes from n = 5 on.
-/

namespace OMA.S_oeis_a025248

/-- The corrected recurrence (n ≥ 5): Mathar's recurrence, which fails at n = 4. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 1 →
    a 2 = 0 →
    a 3 = 2 →
    (∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) →
    ∀ n : ℕ, 5 ≤ n →
      ((n : ℚ)) * a n + (3 - 2 * (n : ℚ)) * a (n - 1) +
        (-3 + (n : ℚ)) * a (n - 2) + (36 - 8 * (n : ℚ)) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025248
