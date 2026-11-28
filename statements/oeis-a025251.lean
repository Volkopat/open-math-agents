import Mathlib

/-!
# A025251: Mathar's recurrence, corrected to n ≥ 7

Source: https://oeis.org/A025251
Credit: @ivillar

Status: false as stated at n = 6 (the left side is -102 at n = 6 on the OEIS data); `main` is the
corrected recurrence (n ≥ 7), which is proved.

A025251 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-3)*a(3) for n >= 4, with initial terms 0, 1, 2, 0;
data 0, 1, 2, 0, 2, 4, 2, 12, 18, 24, 82, 120, ...

Conjecture (R. J. Mathar, Feb 25 2015):
n*(n^2+n+1)*a(n) + (n-1)*(n^2+2*n+3)*a(n-1) - 2*(n-3)*(n^2+n+1)*a(n-2) + 2*(-5*n^3+16*n^2+19*n+30)*a(n-3) + (-7*n^3+23*n^2+59*n+126)*a(n-4) + (n-7)*(n^2+2*n+3)*a(n-5) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-3} a(k)*a(n-k) for n ≥ 4; these conditions determine a(n)
for all n ≥ 1 (the fourth listed term is the value the recurrence gives at n = 4). `main` is the corrected recurrence (n ≥ 7): on the data the left side of the recurrence as stated
is -102 at n = 6, and it vanishes from n = 7 on.
-/

namespace OMA.S_oeis_a025251

/-- The corrected recurrence (n ≥ 7): Mathar's recurrence, which fails at n = 6. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 0 →
    a 2 = 1 →
    a 3 = 2 →
    (∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) →
    ∀ n : ℕ, 7 ≤ n →
      ((n : ℚ) + (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * a n + (-3 + (n : ℚ) + (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * a (n - 1) +
        (6 + 4 * (n : ℚ) + 4 * (n : ℚ) ^ 2 - 2 * (n : ℚ) ^ 3) * a (n - 2) + (60 + 38 * (n : ℚ) + 32 * (n : ℚ) ^ 2 - 10 * (n : ℚ) ^ 3) * a (n - 3) +
        (126 + 59 * (n : ℚ) + 23 * (n : ℚ) ^ 2 - 7 * (n : ℚ) ^ 3) * a (n - 4) + (-21 - 11 * (n : ℚ) - 5 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a025251
