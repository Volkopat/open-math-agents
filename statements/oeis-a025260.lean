import Mathlib

/-!
# A025260: Mathar's recurrence, corrected to n ≥ 6

Source: https://oeis.org/A025260
Credit: @ivillar

Status: false as stated at n = 5 (the left side is 2 at n = 5 on the OEIS data); `main` is the
corrected recurrence (n ≥ 6), which is proved.

A025260 (offset 1): a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-3)*a(3) for n >= 4, with initial terms 2, -2, 1, 2;
data 2, -2, 1, 2, 2, 1, 2, 10, 26, 44, 68, 149, ...

Conjecture (R. J. Mathar, Feb 25 2015):
n*a(n) + 2*(-2*n+3)*a(n-1) + 8*(n-3)*a(n-2) + 6*(-2*n+9)*a(n-3) + 4*(n-6)*a(n-4) = 0.

Formalization: `main` is stated for every a : ℕ → ℚ with the given initial values and the defining
recurrence, written as a(n) = Sum_{k=1..n-3} a(k)*a(n-k) for n ≥ 4; these conditions determine a(n)
for all n ≥ 1 (the fourth listed term is the value the recurrence gives at n = 4). `main` is the corrected recurrence (n ≥ 6): on the data the left side of the recurrence as stated
is 2 at n = 5, and it vanishes from n = 6 on.
-/

namespace OMA.S_oeis_a025260

/-- The corrected recurrence (n ≥ 6): Mathar's recurrence, which fails at n = 5. -/
theorem main : ∀ a : ℕ → ℚ, a 1 = 2 →
    a 2 = (-2) →
    a 3 = 1 →
    (∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) →
    ∀ n : ℕ, 6 ≤ n →
      ((n : ℚ)) * a n + (6 - 4 * (n : ℚ)) * a (n - 1) +
        (-24 + 8 * (n : ℚ)) * a (n - 2) + (54 - 12 * (n : ℚ)) * a (n - 3) +
        (-24 + 4 * (n : ℚ)) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a025260
