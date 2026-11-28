import Mathlib

/-!
# A007497: a(1) = 2, a(n) = sigma(a(n-1))

Source: https://oeis.org/A007497
Credit: @sntntHb

A007497 (offset 1) iterates the sum-of-divisors function starting from `2`:
`2, 3, 4, 7, 8, 15, 24, 60, 168, 480, ...`.

Formalizes the two conjectures in OEIS A007497:
* Benoit Cloitre (May 08 2003): `(1/2) log(n) < a(n+1)/a(n) < 2 log(n)`; at `n = 1` the
  bounds are `0 < 3/2 < 0`, so it is stated for every `n >= 2` (it holds numerically for
  `2 <= n < 69`; `log` is the natural logarithm);
* Ivan N. Ianakiev (Mar 27 2014): `a(n) == 0 (mod 9)` for every `n > 34`.
-/

namespace OMA.S_oeis_a007497

/-- A007497 with offset 1: `a 1 = 2`, `a (n+1) = sigma (a n)` (and `a 0 = 2` is a dummy value). -/
def a : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | n + 2 => ArithmeticFunction.sigma 1 (a (n + 1))

/-- The two conjectures of A007497. -/
theorem main :
    (∀ n : ℕ, 2 ≤ n →
        (1 / 2 : ℝ) * Real.log n < (a (n + 1) : ℝ) / (a n : ℝ) ∧
          (a (n + 1) : ℝ) / (a n : ℝ) < 2 * Real.log n) ∧
      (∀ n : ℕ, 34 < n → 9 ∣ a n) := by
  sorry

end OMA.S_oeis_a007497
