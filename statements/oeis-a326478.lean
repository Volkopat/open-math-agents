import Mathlib

/-!
# A326478: a(n) = n*denominator(n*Bernoulli(n-1))/denominator(Bernoulli(n-1)).

Source: https://oeis.org/A326478
Credit: @luciusacarr

The entry records the empirical observation: a(2*n) = [x^n] x*(2/(x - 1)^2 - 1) for n >= 1
(implying the conjecture that a(2*n) = A103517(n+1) and/or A272651(n)). Known terms:
a(1..8) = 1, 1, 1, 4, 1, 6, 1, 8.

Reading of the source:
* `B(k)` is the `k`-th Bernoulli number with the OEIS / PARI (`bernfrac`) convention
  `B(1) = -1/2`; this is Mathlib's `bernoulli` (not `bernoulli'`). Denominators are those of the
  reduced fractions (`Rat.den`, always positive). The sequence is taken with values in `ℚ`.
* `[x^n] F` is the coefficient of `x^n` in the formal power series `F` over `ℚ`; `2/(x - 1)^2` is
  `2 * ((x - 1)^2)⁻¹`, which is well defined since `(x - 1)^2` has constant term `1`.
* Only the empirical formula for the even-indexed terms is formalized. The entry's other comment
  (conjecturally, the odd fixed points > 1 are A121707) is a separate open conjecture and is not
  part of this statement.
-/

namespace OMA.S_oeis_a326478

open PowerSeries

/-- `a(n) = n * denominator(n * B(n-1)) / denominator(B(n-1))`, with `B(1) = -1/2`. -/
def a (n : ℕ) : ℚ :=
  (n : ℚ) * ((n : ℚ) * bernoulli (n - 1)).den / (bernoulli (n - 1)).den

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a (2 * n) = coeff n ((X : PowerSeries ℚ) * (2 * ((X - 1) ^ 2)⁻¹ - 1)) := by
  sorry

end OMA.S_oeis_a326478
