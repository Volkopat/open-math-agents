import Mathlib

/-!
# A129654: Number of ways to represent n as a general polygonal number P(m,r), m, r > 1.

Source: https://oeis.org/A129654
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 2, data 1, 2, 2, 2, 3, 2, 2, 3, 3, 2, 3, 2, 2, 4, 3, ...) is named
Number of different ways to represent n as general polygonal number
P(m,r) = 1/2*r*((m-2)*r-(m-4)) = n>1, for m,r>1.
Its FORMULA section records:

  G.f.: x * Sum_{k>=1} x^k / (1 - x^(k*(k + 1)/2)) (conjecture). - Ilya Gutkovskiy, Apr 09 2020

Conventions:
* `polygonal m r` is `P(m,r) = r*((m-2)*r-(m-4))/2`, computed in `ℤ` (so that `m - 4` may be
  negative). The numerator equals `(m-2)*r*(r-1) + 2*r`, which is always even, so the division
  is exact.
* `a n` is the number of pairs `(m, r)` of natural numbers with `m > 1`, `r > 1` and
  `P(m,r) = n`, as in the entry name (for example `6 = P(2,6) = P(3,3) = P(6,2)`, so `a 6 = 3`).
  It is defined as the cardinality of the set of all such pairs; the set is finite for `n ≥ 2`.
* The sequence has offset 2, so the claim is made for every `n ≥ 2`.
* The generating function is read in `ℚ⟦X⟧`, with `1/(1 - x^t)` the inverse power series
  `(1 - X^t)⁻¹` (here `t = k*(k+1)/2 ≥ 1`). The summand for `k` is divisible by `X^(k+1)`, so
  it has no `x^n` term when `k ≥ n`; the coefficient of `x^n` in the full infinite sum is
  therefore the coefficient of `x^n` in the finite sum over `1 ≤ k ≤ n`, which is what `main`
  uses.
-/

namespace OMA.S_oeis_a129654

open PowerSeries

/-- The general polygonal number `P(m,r) = r*((m-2)*r-(m-4))/2`. -/
def polygonal (m r : ℕ) : ℤ :=
  (r : ℤ) * (((m : ℤ) - 2) * r - ((m : ℤ) - 4)) / 2

/-- A129654: the number of pairs `(m, r)` with `m > 1`, `r > 1` and `P(m,r) = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | 1 < p.1 ∧ 1 < p.2 ∧ polygonal p.1 p.2 = n}

/-- The conjecture of A129654: for every `n ≥ 2`, `a n` is the coefficient of `x^n` in
`x * Sum_{k>=1} x^k / (1 - x^(k*(k+1)/2))`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℚ) = PowerSeries.coeff n
      (∑ k ∈ Finset.Icc 1 n, (X : ℚ⟦X⟧) * X ^ k * (1 - X ^ (k * (k + 1) / 2))⁻¹) := by
  sorry

end OMA.S_oeis_a129654
