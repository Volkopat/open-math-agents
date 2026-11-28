import Mathlib

namespace OMA.S_oeis_a183240

open PowerSeries BigOperators

/-- The multinomial coefficient `n! / ∏_{a ∈ P.parts} a!` of an integer partition `P` of `n`. -/
def multinom (n : ℕ) (P : Nat.Partition n) : ℕ :=
  Nat.factorial n / (P.parts.map Nat.factorial).prod

/-- Sum of `2`-th powers of multinomial coefficients over all partitions of `n`. -/
noncomputable def multiPowSum (k n : ℕ) : ℕ :=
  ∑ P : Nat.Partition n, (multinom n P) ^ k

/-- Exponential power series `A(x) = exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n C(k) * a(n - k)` for `n ≥ 1`. -/
noncomputable def expLogCoeffs (C : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 =>
      (∑ k : Fin (n + 1), (C (k.val + 1) : ℚ) * expLogCoeffs C (n - k.val)) / ((n + 1 : ℕ) : ℚ)
termination_by n => n
decreasing_by
  have := k.isLt
  omega

/-- The formal power series `exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`. -/
noncomputable def expLogSeries (C : ℕ → ℤ) : PowerSeries ℚ :=
  PowerSeries.mk (expLogCoeffs C)

/-- Predicate that a formal power series over `ℚ` has integer coefficients. -/
def isIntegerSeries (f : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, ∃ z : ℤ, PowerSeries.coeff n f = (z : ℚ)

/-- OEIS A183240 conjecture:
"Sums of the squares of multinomial coefficients. Ignoring initial term, equals the logarithmic derivative of A183241; A183241 is conjectured to consist entirely of integers." -/
theorem main :
    isIntegerSeries (expLogSeries fun n => (multiPowSum 2 n : ℤ)) := by sorry

end OMA.S_oeis_a183240
