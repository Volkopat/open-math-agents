import Mathlib

namespace OMA.S_oeis_a255895

open PowerSeries BigOperators

/-- Euler (secant) numbers `A000364(n) = E_{2n}` (`1, 1, 5, 61, 1385, ...`),
uniquely determined by `E_0 = 1` and `∑_{k=0}^n (-1)^(n-k) C(2n, 2k) E_{2k} = 0` for `n ≥ 1`. -/
def eulerSec : ℕ → ℤ
  | 0 => 1
  | n + 1 =>
      ∑ k : Fin (n + 1),
        (-1 : ℤ) ^ (n - k.val) * (Nat.choose (2 * (n + 1)) (2 * k.val) : ℤ) * eulerSec k.val
termination_by n => n
decreasing_by
  exact k.isLt

/-- Exponential power series `A(x) = exp(∑_{n ≥ 1} C(n) * x^n / n)` over `ℚ`,
uniquely defined by `a(0) = 1` and `n * a(n) = ∑_{k=1}^n C(k) * a(n - k)` for `n ≥ 1`. -/
def expLogCoeffs (C : ℕ → ℤ) : ℕ → ℚ
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

/-- OEIS A255895 conjecture:
"O.g.f.: exp( Sum_{n>=1} A000364(n+1)*x^n/n ), where A000364 is the Euler numbers.
Inspired by Peter Bala's sequence A255881, which suggests the following conjecture:
exp( Sum_{n>=1} A000364(n+m)*x^n/n ) is an integer series for integer m >= 0." -/
theorem main :
    ∀ m : ℕ, isIntegerSeries (expLogSeries fun n => eulerSec (n + m)) := by sorry

end OMA.S_oeis_a255895
