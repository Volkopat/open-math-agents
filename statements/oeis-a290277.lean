import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# The inverse Euler transform of the Motzkin numbers

R. J. Mathar conjectured the divisor sum below for OEIS A290277. Its offset is one.
The Motzkin recurrence is the coefficient form of M = 1 + XM + X²M².
A002426(n) is the central coefficient in the nth power of 1 + x + x².

For the Euler transform M = ∏ (1 − X^d)^(-a(d)), the coefficient of X^n in
XM'/M is the sum of d*a(d) over the divisors of n. Removing the proper divisors
recursively therefore defines the inverse Euler transform.

Sources: https://oeis.org/A290277, https://oeis.org/A001006, https://oeis.org/A002426.
-/

namespace OMA.S_oeis_a290277

open PowerSeries

/-- Motzkin numbers from the first-step decomposition of Motzkin paths. -/
def motzkin : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => motzkin (n + 1) +
      ∑ i : Fin (n + 1), motzkin i.val * motzkin (n - i.val)
termination_by n => n
decreasing_by all_goals omega

/-- The coefficient of X^n in (1 + X + X²)^n, the central trinomial coefficient. -/
noncomputable def centralTrinomial (n : ℕ) : ℕ :=
  ((1 + Polynomial.X + Polynomial.X^2 : Polynomial ℕ)^n).coeff n

noncomputable def motzkinSeries : ℚ⟦X⟧ := PowerSeries.mk fun n => (motzkin n : ℚ)

/-- The coefficients of the logarithmic derivative multiplied by X. -/
noncomputable def logCoeffs (n : ℕ) : ℚ :=
  coeff n (X * derivative ℚ motzkinSeries * motzkinSeries⁻¹)

/-- Invert a divisor sum by subtracting each already determined proper-divisor weight. -/
def eulerWeight (g : ℕ → ℚ) (n : ℕ) : ℚ :=
  g n - ∑ d ∈ n.properDivisors.attach, eulerWeight g d.val
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.property).2

/-- A290277, the Euler exponents of the Motzkin generating function. -/
noncomputable def a (n : ℕ) : ℚ := eulerWeight logCoeffs n / n

theorem main : ∀ n : ℕ, 0 < n →
    (n : ℚ) * a n = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℚ) * centralTrinomial (n / d) := by
  sorry

end OMA.S_oeis_a290277
