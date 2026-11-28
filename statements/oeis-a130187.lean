import Mathlib

/-!
# A130187: Numerators of rationals r(n) related to the z-sequence of the Sheffer matrix A060821 for Hermite polynomials.

Source: https://oeis.org/A130187
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A130187 (Wolfdieter Lang, Jan 04 2013):
a(n) = A001147(n+1)/A000265(n+1), n >= 0.

Conventions:
* The sequence has offset 0 (data 1, 3, 5, 105, 189, 3465, 19305, ...).
* The entry defines everything through the z-sequence: "The e.g.f. for the z-sequence is
  -2*(exp((x^2)/4)-1)/x", "r(n) := -2*z(2*n+1) (in lowest terms)" and
  "a(n) = numerator(r(n)), n >= 0". This is what is formalized; nothing about Sheffer matrices
  is needed to state it.
* exp(x^2/4) is the formal power series Sum_{k>=0} x^(2k)/(4^k k!), `expSq` below (coefficient
  1/(4^(m/2) (m/2)!) at even m and 0 at odd m). The division by x of the series
  -2*(exp(x^2/4)-1), which has constant term 0, is the shift of its coefficients, so the
  coefficient of x^m of the e.g.f. is -2 times the coefficient of x^(m+1) of exp(x^2/4) - 1;
  this is `zEgf`. As it is an exponential generating function, z(m) = m! * [x^m] `zEgf`
  (z = 0, -1/2, 0, -3/8, 0, -5/8, 0, -105/64, ... as listed in the entry).
* The numerator of a rational number in lowest terms (with positive denominator) is `Rat.num`.
* A001147(n+1) = (2n+1)!! = 1*3*5*...*(2n+1) is `Nat.doubleFactorial (2 * n + 1)`.
* A000265(m) is the largest odd divisor of m, i.e. m divided by the largest power of 2 dividing
  m; it is `oddPart m` below, defined with the 2-adic valuation `padicValNat 2 m`.
* The quotient A001147(n+1)/A000265(n+1) is formed in `ℚ`; the statement therefore includes
  that this quotient is the integer a(n).
-/

namespace OMA.S_oeis_a130187

/-- The formal power series exp(x^2/4) = Sum_{k>=0} x^(2k)/(4^k k!). -/
noncomputable def expSq : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    if m % 2 = 0 then 1 / ((4 : ℚ) ^ (m / 2) * ((m / 2).factorial : ℚ)) else 0

/-- The e.g.f. of the z-sequence, -2*(exp(x^2/4)-1)/x. -/
noncomputable def zEgf : PowerSeries ℚ :=
  PowerSeries.mk fun m => -2 * PowerSeries.coeff (m + 1) (expSq - 1)

/-- The z-sequence: z(m) = m! * [x^m] (-2*(exp(x^2/4)-1)/x). -/
noncomputable def z (m : ℕ) : ℚ := (m.factorial : ℚ) * PowerSeries.coeff m zEgf

/-- r(n) = -2*z(2n+1). -/
noncomputable def r (n : ℕ) : ℚ := -2 * z (2 * n + 1)

/-- A130187 (offset 0): a(n) is the numerator of r(n) in lowest terms. -/
noncomputable def a (n : ℕ) : ℤ := (r n).num

/-- A000265: the largest odd divisor of m. -/
def oddPart (m : ℕ) : ℕ := m / 2 ^ (padicValNat 2 m)

/-- For every `n ≥ 0`, a(n) = A001147(n+1)/A000265(n+1) = (2n+1)!!/oddPart(n+1). -/
theorem main : ∀ n : ℕ,
    (a n : ℚ) = (Nat.doubleFactorial (2 * n + 1) : ℚ) / (oddPart (n + 1) : ℚ) := by
  sorry

end OMA.S_oeis_a130187
