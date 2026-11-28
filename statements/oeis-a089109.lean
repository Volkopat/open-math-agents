import Mathlib

/-!
# A089109: Convoluted convolved Fibonacci numbers G_5^(r).

Source: https://oeis.org/A089109
Credit: @agchua

Colin Barker (Jul 31 2013), in the formula section of A089109:
  Conjecture: a(n) = (66-18*(-1)^n+(115-3*(-1)^n)*n+36*n^2+2*n^3)/48. G.f.: -x*(x^5-2*x^4-2*x^3+6*x^2+x-5) / ((x-1)^4*(x+1)^2).
This file states both parts: the closed form for every n >= 1 (the offset is 1), and the g.f. as
an identity of formal power series over Q,
(sum of a(n) X^n) * ((X - 1)^4 (X + 1)^2) = -X (X^5 - 2X^4 - 2X^3 + 6X^2 + X - 5);
its coefficient of X^0 is a(0), which the definition below makes 0 (1/0 = 0 in Q, and 0 has no
divisors), in accordance with the factor x of the g.f. (offset 1).
Definition: the Maple program of the entry,
  f := z->1/(1-z-z^2): m := proc(r,j) d := divisors(r): W := (1/r)*z*sum(mobius(d[i])*f(z^d[i])^(r/d[i]),i=1..nops(d)): Wser := simplify(series(W,z=0,80)): coeff(Wser,z^j) end: seq(m(r,5),r=1..65);
that is, a(r) is the coefficient of z^5 in the power series
W(r) = (1/r) z sum over the divisors d of r of mobius(d) f(z^d)^(r/d), with f(z) = 1/(1 - z - z^2).
Below, f d is f(z^d) = 1/(1 - z^d - (z^d)^2), the inverse in Q[[X]] (its constant term is 1).
The definition gives the listed terms 5, 9, 17, 25, 38, 51, 70, 89, ... (all 48 listed terms
checked by exact computation).
-/

namespace OMA.S_oeis_a089109

/-- f d = f(z^d) = 1/(1 - z^d - (z^d)^2), with f(z) = 1/(1 - z - z^2). -/
noncomputable def f (d : ℕ) : PowerSeries ℚ :=
  (1 - PowerSeries.X ^ d - (PowerSeries.X ^ d) ^ 2)⁻¹

/-- W(r) = (1/r) z sum over the divisors d of r of mobius(d) f(z^d)^(r/d). -/
noncomputable def W (r : ℕ) : PowerSeries ℚ :=
  PowerSeries.C (1 / (r : ℚ)) * PowerSeries.X *
    ∑ d ∈ r.divisors, PowerSeries.C ((ArithmeticFunction.moebius d : ℤ) : ℚ) * f d ^ (r / d)

/-- A089109: a(r) = the coefficient of z^5 in W(r) (= m(r, 5) of the Maple program). -/
noncomputable def a (r : ℕ) : ℚ := PowerSeries.coeff 5 (W r)

/-- Barker's conjectures: the closed form for n >= 1, and the g.f.
-x(x^5 - 2x^4 - 2x^3 + 6x^2 + x - 5)/((x - 1)^4 (x + 1)^2). -/
theorem main : (∀ n : ℕ, 1 ≤ n →
      a n = (66 - 18 * (-1) ^ n + (115 - 3 * (-1) ^ n) * (n : ℚ) + 36 * (n : ℚ) ^ 2 +
        2 * (n : ℚ) ^ 3) / 48) ∧
    PowerSeries.mk a * ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2) =
      -PowerSeries.X * (PowerSeries.X ^ 5 - 2 * PowerSeries.X ^ 4 - 2 * PowerSeries.X ^ 3 +
        6 * PowerSeries.X ^ 2 + PowerSeries.X - 5) := by
  sorry

end OMA.S_oeis_a089109
