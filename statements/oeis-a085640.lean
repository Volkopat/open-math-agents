import Mathlib

/-!
# A085640: Resultant of the polynomial x^3-1 and the Chebyshev polynomial of the first kind T_n(x).

Source: https://oeis.org/A085640
Credit: @agchua

Conjecture in the formula section of A085640:
  From Creighton Dement, Jan 17 2009: G.f.: (1+3*x+3*x^2-x^3)/(1-4*x-6*x^2-4*x^3+x^4)
  (conjecture).
Definition: a(n) = Res(x^3 - 1, T_n(x)), the resultant of x^3 - 1 and the Chebyshev polynomial
T_n of the first kind over ℤ (Mathlib's Polynomial.resultant with its default degrees, the
convention of polresultant in the entry's PARI program). The offset is 1 and the g.f. begins
with a(1) = 1, so it is the series Sum_{n ≥ 0} a(n+1) x^n; it is stated as an identity of formal
power series over ℚ. The rest of that formula line names a generating floretion (an element of
Dement's floretion algebra by which the sequence was found); it describes how the sequence was
obtained and is not a claim about its terms, so it is not part of this statement.
-/

namespace OMA.S_oeis_a085640

/-- A085640: a(n) = resultant(x^3 - 1, T_n(x)). -/
noncomputable def a (n : ℕ) : ℤ :=
  Polynomial.resultant (Polynomial.X ^ 3 - 1 : Polynomial ℤ) (Polynomial.Chebyshev.T ℤ (n : ℤ))

/-- The conjecture of Creighton Dement: Sum_{n ≥ 0} a(n+1) x^n =
(1+3*x+3*x^2-x^3)/(1-4*x-6*x^2-4*x^3+x^4). -/
theorem main : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
    (1 - 4 * PowerSeries.X - 6 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4) =
    1 + 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3 := by
  sorry

end OMA.S_oeis_a085640
