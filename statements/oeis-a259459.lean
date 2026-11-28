import Mathlib

/-!
# A259459: From higher-order arithmetic progressions.

Source: https://oeis.org/A259459
Credit: @agchua

R. J. Mathar (Aug 09 2015), in the formula section of A259459:
  Conjectured g.f.: 3F0(4,3,3;;x/2).
Definition, from the programs of the entry (Maple by R. J. Mathar, Jul 14 2015; Mathematica by
Jean-François Alcover, Apr 27 2023, after Mathar, offset 0): with
rV(i,a,d) = i(i+1)/2*a + (i-1)i(i+1)/6*d, a(n) is the coefficient of d^1 a^(n+1) in the product
rV(1,a,d)*rV(2,a,d)*...*rV(n+2,a,d). Here the product is a polynomial in d whose coefficients are
polynomials in a over ℚ (Polynomial (Polynomial ℚ)); a(n) is the coefficient of a^(n+1) in its
coefficient of d^1. This gives the listed terms 1, 18, 360, 9000, 283500, ... Offset 0.
The hypergeometric series 3F0(4,3,3;;z) is the formal series Sum_{n>=0} (4)_n (3)_n (3)_n z^n / n!,
with the rising factorial (x)_n = x(x+1)...(x+n-1) (ascPochhammer); at z = x/2 its coefficient of
x^n is (4)_n (3)_n (3)_n / n! * (1/2)^n. The conjecture is stated as an identity of formal power
series over ℚ.
-/

namespace OMA.S_oeis_a259459

/-- rV(i,a,d) = i(i+1)/2*a + (i-1)i(i+1)/6*d, with d the outer and a the inner variable. -/
noncomputable def rV (i : ℕ) : Polynomial (Polynomial ℚ) :=
  Polynomial.C (Polynomial.C ((i : ℚ) * ((i : ℚ) + 1) / 2) * Polynomial.X) +
    Polynomial.C (Polynomial.C (((i : ℚ) - 1) * (i : ℚ) * ((i : ℚ) + 1) / 6)) * Polynomial.X

/-- A259459(n): the coefficient of d^1 a^(n+1) in rV(1,a,d) * ... * rV(n+2,a,d). -/
noncomputable def a (n : ℕ) : ℚ :=
  ((∏ i ∈ Finset.Icc 1 (n + 2), rV i).coeff 1).coeff (n + 1)

/-- Mathar's conjecture: the g.f. is 3F0(4,3,3;;x/2). -/
theorem main :
    PowerSeries.mk a =
      PowerSeries.mk (fun n => (ascPochhammer ℚ n).eval 4 * (ascPochhammer ℚ n).eval 3 *
        (ascPochhammer ℚ n).eval 3 / (n.factorial : ℚ) * (1 / 2 : ℚ) ^ n) := by
  sorry

end OMA.S_oeis_a259459
