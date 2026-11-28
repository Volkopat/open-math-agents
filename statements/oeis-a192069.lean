import Mathlib

/-!
# A192069: (A192249)/5.

Source: https://oeis.org/A192069
Credit: @rtflynn (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 0, 1, 4, 18, 60, 186, ...) records in its FORMULA section
(R. J. Mathar, May 04 2014):

  Conjecture: G.f.: x^2*(1-2*x+4*x^2-3*x^3+x^4) / ( (x-1)*(x^2+x-1)^5 ).

Definitions, following A192248, A192249 and A192232 (Clark Kimberling, Mathematica program
by Peter J. C. Moses):
* `c m = m(m+1)(m+2)(m+3)/24 = C(m+3, 4)` (A000332, offset shifted as in the program).
* `p 0 = 1` and `p m = p (m-1) + c (m+1) * x^m`, so `p m = ∑_{k=0}^{m} C(k+4, 4) x^k`.
* The reduction of a polynomial by `x^2 -> x+1` replaces `x^2` by `x + 1` until the degree is
  below 2. Each replacement changes the polynomial by a multiple of `x^2 - x - 1`, and the
  result has degree below 2, so the reduction is the remainder of the division by the monic
  polynomial `x^2 - x - 1`, i.e. `p %ₘ (X^2 - X - 1)`.
* A192249(n) is the coefficient of `x` (the "1-sequence") in the reduction of `p (n-1)`,
  for `n ≥ 1` (the program's `Part[t, n]` is the reduction of `p[n-1, x]`).
  Its data 0, 5, 20, 90, 300, ... is what this gives.
* A192069(n) = A192249(n)/5, taken in `ℚ` so that no divisibility is assumed.
* The generating function, with offset 1, is `∑_{n ≥ 1} a(n) x^n`; the formal power series
  below has coefficient 0 at `x^0`.
The rational g.f. is stated as an identity of formal power series over `ℚ`:
`(∑_{n ≥ 1} a(n) x^n) * ((x-1)*(x^2+x-1)^5) = x^2*(1-2*x+4*x^2-3*x^3+x^4)`.
-/

namespace OMA.S_oeis_a192069

open Polynomial

/-- `p m = 1 + ∑_{k=1}^{m} c(k+1) x^k` with `c(j) = C(j+3, 4)`, i.e. `∑_{k=0}^{m} C(k+4, 4) x^k`. -/
noncomputable def p (m : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (m + 1), C (((k + 4).choose 4 : ℕ) : ℤ) * X ^ k

/-- The reduction of a polynomial by `x^2 -> x+1`: its remainder modulo `x^2 - x - 1`. -/
noncomputable def reduce (q : ℤ[X]) : ℤ[X] := q %ₘ (X ^ 2 - X - 1)

/-- A192249(n), for `n ≥ 1`: the coefficient of `x` in the reduction of `p (n-1)`. -/
noncomputable def A192249 (n : ℕ) : ℤ := (reduce (p (n - 1))).coeff 1

/-- A192069(n) = A192249(n)/5, for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℚ := (A192249 n : ℚ) / 5

/-- The conjectured generating function of A192069 (offset 1). -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else a n) *
        ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + PowerSeries.X - 1) ^ 5) =
      PowerSeries.X ^ 2 *
        (1 - 2 * PowerSeries.X + 4 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 +
          PowerSeries.X ^ 4) := by
  sorry

end OMA.S_oeis_a192069
