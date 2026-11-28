import Mathlib

/-!
# A166587: A signed variant of the Motzkin numbers.

Source: https://oeis.org/A166587 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

Entry (Paul Barry, Oct 17 2009), offset 0. The name is descriptive; the sequence is given by
its generating function, the first line of the formula section:

  G.f.: (1+3*x-sqrt(1+2*x-3*x^2))/(2*x).

Terms: 1, 1, -1, 2, -4, 9, -21, 51, -127, 323, -835, 2188, ... The formula section also states:

  Conjecture: n*(n+1)*a(n) + n*(n+1)*a(n-1) - (5*n-3)*(n-2)*a(n-2) + 3*(n-2)*(n-3)*a(n-3) = 0.
  - R. J. Mathar, Nov 15 2012

(A later line by Robert Israel, May 17 2016, says that the conjecture follows from a
differential equation satisfied by the g.f.)

Formalization notes:
* The square root is a formal power series over ℚ: `S` with `S ^ 2 = 1 + 2x - 3x^2` and constant
  coefficient 1 (the constant coefficient selects the branch of the square root; such an `S`
  exists, by the binomial series, and is unique). The g.f. `G` is determined by `2x·G = 1 + 3x - S`
  (x is not a zero divisor in ℚ⟦X⟧), and a(n) = [x^n] G. This is the layout of the merged
  square-root statements, for example `oeis-a071715`.
* The source gives no range. The recurrence mentions a(n-3), so it is stated for n ≥ 3, where all
  four terms exist. Coefficients are written in ℚ, so that no natural-number subtraction occurs
  in them (for n ≥ 3 the indices n-1, n-2, n-3 are genuine).
* Controls: with the entry's terms, n = 3 gives 12*2 + 12*(-1) - 12*1 + 0 = 0, and the identity
  holds for the twenty terms checked (n = 3..21).
-/

namespace OMA.S_oeis_a166587

open PowerSeries

/-- Mathar's conjectured recurrence for the coefficients of (1+3x-sqrt(1+2x-3x^2))/(2x),
for n ≥ 3. -/
theorem main : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 + 2 * X - 3 * X ^ 2 →
    coeff 0 S = 1 →
    2 * X * G = 1 + 3 * X - S →
    ∀ n : ℕ, 3 ≤ n →
      (n : ℚ) * (n + 1) * coeff n G + (n : ℚ) * (n + 1) * coeff (n - 1) G
        - (5 * (n : ℚ) - 3) * ((n : ℚ) - 2) * coeff (n - 2) G
        + 3 * ((n : ℚ) - 2) * ((n : ℚ) - 3) * coeff (n - 3) G = 0 := by
  sorry

end OMA.S_oeis_a166587
