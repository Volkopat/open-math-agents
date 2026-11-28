import Mathlib

/-!
# A381737: Orders k of Hermite polynomials whose maximal coefficient in absolute value appears twice.

Source: https://oeis.org/A381737
Credit: @Mapika (AI-assisted: Claude Code, model claude-opus-5-5).

The formula section of A381737 (entry by Mike Sheppard, Mar 05 2025) states:
  Conjecture 1: a(n) = 2*n*(n + 2) + (n + 1)*(-1)^(n+1).
  Conjecture 2: a(n) = a(n-1) + 2*a(n-2) - 2*a(n-3) - a(n-4) + a(n-5).
  Conjecture 3: G.f.: (8*x + 5*x^2 + 5*x^3 - x^4 - x^5) / ((1 - x)^3 * (1 + x)^2).
  Terms < 20000 consistent with conjectures. - Jinyuan Wang, Mar 09 2025.
This file states all three as a conjunction.

Modelling choices:
* The Hermite polynomials are the physicists' ones, as in the entry's examples
  (H_8(x) = 1680 - 13440 x^2 + 13440 x^4 - 3584 x^6 + 256 x^8, and A060821, which the entry
  cites): H_0 = 1, H_1 = 2x, H_(n+2) = 2x H_(n+1) - 2(n+1) H_n, with integer coefficients.
  Mathlib's `Polynomial.hermite` is the probabilists' family, so it is not used.
* "The maximal coefficient in absolute value appears twice": the largest absolute value of a
  coefficient of H_k is attained at exactly two exponents. The coefficients run over the
  support of H_k (zero coefficients are never maximal, since H_k is nonzero).
* The offset is 1 (a(1) = 8): a(n) is the n-th term in increasing order, i.e.
  `Nat.nth isTerm (n - 1)` for n ≥ 1.
* Conjecture 1 is stated for every n ≥ 1, in ℤ because of the sign (-1)^(n+1).
* Conjecture 2 has no stated range; it is stated for n ≥ 6, the range on which all of
  a(n-5), ..., a(n) are terms of the sequence (offset 1). It is stated in ℤ.
* Conjecture 3 is stated as an identity of formal power series over ℚ after clearing the
  denominator: (∑_(n ≥ 1) a(n) X^n) * (1 - X)^3 * (1 + X)^2 = 8X + 5X^2 + 5X^3 - X^4 - X^5.
  The constant coefficient of the series is 0 because the offset is 1.
-/

namespace OMA.S_oeis_a381737

open Polynomial

/-- The physicists' Hermite polynomials: `H 0 = 1`, `H 1 = 2x`,
`H (n + 2) = 2x * H (n + 1) - 2(n + 1) * H n`. -/
noncomputable def H : ℕ → ℤ[X]
  | 0 => 1
  | 1 => C 2 * X
  | n + 2 => C 2 * X * H (n + 1) - C (2 * ((n : ℤ) + 1)) * H n

/-- The largest absolute value of a coefficient of `H k`. -/
noncomputable def maxAbsCoeff (k : ℕ) : ℕ :=
  (H k).support.sup fun i => ((H k).coeff i).natAbs

/-- `k` is a term: the largest absolute value of a coefficient of `H k` is attained at
exactly two exponents. -/
def isTerm (k : ℕ) : Prop :=
  ((H k).support.filter fun i => ((H k).coeff i).natAbs = maxAbsCoeff k).card = 2

/-- A381737 with offset 1: `a n` is the `n`-th term (`n ≥ 1`) in increasing order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth isTerm (n - 1)

/-- Mike Sheppard's three conjectures in A381737: the closed form, the recurrence of order 5,
and the generating function. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = 2 * n * (n + 2) + (n + 1) * (-1) ^ (n + 1)) ∧
    (∀ n : ℕ, 6 ≤ n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        (1 - PowerSeries.X) ^ 3 * (1 + PowerSeries.X) ^ 2 =
      8 * PowerSeries.X + 5 * PowerSeries.X ^ 2 + 5 * PowerSeries.X ^ 3 -
        PowerSeries.X ^ 4 - PowerSeries.X ^ 5 := by
  sorry

end OMA.S_oeis_a381737
