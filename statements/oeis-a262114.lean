import Mathlib

/-!
# A262114: Irregular triangle read by rows: row b (b >= 2) gives periodic part of digits of the base-b expansion of 1/5.

Source: https://oeis.org/A262114

The conjectures listed in the entry (Colin Barker, Oct 09 2015), stated below as one conjunction:
* a(n) = 2*a(n-12) - a(n-24) for n>24.
* G.f.: x^3*(x^19 +x^18 +x^17 +2*x^16 +2*x^15 +x^14 +2*x^13 +3*x^12 +2*x^11 +x^10 +x^9 +x^8 +3*x^7
  +x^5 +2*x^4 +x^3 +x +1) / (x^24 -2*x^12 +1).

Conventions.
* The `k`-th digit (`k >= 1`) after the radix point of the base-`b` expansion of 1/5 is
  `floor(b^k / 5) mod b`.
* Row `b` (for `b >= 2`): if `5` divides `b`, the expansion of 1/5 terminates after one digit
  and the row is that single digit (as in the entry's examples, e.g. row 10 is `2`); otherwise
  the expansion is purely periodic with period the multiplicative order of `b` modulo `5`, and
  the row is the first period of digits (e.g. row 8 is `1, 4, 6, 3`).
* The rows `b = 2, 3, 4, ...` are concatenated. Barker's formulas index the terms from 1
  (his g.f. starts with `x^3`, matching the data 0, 0, 1, 1, 0, 1, ...), so `a 1` is the first
  term and `a 0 = 0`; the recurrence and the g.f. are stated with this indexing (the offset field
  of the entry says 2, which is incompatible with "n>24" and with the `x^3` of the g.f.).
* The g.f. is stated with the denominator multiplied out, as an identity of formal power series
  over the integers, with `a 0 = 0`.
The definition below reproduces every term listed in the entry; both formulas were checked for
every n < 200.
-/

namespace OMA.S_oeis_a262114

/-- The `(k + 1)`-th digit after the radix point of the base-`b` expansion of `1/5`. -/
def digit (b k : ℕ) : ℕ := b ^ (k + 1) / 5 % b

/-- Row `b` of the triangle: the terminating digit if `5 ∣ b`, otherwise the first period of the
purely periodic expansion, whose length is the order of `b` modulo `5`. -/
noncomputable def row (b : ℕ) : List ℕ :=
  if 5 ∣ b then [digit b 0] else (List.range (orderOf (b : ZMod 5))).map (digit b)

/-- A262114(n), indexed from `n = 1` (Barker's indexing): the `n`-th entry of the concatenation of
the rows `b = 2, 3, 4, ...`; `a 0 = 0`. Every row is nonempty, so the first `n` rows already
contain at least `n` entries. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((List.range n).flatMap (fun k => row (k + 2))).getD (n - 1) 0

open PowerSeries in
theorem main :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 2 * a (n - 12) - a (n - 24)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (X ^ 24 - 2 * X ^ 12 + 1) =
      X ^ 3 * (X ^ 19 + X ^ 18 + X ^ 17 + 2 * X ^ 16 + 2 * X ^ 15 + X ^ 14 + 2 * X ^ 13 + 3 * X ^ 12 +
        2 * X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + 3 * X ^ 7 + X ^ 5 + 2 * X ^ 4 + X ^ 3 + X + 1) := by
  sorry

end OMA.S_oeis_a262114
