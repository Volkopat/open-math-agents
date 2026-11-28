import Mathlib

/-!
# A003067: Problimes (second definition).

Source: https://oeis.org/A003067
Credit: @agchua

Comment in A003067 (entry by N. J. A. Sloane; offset 1):
  The g.f. (z^2+2+z^9+z^5)/(z-1)^2 conjectured by _Simon Plouffe_ in his 1992 dissertation is wrong.
The statement below is this comment's assertion, as a non-identity of formal power series over Q.
Plouffe's generating functions (Approximations de series generatrices et quelques conjectures,
Dissertation, UQAM 1992, arXiv:0911.4975) expand the listed terms from the constant term on, so the
g.f. of the sequence a(1), a(2), a(3), ... is the series sum of a(n + 1) X^n. Since (X - 1)^2 is
invertible, the comment says: (sum of a(n + 1) X^n) * (X - 1)^2 is not X^2 + 2 + X^9 + X^5.
(Plouffe's g.f. expands to 2, 4, 7, 10, 13, 17, 21, 25, 29, 34, ..., which agrees with the first
twenty terms of the sequence.)
Definition: the Maple program of the entry (James Sellers, Mar 07 2000):
  a[1] := 2: for i from 1 to 150 do a[i+1] := round(a[i]+1/product((1-1/a[j]), j=1..i)): od:
that is, a(1) = 2 and a(i+1) = round(a(i) + 1/P(i)) with P(i) = product of (1 - 1/a(j)) over
j = 1..i. Below, st k = (a(k + 1), P(k + 1)): the second component carries the running product,
P(1) = 1/2 and P(k + 2) = P(k + 1) * (1 - 1/a(k + 2)). round is Mathlib's round (halves rounded
up), which agrees with Maple's round on positive numbers; in any case no tie x + 1/2 occurs among
the first 80 terms. The definition gives the listed terms 2, 4, 7, 10, 13, 17, 21, 25, 29, 34, ...
(all 57 listed terms checked).
-/

namespace OMA.S_oeis_a003067

/-- st k = (a(k+1), product of (1 - 1/a(j)) over j = 1..k+1). -/
noncomputable def st : ℕ → ℤ × ℚ
  | 0 => (2, 1 / 2)
  | (k + 1) => (round (((st k).1 : ℚ) + 1 / (st k).2),
      (st k).2 * (1 - 1 / ((round (((st k).1 : ℚ) + 1 / (st k).2) : ℤ) : ℚ)))

/-- A003067 (offset 1): a(n) = (st (n - 1)).1, so a(1) = 2, a(2) = 4, a(3) = 7, ... -/
noncomputable def a (n : ℕ) : ℤ := (st (n - 1)).1

/-- The comment of the entry: the g.f. (z^2+2+z^9+z^5)/(z-1)^2 conjectured by Plouffe is wrong. -/
theorem main : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * (PowerSeries.X - 1) ^ 2 ≠
    PowerSeries.X ^ 2 + 2 + PowerSeries.X ^ 9 + PowerSeries.X ^ 5 := by
  sorry

end OMA.S_oeis_a003067
