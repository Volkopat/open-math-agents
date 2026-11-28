import Mathlib

/-!
# A262115: Barker's recurrence for the periodic digits of 1/7 in base b

Source: https://oeis.org/A262115
Credit: @ivillar

Irregular triangle read by rows: row b (b >= 2) gives the periodic part of the digits of the
base-b expansion of 1/7 (offset 2; data 0, 0, 1, 0, 1, 0, 2, 1, 2, 0, 2, 1, 0, 3, 2, 4, 1, 2, 0,
5, 1, 1, 1, 2, 5, ...). Colin Barker conjectured (Oct 09 2015) a(n) = 2*a(n-22) - a(n-44) for
n > 44, together with the rational generating function determined by it.

Status: known result (Robert Israel, Dec 04 2015, sketches a proof in the entry: the digits in
base 7k + d are linear in k).

Formalization notes:
* The k-th digit (k >= 1) after the point of 1/7 in base b is floor(b^k / 7) mod b (`digit`).
* Row b lists the digits 1, ..., `len b`, where `len b` is the period of the expansion: the
  multiplicative order of b modulo 7 when 7 does not divide b (the expansion is then purely
  periodic), and 1 when 7 divides b (the expansion terminates after its single digit b/7, which
  the entry lists as the row, e.g. row 7 is 1 and row 14 is 2).
* The sequence is the concatenation of the rows b = 2, 3, 4, ...; with the entry's offset 2 its
  term a(n) is the entry of index n - 2 (counting from 0) of the concatenation, which already
  lies in the concatenation of the rows 2, ..., n + 1 (every row is nonempty).
* Barker's generating function x^3*(1 + x^2 + ...)/(x^44 - 2*x^22 + 1) gives the first term
  as the coefficient of x^1, i.e. he indexed the data from 1. His range n > 44 is therefore the
  range n > 45 for the entry's offset 2 used here (for n = 45 the recurrence would involve the
  undefined term a(1)). The recurrence is stated over ℤ; the generating function is not restated.
-/

namespace OMA.S_oeis_a262115

/-- The `k`-th digit after the point of the base-`b` expansion of `1/7`. -/
def digit (b k : ℕ) : ℕ := b ^ k / 7 % b

/-- The length of row `b`: the period of `1/7` in base `b` (the order of `b` modulo 7), or `1`
when `7 ∣ b` and the expansion terminates. -/
noncomputable def len (b : ℕ) : ℕ := if b % 7 = 0 then 1 else orderOf (b : ZMod 7)

/-- Row `b` of the triangle: the digits `1, ..., len b` of `1/7` in base `b`. -/
noncomputable def row (b : ℕ) : List ℕ := (List.range (len b)).map fun k => digit b (k + 1)

/-- A262115(n) (offset 2): the entry of index `n - 2` of the concatenation of the rows
`2, 3, ..., n + 1`. -/
noncomputable def a (n : ℕ) : ℕ := (((List.range n).map fun i => row (i + 2)).flatten).getD (n - 2) 0

/-- Barker's recurrence `a(n) = 2*a(n-22) - a(n-44)` (his range `n > 44` with the data indexed
from 1, i.e. `n > 45` for the entry's offset 2). -/
theorem main : ∀ n : ℕ, 45 < n → (a n : ℤ) = 2 * a (n - 22) - a (n - 44) := by
  sorry

end OMA.S_oeis_a262115
