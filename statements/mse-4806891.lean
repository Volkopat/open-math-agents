import Mathlib

/-!
# Does there exist a midsquare with natural sides and diagonal?

Source: https://math.stackexchange.com/questions/4806891/does-there-exist-a-midsquare-with-natural-sides-and-diagonal
Credit: @jeonbik

A midsquare is an orthodiagonal and equidiagonal quadrilateral (source).
The question asks for naturals a, b, c, d, e such that the quadrilateral
with sides a, b, c, d and diagonal e is a midsquare. See the comment on
`main` for how this is encoded.

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_mse_4806891

/-- Encoding of the source's question. The diagonal e is read as the
diagonal splitting the quadrilateral into the triangles of sides
(a, b, e) and (c, d, e); this is the reading that reproduces the
source's own formulas and its numerical table (for example the row
a, b, c, d = 35, 101, 149, 115 with e ^ 2 = 16704 satisfies the
triangle inequalities, the orthodiagonal condition and the quartic
below). The clauses are:

- the strict triangle inequalities: the two triangles exist as
  genuine non-degenerate triangles. They also force a, b, c, d, e
  to be positive, which is the usual sense of natural on the source
  site, so no separate positivity clause is needed;
- a ^ 2 + c ^ 2 = b ^ 2 + d ^ 2: the classical orthodiagonal
  condition, a quadrilateral has perpendicular diagonals iff the
  sums of the squares of opposite sides are equal;
- the last equation: the source's own equidiagonal condition
  2 * e ^ 4 - 2 * (a ^ 2 + c ^ 2) * e ^ 2 + (a ^ 2 - b ^ 2) ^ 2
  + (b ^ 2 - c ^ 2) ^ 2 = 0, rearranged into natural-number form
  by expanding the squares and moving terms across, so that no
  truncated subtraction on naturals is needed. Expanding,
  (a ^ 2 - b ^ 2) ^ 2 + (b ^ 2 - c ^ 2) ^ 2
  = a ^ 4 + 2 * b ^ 4 + c ^ 4 - 2 * a ^ 2 * b ^ 2 - 2 * b ^ 2 * c ^ 2;
- 2 * e ^ 2 ≥ a ^ 2 + c ^ 2: this selects the larger root of that
  quadratic in e ^ 2, the root the source writes as
  e ^ 2 = (a ^ 2 + c ^ 2 + sqrt D) / 2 with
  D = 4 * b ^ 2 * d ^ 2 - (a ^ 2 - c ^ 2) ^ 2. The smaller root is
  extraneous: it makes e the difference of the two triangle heights
  rather than their sum, so it does not give equal diagonals. For
  example, with a, b, c, d = 35, 101, 149, 115 as above, the smaller
  root e ^ 2 = 6722 also satisfies the quartic and the triangle
  inequalities, but the other diagonal is about 146.37 while
  e is about 81.99, so that quadruple is not a midsquare. Without
  this clause the statement would be strictly weaker than the
  source's question.
-/
theorem main : ∃ a b c d e : ℕ,
    (e < a + b ∧ b < a + e ∧ a < b + e) ∧
    (e < c + d ∧ d < c + e ∧ c < d + e) ∧
    a ^ 2 + c ^ 2 = b ^ 2 + d ^ 2 ∧
    2 * e ^ 2 ≥ a ^ 2 + c ^ 2 ∧
    2 * e ^ 4 + a ^ 4 + 2 * b ^ 4 + c ^ 4
      = 2 * (a ^ 2 + c ^ 2) * e ^ 2 + 2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 := by
  sorry

end OMA.S_mse_4806891
