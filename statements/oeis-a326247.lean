import Mathlib

/-!
# A326247: Barker's closed form and recurrence for 2-edge multigraphs neither crossing nor nesting

Source: https://oeis.org/A326247
Credit: @ivillar

Number of labeled n-vertex 2-edge multigraphs that are neither crossing nor nesting (offset 0;
data 0, 0, 1, 9, 32, 80, 165, 301, 504, 792, ...). Two edges {a,b}, {c,d} are crossing if
a < c < b < d or c < a < d < b, and nesting if a < c < d < b or c < a < b < d. Colin Barker
conjectured (Jun 21 2019) the g.f. x^2*(1 + 4*x - 3*x^2) / (1 - x)^5,
a(n) = (n*(12 - 19*n + 6*n^2 + n^3)) / 12, and
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n > 4.

Status: open conjecture (Colin Barker, Jun 21 2019).

Formalization notes:
* The vertices are 0, ..., n-1 (any n labels in increasing order give the same count). An edge
  {a,b} (a ≠ b; the example lists only edges between distinct vertices) is written as the pair
  `(a, b)` with `a < b`.
* As in the entry's list of the a(3) = 9 pairs of edges ({12,12}, {12,13}, ..., {23,23}, with
  {12,13} and {13,12} both listed), a 2-edge multigraph is an ordered pair `(e, f)` of edges, and
  the two edges may coincide.
* The closed form is stated multiplied out by 12 over ℤ, for every n; the recurrence is stated
  over ℤ for n > 4. The generating function is the rational function determined by the closed
  form and is not restated.
-/

namespace OMA.S_oeis_a326247

/-- The edges `(a, b)` (with `a < b`) and `(c, d)` (with `c < d`) are crossing. -/
abbrev Crossing (a b c d : ℕ) : Prop := a < c ∧ c < b ∧ b < d ∨ c < a ∧ a < d ∧ d < b

/-- The edges `(a, b)` (with `a < b`) and `(c, d)` (with `c < d`) are nesting. -/
abbrev Nesting (a b c d : ℕ) : Prop := a < c ∧ c < d ∧ d < b ∨ c < a ∧ a < b ∧ b < d

/-- A326247(n): ordered pairs of edges `((a, b), (c, d))` on the vertices `0, ..., n-1` that are
neither crossing nor nesting. -/
def a (n : ℕ) : ℕ :=
  (((Finset.range n ×ˢ Finset.range n) ×ˢ (Finset.range n ×ˢ Finset.range n)).filter fun e =>
    e.1.1 < e.1.2 ∧ e.2.1 < e.2.2 ∧ ¬ Crossing e.1.1 e.1.2 e.2.1 e.2.2 ∧
      ¬ Nesting e.1.1 e.1.2 e.2.1 e.2.2).card

/-- Barker's conjectured closed form (for every `n`) and recurrence (for `n > 4`). -/
theorem main :
    (∀ n : ℕ, 12 * (a n : ℤ) = n * (12 - 19 * n + 6 * n ^ 2 + n ^ 3)) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) -
      5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a326247
