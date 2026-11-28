import Mathlib

/-!
# A326278: n-vertex, 2-edge multigraphs that are not nesting (or not crossing)

Source: https://oeis.org/A326278 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A326278, offset 0: Number of n-vertex, 2-edge multigraphs that are not nesting. Number of
n-vertex, 2-edge multigraphs that are not crossing. Data
0, 0, 1, 9, 34, 90, 195, 371, 644, 1044, 1605, 2365, 3366, 4654, 6279, 8295, 10760, ...
Comment: Two edges {a,b}, {c,d} are crossing if a < c < b < d or c < a < d < b, and nesting if
a < c < d < b or c < a < b < d.
Example: The a(3) = 9 non-crossing multigraphs: {12,12}, {12,13}, {12,23}, {13,12}, {13,13},
{13,23}, {23,12}, {23,13}, {23,23}.

Formula section, Conjectures from Colin Barker, Jun 25 2019:
G.f.: x^2*(1 + 4*x - x^2) / (1 - x)^5.
a(n) = (n*(3 - 4*n + n^3)) / 6.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>4.

Formalization notes.
* The example of the entry lists both {12,13} and {13,12}, so a 2-edge multigraph is an ordered
  pair of edges, and an edge is a pair of vertices a < b. The vertices are 0..n-1 here.
  `notNesting n` and `notCrossing n` count the quadruples (a, b, c, d) with a < b, c < d that are
  not nesting, respectively not crossing. Both agree with the data for n = 0..7.
* The closed form is stated without division and subtraction of natural numbers as
  6 a(n) + 4 n^2 = n (n^3 + 3). The generating function is the closed form (a polynomial of
  degree 4 in n), and the recurrence is stated separately. The title claims that the two
  counts are equal; `main` states this too.
-/

namespace OMA.S_oeis_a326278

open Finset

/-- The number of ordered pairs of edges ({a,b}, {c,d}), a < b, c < d, on the vertices 0..n-1
that are not nesting: not (a < c < d < b) and not (c < a < b < d). -/
def notNesting (n : ℕ) : ℕ :=
  ((range n ×ˢ range n ×ˢ range n ×ˢ range n).filter (fun q : ℕ × ℕ × ℕ × ℕ =>
    q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2 ∧
    ¬ (q.1 < q.2.2.1 ∧ q.2.2.1 < q.2.2.2 ∧ q.2.2.2 < q.2.1) ∧
    ¬ (q.2.2.1 < q.1 ∧ q.1 < q.2.1 ∧ q.2.1 < q.2.2.2))).card

/-- The number of ordered pairs of edges ({a,b}, {c,d}), a < b, c < d, that are not crossing:
not (a < c < b < d) and not (c < a < d < b). -/
def notCrossing (n : ℕ) : ℕ :=
  ((range n ×ˢ range n ×ˢ range n ×ˢ range n).filter (fun q : ℕ × ℕ × ℕ × ℕ =>
    q.1 < q.2.1 ∧ q.2.2.1 < q.2.2.2 ∧
    ¬ (q.1 < q.2.2.1 ∧ q.2.2.1 < q.2.1 ∧ q.2.1 < q.2.2.2) ∧
    ¬ (q.2.2.1 < q.1 ∧ q.1 < q.2.2.2 ∧ q.2.2.2 < q.2.1))).card

/-- Barker's conjectures: a(n) = n(3 - 4n + n^3)/6 and the recurrence of order 5; the two
counts of the title are equal. -/
theorem main :
    (∀ n : ℕ, 6 * notNesting n + 4 * n ^ 2 = n * (n ^ 3 + 3)) ∧
    (∀ n : ℕ, notCrossing n = notNesting n) ∧
    (∀ n : ℕ, 4 < n → (notNesting n : ℤ) = 5 * notNesting (n - 1) - 10 * notNesting (n - 2)
      + 10 * notNesting (n - 3) - 5 * notNesting (n - 4) + notNesting (n - 5)) := by
  sorry

end OMA.S_oeis_a326278
