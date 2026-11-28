import Mathlib

/-!
# OEIS A223332: Barker's g.f. and closed form for rolling cube footprints on 3 X n arrays

Source: https://oeis.org/A223332 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Mar 19 2013), offset 1: Rolling cube footprints: number of 3 X n 0..7
arrays starting with 0 where 0..7 label vertices of a cube and every array movement to a
horizontal or antidiagonal neighbor moves along a corresponding cube edge. Row 3 of A223331.
Data: 64, 243, 3969, 64827, 1059723, ... Formula: Empirical: a(n) = 18*a(n-1) - 27*a(n-2) for
n>4. Conjectures from Colin Barker, Aug 19 2018: G.f.: x*(64 - 909*x + 1323*x^2 - 54*x^3) /
(1 - 18*x + 27*x^2). a(n) = (49/54)*((9-3*sqrt(6))^n + (3*(3+sqrt(6)))^n) for n>2.

Formalization notes:
* The labels 0..7 are the vertices of the cube {0,1}^3 written in binary, and a move along a cube
  edge joins two labels that differ in exactly one bit. Any other labelling gives the same count:
  a relabelling is a graph isomorphism and the cube is vertex-transitive, so the condition
  starting with 0 is equivalent to starting with any fixed vertex.
* A 3 X n array is f : Fin 3 -> Fin n -> Fin 8 with f i j in row i and column j; starting with 0
  means that the top left entry f 0 0 is 0. Its horizontal neighbours are (i, j) and (i, j + 1),
  its antidiagonal neighbours (i, j + 1) and (i + 1, j); each such pair must carry adjacent
  vertices. The phrase corresponding cube edge is read as an edge of the cube between the two
  labels; with this reading the count reproduces all thirteen terms of the entry's data, which the
  proof file checks.
* The g.f. is Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x)*D(x) = N(x) in Q[[x]], which is
  equivalent to A = N/D because D has constant term 1.
* The closed form is stated in the reals for every n > 2, as in the entry.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..13) = 64, 243, 3969, 64827, 1059723, 17324685,
  283231809, 4630406067, 75700050363, 1237579942725, 20232537609249, 330771018512907,
  5407599817782603, the entry's data.
-/

namespace OMA.S_oeis_a223332

open PowerSeries Finset

/-- The cube on the labels 0..7: a label is the binary expansion of a vertex of {0,1}^3, and two
labels are adjacent when they differ in exactly one bit. -/
def adj (x y : Fin 8) : Prop := x.val ^^^ y.val = 1 ∨ x.val ^^^ y.val = 2 ∨ x.val ^^^ y.val = 4

instance : DecidableRel adj := fun x y => by unfold adj; infer_instance

/-- A223332: the number of 3 X n arrays f (f i j in row i, column j) with entries 0..7 whose top
left entry is 0 and in which every pair of horizontal neighbours (i, j), (i, j + 1) and every pair
of antidiagonal neighbours (i, j + 1), (i + 1, j) carries adjacent vertices of the cube. -/
def a (n : ℕ) : ℕ :=
  ((univ : Finset (Fin 3 → Fin n → Fin 8)).filter (fun f =>
    (∀ j : Fin n, j.val = 0 → f 0 j = 0) ∧
    (∀ i : Fin 3, ∀ j j' : Fin n, j'.val = j.val + 1 → adj (f i j) (f i j')) ∧
    (∀ i i' : Fin 3, i'.val = i.val + 1 → ∀ j j' : Fin n, j'.val = j.val + 1 →
      adj (f i j') (f i' j)))).card

/-- Barker's conjectures: the g.f. and the closed form. -/
theorem main : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    (1 - 18 * X + 27 * X ^ 2) = X * (64 - 909 * X + 1323 * X ^ 2 - 54 * X ^ 3) ∧
    ∀ n : ℕ, 2 < n →
      (a n : ℝ) = (49 / 54) * ((9 - 3 * Real.sqrt 6) ^ n + (3 * (3 + Real.sqrt 6)) ^ n) := by
  sorry

end OMA.S_oeis_a223332
