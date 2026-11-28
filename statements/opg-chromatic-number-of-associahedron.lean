import Mathlib

/-!
# Chromatic number of associahedron

Source: https://www.openproblemgarden.org/op/chromatic_number_of_associahedron
Credit: @shc261392

Conjecture (Fabila-Monroy, Flores-Peñaloza, Huemer, Hurtado, Urrutia, Wood): associahedra have
unbounded chromatic number.

The 1-skeleton of the associahedron is the flip graph of a convex `n`-gon: its vertices are the
triangulations of the polygon and two triangulations are adjacent when one is obtained from the
other by removing a single diagonal and replacing it by a different diagonal.

Reading used here:
* The polygon has vertices `0, 1, …, n-1` in convex position, in cyclic order.
* A diagonal is a pair `(i, j)` with `i + 2 ≤ j` and `(i, j) ≠ (0, n-1)` (so it joins two
  non-consecutive vertices); it is stored with `i < j`.
* Two diagonals `(i, j)` and `(k, l)` cross iff `i < k < j < l` or `k < i < l < j`
  (their endpoints interleave around the polygon).
* A triangulation is a set of diagonals, pairwise non-crossing, that is maximal: every diagonal
  outside it crosses one of its members.
* Two triangulations are adjacent iff each has exactly one diagonal the other lacks.
-/

namespace OMA.S_opg_chromatic_number_of_associahedron

/-- `(i, j)` is a diagonal of the convex `n`-gon, stored with `i < j`. -/
def IsDiagonal {n : ℕ} (d : Fin n × Fin n) : Prop :=
  (d.1 : ℕ) + 2 ≤ d.2 ∧ ¬ ((d.1 : ℕ) = 0 ∧ (d.2 : ℕ) + 1 = n)

/-- Two diagonals cross when their endpoints interleave. -/
def Cross {n : ℕ} (d e : Fin n × Fin n) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

/-- A triangulation: a maximal set of pairwise non-crossing diagonals. -/
def IsTriangulation {n : ℕ} (T : Finset (Fin n × Fin n)) : Prop :=
  (∀ d ∈ T, IsDiagonal d) ∧ (∀ d ∈ T, ∀ e ∈ T, ¬ Cross d e) ∧
    ∀ d, IsDiagonal d → d ∉ T → ∃ e ∈ T, Cross d e

/-- The flip graph of the convex `n`-gon (the 1-skeleton of the associahedron). -/
def flipGraph (n : ℕ) : SimpleGraph {T : Finset (Fin n × Fin n) // IsTriangulation T} :=
  SimpleGraph.fromRel fun T T' => (T.1 \ T'.1).card = 1 ∧ (T'.1 \ T.1).card = 1

theorem main : ∀ c : ℕ, ∃ n : ℕ, (c : ℕ∞) < (flipGraph n).chromaticNumber := by
  sorry

end OMA.S_opg_chromatic_number_of_associahedron
