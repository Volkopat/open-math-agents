import Mathlib

/-!
# Average diameter of a bounded cell of a simple arrangement

Source: https://www.openproblemgarden.org/op/average_diameter_of_a_bounded_cell_of_a_simple_arrangement
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Deza–Terlaky–Zinchenko): the average diameter of a bounded cell of a simple
arrangement of `n` hyperplanes in dimension `d` is at most `d`.

Conventions.
* Hyperplanes `H_i = {x | ⟪a_i, x⟫ = b_i}` in `ℝ^d`, `a_i ≠ 0`, `i < n`. Simple: every `d` of
  them meet in exactly one point and no `d + 1` of them have a common point.
* Cells are the nonempty regions `{x | ∀ i, σ_i (⟪a_i, x⟫ - b_i) > 0}` for sign vectors `σ`;
  bounded cells are the bounded ones.
* The diameter `δ(P)` of a cell is the diameter of the edge graph of the polytope `cl P`. In a
  simple arrangement the vertices of `cl P` are the points of `cl P` lying on `d` hyperplanes,
  and two of them span an edge of `cl P` iff they lie on `d - 1` common hyperplanes.
* "Average `≤ d`" is written `∑ δ(P) ≤ d · #(bounded cells)` (equivalent when there is a
  bounded cell; vacuous otherwise).
-/

namespace OMA.S_opg_average_diameter_of_a_bounded_cell_of_a_simple_arrangement

open Classical

variable {d n : ℕ}

/-- Euclidean space `ℝ^d`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- An arrangement of `n` hyperplanes `⟪a i, x⟫ = b i` in `ℝ^d`. -/
structure Arrangement (d n : ℕ) where
  a : Fin n → E d
  b : Fin n → ℝ
  a_ne : ∀ i, a i ≠ 0

/-- Indices of the hyperplanes through `x`. -/
noncomputable def Arrangement.through (A : Arrangement d n) (x : E d) : Finset (Fin n) :=
  Finset.univ.filter fun i => inner ℝ (A.a i) x = A.b i

/-- The arrangement is simple. -/
def Arrangement.Simple (A : Arrangement d n) : Prop :=
  (∀ S : Finset (Fin n), S.card = d → ∃! x : E d, S ⊆ A.through x) ∧
  ∀ x : E d, (A.through x).card ≤ d

/-- The open region with sign vector `σ` (`true` = positive side). -/
def Arrangement.region (A : Arrangement d n) (σ : Fin n → Bool) : Set (E d) :=
  {x | ∀ i, if σ i then A.b i < inner ℝ (A.a i) x else inner ℝ (A.a i) x < A.b i}

/-- Its closure, as the closed region with the same signs. -/
def Arrangement.closedRegion (A : Arrangement d n) (σ : Fin n → Bool) : Set (E d) :=
  {x | ∀ i, if σ i then A.b i ≤ inner ℝ (A.a i) x else inner ℝ (A.a i) x ≤ A.b i}

/-- `σ` gives a bounded cell. -/
def Arrangement.IsBoundedCell (A : Arrangement d n) (σ : Fin n → Bool) : Prop :=
  (A.region σ).Nonempty ∧ Bornology.IsBounded (A.region σ)

/-- Vertices of the cell `σ`. -/
def Arrangement.cellVertices (A : Arrangement d n) (σ : Fin n → Bool) : Set (E d) :=
  {x | x ∈ A.closedRegion σ ∧ (A.through x).card = d}

/-- Edge graph of the cell `σ`. -/
def Arrangement.cellGraph (A : Arrangement d n) (σ : Fin n → Bool) :
    SimpleGraph (A.cellVertices σ) :=
  SimpleGraph.fromRel fun v w => (A.through v.1 ∩ A.through w.1).card + 1 = d

/-- Diameter of the cell `σ`. -/
noncomputable def Arrangement.cellDiam (A : Arrangement d n) (σ : Fin n → Bool) : ℕ :=
  (A.cellGraph σ).diam

/-- The conjecture: average diameter of a bounded cell `≤ d`. -/
theorem main :
    ∀ (d n : ℕ) (A : Arrangement d n), A.Simple →
      (∑ σ ∈ Finset.univ.filter A.IsBoundedCell, A.cellDiam σ) ≤
        d * (Finset.univ.filter A.IsBoundedCell).card := by
  sorry

end OMA.S_opg_average_diameter_of_a_bounded_cell_of_a_simple_arrangement
