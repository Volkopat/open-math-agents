import Mathlib

/-!
# Counting 3-colorings of the hex lattice

Source: https://www.openproblemgarden.org/op/counting_3_colorings_of_the_hex_lattice
(Open Problem Garden; author listed: Carsten Thomassen)
Credit: @PipeCruz

The source: let `𝒯` be the regular triangular tiling of the plane, and for `n ≥ 1` let `T_n` be
the triangulation of the torus obtained from a regular hexagonal piece of `𝒯` of side length `n`
by identifying opposite edges of the hexagon. Let `H_n` be the dual of `T_n` (a hexagonal tiling of
the torus), and let `χ(G, 3)` be the number of proper `3`-colorings of `G`. The problem is to find
`lim_{n → ∞} χ(H_n, 3) ^ (1 / |V(H_n)|)`. The source gives no conjectured value; it notes that
Thomassen's theorem on planar graphs of girth at least `5` gives the lower bound `2 ^ (1/10000)`,
assuming the limit exists, and compares with Lieb's value `(4/3) ^ (3/2)` for the square lattice.

Reading. Since the source asks for the value of a limit and gives no candidate, and since its own
lower bound is stated only assuming the limit exists, `main` states that the limit exists (as a
real number). The value itself has no closed form to state. The reviewer may prefer a different
reading; this one is the existence part of the question, which every answer to it presupposes.

Construction (axial coordinates, all standard):
* `𝒯` is `ℤ × ℤ`, the point `(q, r)` being adjacent to `(q ± 1, r)`, `(q, r ± 1)`, `(q + 1, r - 1)`
  and `(q - 1, r + 1)`. Its triangles are the up triangles `{(q, r), (q + 1, r), (q, r + 1)}` and
  the down triangles `{(q + 1, r), (q, r + 1), (q + 1, r + 1)}`, one of each for every point.
* The hexagonal piece of side `n` is `max(|q|, |r|, |q + r|) ≤ n`. Identifying opposite edges is the
  quotient by the translations `(2n, -n)`, `(n, -2n)` and `(n, n)`, which generate the lattice
  `Λ n = ⟨(2n, -n), (n, n)⟩` of index `3 n ^ 2`, so `T_n` is `𝒯 / Λ n` (with `3 n ^ 2` vertices;
  the hexagon has `3n² + 3n + 1` points, of which the `6n` boundary points are glued in classes).
* The vertices of `H_n` are the `6 n ^ 2` triangles of `T_n`: a point of `𝒯 / Λ n` with a flag
  (`true` for its up triangle, `false` for its down triangle). Two triangles are adjacent in the
  dual when they share an edge: the up triangle at `p` shares its three edges with the down
  triangles at `p`, `p - (1, 0)` and `p - (0, 1)`, and up (resp. down) triangles never share an edge
  with each other. `Adj` is this relation, symmetrized.
* A proper `3`-coloring is a map to `Fin 3` giving adjacent vertices different colors, and
  `numColorings n` counts them. `|V(H_n)|` is `Nat.card (V n)`.
For small `n` (`n = 1`) the dual may have parallel edges; this does not affect the count of proper
colorings or the limit.
-/

namespace OMA.S_opg_counting_3_colorings_of_the_hex_lattice

open Filter Topology

/-- The lattice of translations identifying opposite edges of the hexagon of side `n`. -/
def Λ (n : ℕ) : AddSubgroup (ℤ × ℤ) :=
  AddSubgroup.closure {((2 * n : ℤ), -(n : ℤ)), ((n : ℤ), (n : ℤ))}

/-- The vertices of the torus triangulation `T_n`. -/
abbrev Pt (n : ℕ) : Type := (ℤ × ℤ) ⧸ Λ n

/-- The vertices of `H_n`: the triangles of `T_n` (`true`: up triangle, `false`: down triangle). -/
abbrev V (n : ℕ) : Type := Pt n × Bool

/-- The unit translation `(1, 0)` on the torus. -/
def e₁ (n : ℕ) : Pt n := QuotientAddGroup.mk ((1 : ℤ), (0 : ℤ))

/-- The unit translation `(0, 1)` on the torus. -/
def e₂ (n : ℕ) : Pt n := QuotientAddGroup.mk ((0 : ℤ), (1 : ℤ))

/-- Adjacency in `H_n`: an up triangle and a down triangle sharing an edge. -/
def Adj (n : ℕ) (x y : V n) : Prop :=
  (x.2 = true ∧ y.2 = false ∧ (y.1 = x.1 ∨ y.1 = x.1 - e₁ n ∨ y.1 = x.1 - e₂ n)) ∨
  (y.2 = true ∧ x.2 = false ∧ (x.1 = y.1 ∨ x.1 = y.1 - e₁ n ∨ x.1 = y.1 - e₂ n))

/-- `χ(H_n, 3)`: the number of proper `3`-colorings of `H_n`. -/
noncomputable def numColorings (n : ℕ) : ℕ :=
  Nat.card {c : V n → Fin 3 // ∀ x y, Adj n x y → c x ≠ c y}

/-- The limit `lim_{n → ∞} χ(H_n, 3) ^ (1 / |V(H_n)|)` exists. -/
theorem main : ∃ L : ℝ, Tendsto
    (fun n : ℕ => (numColorings n : ℝ) ^ ((1 : ℝ) / (Nat.card (V n) : ℝ))) atTop (𝓝 L) := by
  sorry

end OMA.S_opg_counting_3_colorings_of_the_hex_lattice
