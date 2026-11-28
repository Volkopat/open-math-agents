import FormalConjectures.GreensOpenProblems.«24»

/-!
# Green 24: the constant `γ = 1/3` as an upper and a lower bound

`max013AffineTranslates n` is the largest number of pairs `(x, y)` of distinct elements of an
`n`-element set `A ⊆ ℤ` with `x + 3 (y - x) ∈ A`. Equivalently it counts the solutions of
`2 u + w = 3 v` in `A` with `u ≠ v`: the point `v` cuts the segment from `u` to `w` in the ratio
`1 : 2`. The constant `γ` is the upper limit of `max013AffineTranslates n / n ^ 2`.

* `H1` is the upper bound `γ ≤ 1/3`. This is the open part: it is the discrete analogue, for
  the equation `2 u + w = 3 v`, of the rearrangement inequality that gives `1/3` for subsets of
  the real line.
* `H2` is the lower bound `1/3 ≤ γ`, from intervals. In `{0, …, 3m - 1}` every ordered pair
  `(u, w)` of distinct elements in the same residue class modulo `3` gives a solution, and
  there are `3 m (m - 1)` such pairs. This improves the bound `1/12` of
  `Green24.variants.lower_HL` to the conjectured value.

Remark, not formalized here: for a set `a_1 < … < a_n`, a fixed middle element `a_j` is the
point `v` of at most `min (j - 1, n - j)` solutions with `u < v` and as many with `u > v`,
which gives `γ ≤ 1/2`.
-/

namespace OMA.R_Green24_variants_conjecture_R1

/-- The open upper bound. -/
def H1 : Prop := Green24.variants.gamma ≤ 1 / 3

/-- The lower bound from intervals. -/
def H2 : Prop := (1 : ℝ) / 3 ≤ Green24.variants.gamma

theorem main : H1 → H2 → type_of% @Green24.variants.conjecture :=
  fun h1 h2 => le_antisymm h1 h2

end OMA.R_Green24_variants_conjecture_R1
