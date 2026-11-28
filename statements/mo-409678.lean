import Mathlib

/-!
# Does a compact convex set meeting every facet of the cube contain the origin?

Source: https://mathoverflow.net/questions/409678
Credit: @koolkao

Question (Kacper Kurowski, MathOverflow 409678, 2021; CC BY-SA 4.0). Let `(V, ‖·‖)` be a normed
space and consider the set `C = [-1,1]^{dim V}`. The boundary of this set consists of closed
subsets `B_i` of affine hyperplanes. Consider a set `K` that is compact and convex and meets every
`B_i`. Does it follow that `0 ∈ K`? It seems to be true if `dim V < ∞`.

`main` states that the answer is yes in every finite dimension `n ≥ 1`. A disproof is a dimension
`n` and a compact convex set in `ℝⁿ` that meets every facet of `[-1,1]ⁿ` but does not contain `0`.

Translation choices:
* `V` is `ℝⁿ = Fin n → ℝ` with its coordinates, so that `C = [-1,1]ⁿ` is the set of `x` with
  `|x j| ≤ 1` for all `j`; the norm of `V` plays no role (in finite dimension all norms give the
  same compact sets);
* the pieces `B_i` of the boundary are the `2n` facets `{x ∈ C : x i = 1}` and
  `{x ∈ C : x i = -1}`, `i < n`;
* the dimension is `n ≥ 1`: for `n = 0` the cube is a point with no facets and `K = ∅` would
  satisfy the hypotheses vacuously;
* only the finite-dimensional case of Question 1 is stated; the infinite-dimensional case and the
  source's Question 2 (other families of sets `B_i`) are not.
-/

namespace OMA.S_mo_409678

/-- A compact convex subset of `ℝⁿ` (`n ≥ 1`) that meets every facet of the cube `[-1,1]ⁿ`
contains the origin. -/
theorem main :
    ∀ (n : ℕ), 1 ≤ n → ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K →
      (∀ (i : Fin n) (s : ℝ), (s = 1 ∨ s = -1) →
        ∃ x ∈ K, x i = s ∧ ∀ j, |x j| ≤ 1) →
      (0 : Fin n → ℝ) ∈ K := by
  sorry

end OMA.S_mo_409678
