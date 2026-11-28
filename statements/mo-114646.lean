import Mathlib

/-!
# Intersecting family of triangulations

Source: https://mathoverflow.net/questions/114646/intersecting-family-of-triangulations
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Problem (Kalai; Meagher): let `𝒯_n` be the set of triangulations of a convex `n`-gon by `n - 3`
non-crossing diagonals (`|𝒯_n| = C_{n-2}`). If `𝒮 ⊆ 𝒯_n` and every two triangulations in `𝒮`
share a diagonal, then `|𝒮| ≤ |𝒯_{n-1}| = C_{n-3}`.

Encoding. Vertices `0, …, n-1` in convex position, in cyclic order. A diagonal is a pair
`i < j` that are not cyclically adjacent (`j ≠ i + 1` and not `(i, j) = (0, n-1)`). Diagonals
`(i, j)`, `(k, l)` cross iff `i < k < j < l` or `k < i < l < j`. A triangulation is a set of
`n - 3` pairwise non-crossing diagonals. We take `n ≥ 4` (for `n = 3` the claim is trivial).
-/

namespace OMA.S_mo_114646

/-- `(i, j)` is a diagonal of the convex `n`-gon. -/
def IsDiagonal (n : ℕ) (d : ℕ × ℕ) : Prop :=
  d.1 < d.2 ∧ d.2 < n ∧ d.1 + 1 ≠ d.2 ∧ ¬ (d.1 = 0 ∧ d.2 = n - 1)

/-- Two diagonals cross. -/
def Cross (d e : ℕ × ℕ) : Prop :=
  (d.1 < e.1 ∧ e.1 < d.2 ∧ d.2 < e.2) ∨ (e.1 < d.1 ∧ d.1 < e.2 ∧ e.2 < d.2)

/-- Triangulations of the convex `n`-gon. -/
def IsTriangulation (n : ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  T.card = n - 3 ∧ (∀ d ∈ T, IsDiagonal n d) ∧ ∀ d ∈ T, ∀ e ∈ T, ¬ Cross d e

/-- The intersecting-family bound. -/
theorem main :
    ∀ n : ℕ, 4 ≤ n → ∀ S : Finset (Finset (ℕ × ℕ)),
      (∀ T ∈ S, IsTriangulation n T) → (∀ T ∈ S, ∀ T' ∈ S, (T ∩ T').Nonempty) →
      S.card ≤ catalan (n - 3) := by
  sorry

end OMA.S_mo_114646
