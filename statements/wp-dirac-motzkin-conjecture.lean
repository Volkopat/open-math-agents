import Mathlib

-- Dirac–Motzkin conjecture: n non-collinear points in the plane determine at least ⌊n/2⌋
-- ordinary lines.
-- Source: https://en.wikipedia.org/wiki/Sylvester%E2%80%93Gallai_theorem#The_number_of_ordinary_lines
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: an ordinary line of a point set is a line containing exactly two of its points. Let
`t₂(n)` be the minimum number of ordinary lines determined over every set of `n` non-collinear
points (in the Euclidean plane). Dirac conjectured that `t₂(n) ≥ ⌊n/2⌋` for all values of `n`;
this is often called the Dirac–Motzkin conjecture.

Conventions:
* The Euclidean plane is `EuclideanSpace ℝ (Fin 2)`; point sets are finite (`Finset`), and
  non-collinear is `¬ Collinear ℝ S` (Mathlib's `Collinear`).
* Ordinary lines are counted through the pairs of points spanning them: the line through two
  points `p ≠ q` of `S` is ordinary iff no third point of `S` is collinear with `p` and `q`, and
  distinct ordinary lines have distinct pairs. So the number of ordinary lines is the number of
  `2`-element subsets `T ⊆ S` such that every `r ∈ S` collinear with `T` lies in `T`.
* `⌊n/2⌋` is natural-number division `S.card / 2`.
-/

namespace OMA.S_wp_dirac_motzkin_conjecture

open Classical in
/-- The number of ordinary lines of a finite planar point set, counted by their point pairs. -/
noncomputable def ordinaryLines (S : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  ((S.powersetCard 2).filter fun T =>
    ∀ r ∈ S, Collinear ℝ (insert r (T : Set (EuclideanSpace ℝ (Fin 2)))) → r ∈ T).card

/-- Dirac–Motzkin: every finite non-collinear planar set of `n` points has at least `⌊n/2⌋`
ordinary lines. -/
theorem main : ∀ S : Finset (EuclideanSpace ℝ (Fin 2)),
    ¬ Collinear ℝ (S : Set (EuclideanSpace ℝ (Fin 2))) → S.card / 2 ≤ ordinaryLines S := by
  sorry

end OMA.S_wp_dirac_motzkin_conjecture
