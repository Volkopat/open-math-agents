import OMAReductions.R_OeisA255916_conjecture_2_R1

-- Reduction OeisA255916.conjecture_2.R1.H1.R1 of step OeisA255916.conjecture_2.R1.H1
-- Credit: @arindale
--
-- H1 is the positive (universality) half of Sun's conjecture 2: every pair listed in
-- sunPolygonalPairsSet1 is universal for mixed heptagonal + two polygonal numbers.
-- The list splits naturally by the first coordinate j, and each family is a separate
-- universality problem for a fixed ternary shape:
--   * j = 3: 30 pairs  (generalized heptagonal + triangular + k-gonal, k in the list)
--   * j = 4: 14 pairs  (generalized heptagonal + square + k-gonal)
--   * the four sporadic pairs (5,6), (5,9), (6,7), (8,9)
-- Splitting them lets different agents attack different families; the combination is
-- purely bookkeeping on the finite set.

namespace OMA.R_OeisA255916_conjecture_2_R1_H1_R1

open OeisA255916

/-- The `j = 3` family: every listed pair with first coordinate 3 is universal. -/
def H1 : Prop :=
  ∀ k : ℕ, (3, k) ∈ OeisA255916.sunPolygonalPairsSet1 →
    ∀ n : ℕ, OeisA255916.IsSumOfGmPjPk 7 n 3 k

/-- The `j = 4` family: every listed pair with first coordinate 4 is universal. -/
def H2 : Prop :=
  ∀ k : ℕ, (4, k) ∈ OeisA255916.sunPolygonalPairsSet1 →
    ∀ n : ℕ, OeisA255916.IsSumOfGmPjPk 7 n 4 k

/-- The four sporadic listed pairs `(5,6), (5,9), (6,7), (8,9)` are universal. -/
def H3 : Prop :=
  ∀ pair ∈ OeisA255916.sunPolygonalPairsSet1, pair.1 ≠ 3 → pair.1 ≠ 4 →
    ∀ n : ℕ, OeisA255916.IsSumOfGmPjPk 7 n pair.1 pair.2

theorem main : H1 → H2 → H3 → OMA.R_OeisA255916_conjecture_2_R1.H1 := by
  intro h1 h2 h3 pair hpair
  rcases pair with ⟨j, k⟩
  by_cases hj3 : j = 3
  · subst hj3
    exact h1 k hpair
  · by_cases hj4 : j = 4
    · subst hj4
      exact h2 k hpair
    · exact h3 (j, k) hpair hj3 hj4

end OMA.R_OeisA255916_conjecture_2_R1_H1_R1
