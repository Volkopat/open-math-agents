import Mathlib

/-!
# Simplices whose intersection with the nonnegative orthant is the unit simplex

Source: Eilon, https://mathoverflow.net/questions/266728 (CC BY-SA 3.0).
Credit: @connoranderson.

Column j is the proposed vertex rʲ. The unit simplex consists of nonnegative
vectors whose coordinates sum to one, as in the source's three-dimensional
example. The criterion uses only column sums and signs of determinants.
In dimension four the entries of the adjugate are signed 3-by-3 minors.
-/

namespace OMA.S_mo_266728

def Config {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, A i i = 0) ∧
    convexHull ℝ (Set.range A.col) ∩ {v : Fin n → ℝ | ∀ i, 0≤v i} = stdSimplex ℝ (Fin n)

theorem main : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    Config A ↔ (∀ i, A i i = 0) ∧ (∀ j, ∑ i, A i j = 1) ∧
      A.det ≠ 0 ∧ ∀ i j, 0 ≤ A.det * A.adjugate i j := by
  sorry

end OMA.S_mo_266728
