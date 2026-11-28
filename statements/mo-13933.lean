import Mathlib

/-!
# The Newtonian three-body problem starting from rest

Before the first collinear configuration, the two questions concern decrease
of the weighted squared-distance sum and preservation of strict side-length
ordering in the equal-mass case.

[MathOverflow question](https://mathoverflow.net/questions/13933/dropping-three-bodies)
-/

open scoped BigOperators ContDiff

namespace OMA.S_mo_13933

abbrev Space := EuclideanSpace ℝ (Fin 3)

abbrev Positions := Fin 3 → ℝ → Space

noncomputable def separation (q : Positions) (i j : Fin 3) (t : ℝ) : ℝ :=
  dist (q i t) (q j t)

noncomputable def inertia (m : Fin 3 → ℝ) (q : Positions) (t : ℝ) : ℝ :=
  m 0 * m 1 * separation q 0 1 t ^ 2 +
    m 1 * m 2 * separation q 1 2 t ^ 2 +
    m 0 * m 2 * separation q 0 2 t ^ 2

def OrderedSides (q : Positions) (t : ℝ) : Prop :=
  0 < separation q 0 1 t ∧
    separation q 0 1 t < separation q 1 2 t ∧
    separation q 1 2 t < separation q 0 2 t

def StartsFromRest (m : Fin 3 → ℝ) (q : Positions) (tc : ℝ) : Prop :=
  0 < tc ∧
    (∀ i, ContinuousOn (q i) (Set.Icc 0 tc) ∧
      ContDiffOn ℝ 2 (q i) (Set.Ico 0 tc) ∧
      derivWithin (q i) (Set.Ico 0 tc) 0 = 0) ∧
    (∀ t ∈ Set.Ico 0 tc, AffineIndependent ℝ (fun i => q i t)) ∧
    (¬ AffineIndependent ℝ (fun i => q i tc)) ∧
    ∀ t ∈ Set.Ioo 0 tc, ∀ i : Fin 3,
      deriv (deriv (q i)) t =
        ∑ j ∈ Finset.univ.erase i,
          (m j / separation q i j t ^ 3) • (q j t - q i t)

theorem main :
    ∀ (m : Fin 3 → ℝ) (q : Positions) (tc : ℝ),
      (∀ i, 0 < m i) → StartsFromRest m q tc →
      AntitoneOn (inertia m q) (Set.Ioo 0 tc) ∧
        ((∀ i j, m i = m j) → OrderedSides q 0 →
          ∀ t ∈ Set.Ioo 0 tc, OrderedSides q t) := by
  sorry

end OMA.S_mo_13933
