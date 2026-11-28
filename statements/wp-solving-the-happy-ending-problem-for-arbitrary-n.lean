import Mathlib

-- Happy ending problem for arbitrary N (Erdős–Szekeres conjecture): f(N) = 1 + 2^(N-2).
-- Source: https://en.wikipedia.org/wiki/Happy_ending_problem
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
Source: let `f(N)` denote the minimum `M` for which any set of `M` points in general position (in
the plane) must contain a convex `N`-gon. Erdős and Szekeres conjectured
`f(N) = 1 + 2^(N-2)` for all `N ≥ 3`. (The lower bound `f(N) ≥ 1 + 2^(N-2)` is known.)

Conventions:
* The plane is `EuclideanSpace ℝ (Fin 2)`; point sets are `Finset`s (distinct points).
* General position: no three points collinear (the source's footnote: no two points coincide and
  no three are collinear).
* `S` contains a convex `N`-gon: some `N`-element subset `T ⊆ S` is in convex position, i.e. no
  point of `T` lies in the convex hull of the other points of `T`.
* `f(N)` is `sInf` of the set of `M` such that every `M`-point set in general position contains a
  convex `N`-gon. By the Erdős–Szekeres theorem this set is nonempty, so `sInf` is its minimum;
  were it empty, `sInf` would be `0` and the statement below false, not vacuous.
-/

namespace OMA.S_wp_solving_the_happy_ending_problem_for_arbitrary_n

/-- No three points of `S` are collinear. -/
def GeneralPosition (S : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ T ⊆ S, T.card = 3 → ¬ Collinear ℝ (T : Set (EuclideanSpace ℝ (Fin 2)))

/-- `T` is in convex position: the vertices of a convex polygon. -/
def ConvexPosition (T : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ T, p ∉ convexHull ℝ ((T.erase p : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)))

/-- `f(N)`: the least `M` such that every set of `M` points in general position contains a convex
`N`-gon. -/
noncomputable def f (N : ℕ) : ℕ :=
  sInf {M : ℕ | ∀ S : Finset (EuclideanSpace ℝ (Fin 2)), S.card = M → GeneralPosition S →
    ∃ T ⊆ S, T.card = N ∧ ConvexPosition T}

/-- The Erdős–Szekeres conjecture. -/
theorem main : ∀ N : ℕ, 3 ≤ N → f N = 1 + 2 ^ (N - 2) := by
  sorry

end OMA.S_wp_solving_the_happy_ending_problem_for_arbitrary_n
