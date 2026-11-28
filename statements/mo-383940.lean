import Mathlib

/-!
# Equal circumradii of all simplices of a finite point set

Source: https://mathoverflow.net/questions/383940
Asked by MathOverflow user Manfred Weis (Sufficient coordinate-free condition for points
being co-spheric).

Let `P` be a finite set of points in Euclidean space `E^n`. The question asks whether the
following holds: if all the circumspheres of the `n`-simplices with corners in `P` have the
same radius, then these circumspheres have the same center (so that `P` is co-spheric).

Translation choices.
* `E^n` is `EuclideanSpace ℝ (Fin n)`. An `n`-simplex with corners in `P` is a Mathlib
  `Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n`, i.e. `n + 1` affinely independent points,
  all lying in `P`. Its circumsphere has center `circumcenter` and radius `circumradius`.
* `main` is the claim for every dimension `n` and every finite `P`: if any two such
  simplices have the same circumradius, then any two such simplices have the same
  circumcenter.
-/

namespace OMA.S_mo_383940

theorem main :
    ∀ n : ℕ, ∀ P : Set (EuclideanSpace ℝ (Fin n)), P.Finite →
      (∀ s t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n,
        Set.range s.points ⊆ P → Set.range t.points ⊆ P → s.circumradius = t.circumradius) →
      ∀ s t : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n,
        Set.range s.points ⊆ P → Set.range t.points ⊆ P → s.circumcenter = t.circumcenter := by
  sorry

end OMA.S_mo_383940
