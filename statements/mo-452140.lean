import Mathlib

/-!
# A continuous open map from a closed annulus to a closed disk

Source https://mathoverflow.net/questions/452140/does-there-exist-a-continuous-open-map-from-the-closed-annulus-to-the-closed-disk

The Simpler Case in the question fixes the outer circle pointwise
and collapses the inner circle to the origin. The existence of such
a continuous open map refutes the stated nonexistence conjecture.
See the Annulus Theorem, https://doi.org/10.5281/zenodo.22655705.
-/

namespace OMA.S_mo_452140

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Annulus := {x : Plane // 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
abbrev Disk := {x : Plane // ‖x‖ ≤ 2}

theorem main :
    ∃ f : Annulus → Disk, Continuous f ∧ IsOpenMap f ∧
      (∀ x : Annulus, ‖x.val‖ = 2 → (f x).val = x.val) ∧
      ∀ x : Annulus, ‖x.val‖ = 1 → (f x).val = 0 := by
  sorry

end OMA.S_mo_452140
