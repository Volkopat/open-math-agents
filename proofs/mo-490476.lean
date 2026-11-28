import OMAStatements.S_mo_490476
import Mathlib

-- Problem mo-490476: (1) it is not true for all sets X, Y, Z and maps f : X -> Y that precomposition with f
-- (from maps Y -> Z to maps X -> Z) is injective iff f is surjective and surjective iff f is injective;
-- (2) it is true whenever Z has at least two elements.
-- Upstream: statements/mo-490476.lean (declaration OMA.S_mo_490476.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: (1) take X empty and Y = Z a one-point set. All maps into a one-point set are equal, so precomposition
-- is injective, but the map from the empty set to a point is not surjective. (2) is the standard fact that
-- g -> g o f is injective iff f is surjective and surjective iff f is injective when the target has two points.

open OMA.S_mo_490476

theorem OMA.solution : type_of% @OMA.S_mo_490476.main := by
  constructor
  · intro h
    have h1 := (h Empty Unit Unit (fun e => e.elim)).1
    have hinj : Function.Injective
        (precomp (fun e : Empty => (e.elim : Unit)) : (Unit → Unit) → (Empty → Unit)) := by
      intro g₁ g₂ _
      funext y
      exact Subsingleton.elim _ _
    obtain ⟨e, _⟩ := h1.mp hinj ()
    exact e.elim
  · intro X Y Z _ f
    unfold precomp
    exact ⟨Function.injective_comp_right_iff_surjective, Function.surjective_comp_right_iff_injective⟩
