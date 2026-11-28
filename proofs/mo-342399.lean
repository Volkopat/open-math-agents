import OMAStatements.S_mo_342399
import Mathlib

-- Problem: mo-342399, the right adjoint of an R-linear functor between R-linear categories is
-- R-linear.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- The hom-set bijection of the adjunction is injective, and under it both G(r f) and r G(f)
-- correspond to r (counit ; f), using the linearity of F and the naturality of the counit.

open CategoryTheory

theorem OMA.solution : type_of% @OMA.S_mo_342399.main := by
  intro R _ C D _ _ _ _ _ _ F G _ adj
  exact ⟨fun {X Y} f r => (adj.homEquiv _ _).symm.injective
    (by simp [Adjunction.homEquiv_counit])⟩
