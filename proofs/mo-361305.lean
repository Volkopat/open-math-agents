import OMAStatements.S_mo_361305
import Mathlib

-- Problem: mo-361305, is C(X, Y) with the compact-open topology a topological group for every
-- topological space X and every topological group Y?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes. Inversion is post-composition with the continuous map y -> y^-1, and post-composition
-- is continuous for the compact-open topology. Multiplication is the pairing
-- (f, g) -> (x -> (f x, g x)) into C(X, Y x Y) followed by post-composition with the
-- multiplication of Y. The pairing is continuous because the compact-open topology is the
-- topology of uniform convergence on compact sets for the right uniformity of Y, and uniform
-- convergence of both components gives uniform convergence of the pair.

open Topology in
theorem OMA.solution : type_of% @OMA.S_mo_361305.main := by
  intro X Y _ _ _ _
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · let _ : UniformSpace Y := IsTopologicalGroup.rightUniformSpace Y
    have hprod : Continuous (fun p : C(X, Y) × C(X, Y) => p.1.prodMk p.2) := by
      rw [continuous_iff_continuousAt]
      rintro ⟨f, g⟩
      rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn,
        nhds_prod_eq]
      exact fun K hK =>
        (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
            Filter.tendsto_id K hK).prodMk
          (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp
            Filter.tendsto_id K hK)
    have hmul := ContinuousMap.continuous_postcomp (X := X)
      (⟨fun p : Y × Y => p.1 * p.2, continuous_mul⟩ : C(Y × Y, Y))
    exact (hmul.comp hprod).congr (fun p => by ext x; rfl)
  · have hinv := ContinuousMap.continuous_postcomp (X := X)
      (⟨fun y : Y => y⁻¹, continuous_inv⟩ : C(Y, Y))
    exact hinv.congr (fun f => by ext x; rfl)
