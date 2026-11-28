import OMAStatements.S_mo_451681
import Mathlib

-- Problem: mo-451681, the image of an open subset of a real-analytic manifold under a
-- real-analytic map is a measurable set.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Only continuity is needed. A second countable manifold is locally compact, so an open
-- subset U is sigma-compact. Its continuous image is then a countable union of compact sets,
-- which are closed in the Hausdorff space N, hence Borel.

open scoped Manifold ContDiff in
theorem OMA.solution : type_of% @OMA.S_mo_451681.main := by
  intro E E' _ _ _ _ _ _ M N _ _ _ _ _ _ _ _ _ _ _ _ f hf U hU
  have hcont : Continuous f := hf.continuous
  have hlc : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  have hUlc : LocallyCompactSpace U := hU.locallyCompactSpace
  have hUsc : SigmaCompactSpace U := inferInstance
  have hUs : IsSigmaCompact U := isSigmaCompact_iff_sigmaCompactSpace.mpr hUsc
  have himg : IsSigmaCompact (f '' U) := hUs.image hcont
  obtain ⟨K, hK, hKU⟩ := himg
  rw [← hKU]
  exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)
