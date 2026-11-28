import OMAStatements.S_mo_26856
import Mathlib

-- Problem mo-26856: under the hypotheses of the statement (a Noetherian local ring R, a finite module M, an
-- M-regular element x of the maximal ideal, an associated prime p of M and a prime q containing p), if q is an
-- associated prime of M / x M then q lies in the support of M / x M.
-- Upstream: statements/mo-26856.lean (declaration OMA.S_mo_26856.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: the conclusion holds for any module N in place of M / x M: an associated prime q of N is the radical
-- of the annihilator of some element n of N, so the annihilator of n is contained in q, and a prime containing
-- the annihilator of an element lies in the support. The other hypotheses are not needed.

open OMA.S_mo_26856

theorem OMA.solution : type_of% @OMA.S_mo_26856.main := by
  intro R M _ _ _ _ _ _ _ p x _ _ _ q _ hq
  obtain ⟨_, m, hm⟩ := hq
  rw [Module.mem_support_iff_exists_annihilator]
  refine ⟨m, fun r hr => ?_⟩
  rw [hm]
  apply Ideal.le_radical
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  exact (Submodule.mem_annihilator_span_singleton _ _).mp hr
