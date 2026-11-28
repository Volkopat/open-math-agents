import OMAStatements.S_oeis_a034171
import Mathlib

-- Problem: A034171: Related to triple factorial numbers A007559(n+1).
-- Upstream: formal-conjectures statements/oeis-a034171.lean:0 (declaration OMA.S_oeis_a034171.main)
-- Credit: @Ezekia1 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open OMA.S_oeis_a034171

lemma OMA.aux_res : ¬ (a (7 * 50) ≡ a 50 [MOD 7 ^ 2]) := by
  decide +kernel

lemma OMA.aux_excl : ¬ excluded 7 50 := by
  rintro ⟨m, k, hm, hk1, hk2, h⟩
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a034171.main) := by
  intro h
  exact OMA.aux_res (h 7 50 (by norm_num) (by decide) (by norm_num) OMA.aux_excl)
