import OMAStatements.S_mo_365623
import Mathlib

-- Problem mo-365623: the statement claims that for every odd i some set S of interior indices 1 <= k < i has
-- sum_{k in S} (-1)^k C(i, k) = 1.
-- Upstream: statements/mo-365623.lean (declaration OMA.S_mo_365623.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: it fails for i = 1. There are no indices k with 1 <= k < 1, so S must be empty and the sum is 0,
-- not 1.

open OMA.S_mo_365623

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365623.main) := by
  intro h
  obtain ⟨S, hS, hsum⟩ := h 1 (by decide)
  have hS0 : S = ∅ := by
    rw [Finset.Ico_self] at hS
    exact Finset.subset_empty.mp hS
  rw [hS0] at hsum
  unfold signedSum at hsum
  simp at hsum
