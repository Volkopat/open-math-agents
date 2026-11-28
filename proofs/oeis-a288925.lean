import OMAStatements.S_oeis_a288925

-- Problem: A288925: a(n) = a(n-1) + a(n-2) + 3*a(n-4) - 2*a(n-5) for n >= 5, where a(0) = 2, a(1) = 4, a(2) = 8, a(3) = 13, a(4) = 26.
-- Upstream: formal-conjectures statements/oeis-a288925.lean:0 (declaration OMA.S_oeis_a288925.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: the third iterate is 00011000 -> 1000 0 1 0001 1000 = 10000100011000, which has 14
-- letters (as listed in A288926), while a(3) = 13.

open OMA.S_oeis_a288925 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a288925.main) := by
  intro H
  have h1 : a 3 = 13 := by decide
  have h2 : ((w 3).length : ℤ) = 14 := by decide
  have h := H 3
  rw [h1, h2] at h
  omega
