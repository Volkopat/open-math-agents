import OMAStatements.S_oeis_a307740

-- Problem: A307740: Numbers k such that k divides lcm(tau(k), sigma(k)).
-- Upstream: formal-conjectures statements/oeis-a307740.lean:0 (declaration OMA.S_oeis_a307740.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: sigma(k) divides lcm(tau(k), sigma(k)), so k | sigma(k) gives k | lcm(tau(k), sigma(k)).

open OMA.S_oeis_a307740 in
theorem OMA.solution : type_of% @OMA.S_oeis_a307740.main := by
  intro k _ hdiv
  exact Nat.dvd_trans hdiv (Nat.dvd_lcm_right (tau k) (sigma k))
