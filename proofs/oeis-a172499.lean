import OMAStatements.S_oeis_a172499

-- Problem: A172499: a(n) = numerator of fraction whose decimal representation is
-- (n).(1)(2)(3)...(n-1)(n)... with repeating part (1)(2)(3)...(n-1)(n).
-- Upstream: formal-conjectures statements/oeis-a172499.lean:0 (declaration OMA.S_oeis_a172499.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: x(n) = n + q(n) with q(n) = cat(n)/(10^len(n) - 1), and adding a natural number to a
-- rational number does not change its reduced denominator (Rat.natCast_add_den). So the
-- denominators of the fractions of A172499 equal A172498 for every n, and no n is a witness.

open OMA.S_oeis_a172499 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a172499.main) := by
  rintro ⟨n, -, h⟩
  apply h
  unfold x A172498
  exact Rat.natCast_add_den n _
