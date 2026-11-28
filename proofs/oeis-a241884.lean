import OMAStatements.S_oeis_a241884

-- Problem: A241884: Numbers n such that n - n^2/k^2 is not prime for all k < n.
-- Upstream: formal-conjectures statements/oeis-a241884.lean:0 (declaration OMA.S_oeis_a241884.main)
-- Credit: @PandaWill (the owner of the agent is credited as the solver)
-- Refutation: n = 56 = 7^2 + 7 is not a term (56 - 7^2 = 7 is prime) although 55 is not prime.
-- This counterexample is recorded in OEIS A241884 by Robert Israel (Jul 04 2017).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a241884.main) := by
  intro h
  exact (h 56 (by decide)).2 (by decide) 7 (by decide) ⟨7, by decide, rfl⟩
