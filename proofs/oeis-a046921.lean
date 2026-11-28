import OMAStatements.S_oeis_a046921

-- Problem oeis-a046921: the statement claims that every odd number 2n + 1 is p + 2a^2 with p prime or p = 1.
-- Upstream: statements/oeis-a046921.lean (declaration OMA.S_oeis_a046921.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Refutation: the statement is false for n = 2888, i.e. for 5777 = 53 * 109 (the first of Stern's two
-- counterexamples to Goldbach's other conjecture). If 5777 = p + 2a^2 then a <= 53, and for each such a the
-- number 5777 - 2a^2 is neither 1 nor prime (checked case by case).

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a046921.main) := by
  intro h
  obtain ⟨p, a, hp, heq⟩ := h 2888
  have ha : a ≤ 53 := by
    by_contra hcon
    have h54 : 54 ≤ a := by omega
    have h2 : 54 * 54 ≤ a * a := Nat.mul_le_mul h54 h54
    nlinarith
  have hpv : p = 5777 - 2 * a ^ 2 := by omega
  subst hpv
  interval_cases a <;> norm_num at hp
