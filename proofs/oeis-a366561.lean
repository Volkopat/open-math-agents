import OMAStatements.S_oeis_a366561

-- Problem oeis-a366561: T(n, k) counts the pairs (x, y) with 1 <= x, y <= n and gcd(x^2 - y^2, n) = k.
-- The statement claims that for 1 <= k <= n, T(n, k) = 0 exactly when k does not divide n.
-- Upstream: statements/oeis-a366561.lean (declaration OMA.S_oeis_a366561.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- The statement is false. A difference of two squares is never 2 modulo 4, so gcd(x^2 - y^2, 4) is 1 or 4
-- and never 2: T(4, 2) = 0 although 2 divides 4. The count is finite and is evaluated by the kernel.

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a366561.main) := by
  intro h
  have h0 : OMA.S_oeis_a366561.T 4 2 = 0 := by decide +kernel
  exact (h 4 2 (by norm_num) (by norm_num)).mp h0 (by norm_num)
