import OMAStatements.S_oeis_a135954

-- Problem: A135954: Nonprime Fibonacci numbers with prime indices (A050937) that have exactly 3 prime factors.
-- Upstream: formal-conjectures statements/oeis-a135954.lean:0 (declaration OMA.S_oeis_a135954.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: p = 2 gives F(2) = 1, which has no prime factor. For odd p = 2m + 1,
-- F(p) = F(m+1)^2 + F(m)^2 with F(m+1) and F(m) coprime, so -1 is a square modulo F(p), hence
-- modulo every divisor q of F(p), and then q is a sum of two squares.

open OMA.S_oeis_a135954 in
theorem OMA.solution : type_of% @OMA.S_oeis_a135954.main := by
  intro n hn q hq
  obtain ⟨p, hp, rfl, -, -⟩ := hn
  have hq' : q ∣ Nat.fib p := Nat.dvd_of_mem_primeFactors hq
  rcases hp.eq_two_or_odd' with rfl | ⟨m, rfl⟩
  · rw [Nat.fib_two, Nat.primeFactors_one] at hq
    exact absurd hq (Finset.notMem_empty q)
  · have hsq : IsSquare (-1 : ZMod (Nat.fib (2 * m + 1))) :=
      ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime (Nat.fib_two_mul_add_one m)
        (Nat.fib_coprime_fib_succ m).symm
    exact Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hq' hsq)
