import OMAStatements.S_oeis_a308707

-- Problem: A308707: a(n) = gcd(n, phi(n) + sigma(n)), where phi is A000010 and sigma is A000203.
-- Upstream: formal-conjectures statements/oeis-a308707.lean:0 (declaration OMA.S_oeis_a308707.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: m = 14 is a counterexample to the second conjecture. 196 = 2^2 * 7^2, so
-- phi(196) = 2 * 42 = 84 and sigma(196) = 7 * 57 = 399, and a(196) = gcd(196, 483) = 7.

open OMA.S_oeis_a308707 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a308707.main) := by
  intro H
  have h196 : (196 : ℕ) = 2 ^ 2 * 7 ^ 2 := by norm_num
  have hcop : Nat.Coprime (2 ^ 2) (7 ^ 2) := by decide
  have e1 := Nat.totient_mul hcop
  rw [Nat.totient_prime_pow Nat.prime_two (show 0 < 2 by norm_num),
    Nat.totient_prime_pow (show Nat.Prime 7 by norm_num) (show 0 < 2 by norm_num)] at e1
  have hphi : Nat.totient 196 = 84 := by
    rw [h196]
    exact e1.trans (by norm_num)
  have e2 := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    ArithmeticFunction.sigma_one_apply_prime_pow (show Nat.Prime 7 by norm_num)] at e2
  have r2 : (∑ k ∈ Finset.range (2 + 1), (2 : ℕ) ^ k) = 7 := by
    norm_num [Finset.sum_range_succ]
  have r7 : (∑ k ∈ Finset.range (2 + 1), (7 : ℕ) ^ k) = 57 := by
    norm_num [Finset.sum_range_succ]
  rw [r2, r7] at e2
  have hsig : ArithmeticFunction.sigma 1 196 = 399 := by
    rw [h196]
    exact e2.trans (by norm_num)
  have e3 : a (14 ^ 2) = Nat.gcd 196 (84 + 399) := by
    unfold a
    rw [show (14 : ℕ) ^ 2 = 196 by norm_num, hphi, hsig]
  have ha : a (14 ^ 2) = 7 := e3.trans (by norm_num)
  have h1 := H.2 14 (by norm_num)
  exact absurd (ha.symm.trans h1) (by norm_num)
