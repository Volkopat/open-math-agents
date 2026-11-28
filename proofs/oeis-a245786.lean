import OMAStatements.S_oeis_a245786

-- Problem: A245786: Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer.
-- Upstream: formal-conjectures statements/oeis-a245786.lean:0 (declaration OMA.S_oeis_a245786.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 275890944 = 2^8*3*7*19*37*73 is a term of A245786 (a(7) of its data): tau(n) = 288,
-- sigma(n) = 919636480 and n/288 + 919636480/n = 957958. But gcd(sigma(n), n) = 91963648, while
-- m = 142990848 = 2^9*3^2*7*11*13*31 < n has sigma(m) = 571963392 = 4*m, so gcd(sigma(m), m) = m
-- is larger; hence n is not a term of A216793. sigma and tau are computed by multiplicativity.

namespace D1A245786

open OMA.S_oeis_a245786

theorem sig_mul {a b : ℕ} (h : Nat.Coprime a b) : sigma (a * b) = sigma a * sigma b := by
  unfold sigma
  exact Nat.Coprime.sum_divisors_mul h

theorem sig_pp {p k : ℕ} (hp : p.Prime) : sigma (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  unfold sigma
  exact Nat.sum_divisors_prime_pow hp

theorem sig_prime {p : ℕ} (hp : p.Prime) : sigma p = p + 1 := by
  unfold sigma
  rw [Nat.Prime.sum_divisors hp]

theorem tau_mul {a b : ℕ} (h : Nat.Coprime a b) : tau (a * b) = tau a * tau b := by
  unfold tau
  exact Nat.Coprime.card_divisors_mul h

theorem tau_pp {p k : ℕ} (hp : p.Prime) : tau (p ^ k) = k + 1 := by
  unfold tau
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

theorem tau_prime {p : ℕ} (hp : p.Prime) : tau p = 2 := by
  unfold tau
  rw [Nat.Prime.divisors hp, Finset.card_pair (Nat.Prime.one_lt hp).ne]

theorem p3 : Nat.Prime 3 := by norm_num
theorem p7 : Nat.Prime 7 := by norm_num
theorem p11 : Nat.Prime 11 := by norm_num
theorem p13 : Nat.Prime 13 := by norm_num
theorem p19 : Nat.Prime 19 := by norm_num
theorem p31 : Nat.Prime 31 := by norm_num
theorem p37 : Nat.Prime 37 := by norm_num
theorem p73 : Nat.Prime 73 := by norm_num

theorem c1 : Nat.Coprime (2 ^ 8 * 3 * 7 * 19 * 37) 73 := by decide
theorem c2 : Nat.Coprime (2 ^ 8 * 3 * 7 * 19) 37 := by decide
theorem c3 : Nat.Coprime (2 ^ 8 * 3 * 7) 19 := by decide
theorem c4 : Nat.Coprime (2 ^ 8 * 3) 7 := by decide
theorem c5 : Nat.Coprime (2 ^ 8) 3 := by decide

theorem fn : (275890944 : ℕ) = 2 ^ 8 * 3 * 7 * 19 * 37 * 73 := by norm_num

theorem sigma_n : sigma 275890944 = 919636480 := by
  rw [fn, sig_mul c1, sig_mul c2, sig_mul c3, sig_mul c4, sig_mul c5, sig_pp Nat.prime_two,
    sig_prime p3, sig_prime p7, sig_prime p19, sig_prime p37, sig_prime p73]
  norm_num [Finset.sum_range_succ]

theorem tau_n : tau 275890944 = 288 := by
  have h : tau 275890944 = (8 + 1) * 2 * 2 * 2 * 2 * 2 := by
    rw [fn, tau_mul c1, tau_mul c2, tau_mul c3, tau_mul c4, tau_mul c5, tau_pp Nat.prime_two,
      tau_prime p3, tau_prime p7, tau_prime p19, tau_prime p37, tau_prime p73]
  exact h.trans (by norm_num)

theorem d1 : Nat.Coprime (2 ^ 9 * 3 ^ 2 * 7 * 11 * 13) 31 := by decide
theorem d2 : Nat.Coprime (2 ^ 9 * 3 ^ 2 * 7 * 11) 13 := by decide
theorem d3 : Nat.Coprime (2 ^ 9 * 3 ^ 2 * 7) 11 := by decide
theorem d4 : Nat.Coprime (2 ^ 9 * 3 ^ 2) 7 := by decide
theorem d5 : Nat.Coprime (2 ^ 9) (3 ^ 2) := by decide

theorem fm : (142990848 : ℕ) = 2 ^ 9 * 3 ^ 2 * 7 * 11 * 13 * 31 := by norm_num

theorem sigma_m : sigma 142990848 = 571963392 := by
  rw [fm, sig_mul d1, sig_mul d2, sig_mul d3, sig_mul d4, sig_mul d5, sig_pp Nat.prime_two,
    sig_pp p3, sig_prime p7, sig_prime p11, sig_prime p13, sig_prime p31]
  norm_num [Finset.sum_range_succ]

end D1A245786

open OMA.S_oeis_a245786 D1A245786 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a245786.main) := by
  intro H
  have hA : InA245786 275890944 := by
    refine ⟨by norm_num, 957958, ?_⟩
    rw [sigma_n, tau_n]
    norm_num
  obtain ⟨-, hrec⟩ := H 275890944 hA
  have h := hrec 142990848 (by norm_num) (by norm_num)
  rw [sigma_m, sigma_n] at h
  norm_num at h
