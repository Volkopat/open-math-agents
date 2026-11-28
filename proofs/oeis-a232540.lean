import OMAStatements.S_oeis_a232540

-- Problem: A232540: Numbers n such that (n(n+1)/2) modulo sigma(n) = 1.
-- Upstream: formal-conjectures statements/oeis-a232540.lean:0 (declaration OMA.S_oeis_a232540.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a semiprime n = p * q with n mod 6 = 4 is even, so one factor is 2 and n = 2 * r
-- with r prime. Since n is not 4, r is odd, and 2r mod 6 = 4 gives r mod 3 = 2, so r = 6s + 5.
-- Then sigma(n) = sigma(2) * sigma(r) = 3 * (r + 1) = 18(s + 1), and
-- n(n+1)/2 = r(2r + 1) = (6s + 5)(12s + 11) = 1 + 18(s + 1)(4s + 3), whose remainder modulo
-- 18(s + 1) is 1.

open OMA.S_oeis_a232540 in
theorem OMA.solution : type_of% @OMA.S_oeis_a232540.main := by
  intro n hn hne
  obtain ⟨⟨p, q, hp, hq, rfl⟩, hmod⟩ := hn
  have hsigp : ∀ x : ℕ, x.Prime → ArithmeticFunction.sigma 1 x = x + 1 := by
    intro x hx
    rw [ArithmeticFunction.sigma_one_apply]
    exact Nat.Prime.sum_divisors hx
  obtain ⟨r, hr, hpq⟩ : ∃ r : ℕ, r.Prime ∧ p * q = 2 * r := by
    have h2 : 2 ∣ p * q := by omega
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
    · have hp2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
      exact ⟨q, hq, by rw [← hp2]⟩
    · have hq2 : 2 = q := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp h
      exact ⟨p, hp, by rw [← hq2, mul_comm]⟩
  rw [hpq] at hmod hne ⊢
  have hodd : r % 2 = 1 := by
    rcases hr.eq_two_or_odd with h | h
    · exfalso
      exact hne (by omega)
    · exact h
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = 6 * s + 5 := ⟨r / 6, by omega⟩
  have hcop : Nat.Coprime 2 (6 * s + 5) := Nat.coprime_two_left.mpr ⟨3 * s + 2, by omega⟩
  have hsig : ArithmeticFunction.sigma 1 (2 * (6 * s + 5)) = (2 + 1) * (6 * s + 5 + 1) := by
    rw [(ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop,
      hsigp 2 Nat.prime_two, hsigp (6 * s + 5) hr]
  have e : 2 * (6 * s + 5) * (2 * (6 * s + 5) + 1) / 2
      = 1 + (2 + 1) * (6 * s + 5 + 1) * (4 * s + 3) :=
    Nat.div_eq_of_eq_mul_left (by norm_num) (by ring)
  refine ⟨by omega, ?_⟩
  rw [hsig, e, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)
