import OMAStatements.S_oeis_a234285

-- Problem: A234285: Positive odd numbers n such that sigma(m) - 2m is never equal to n, where sigma(.) is the sum of divisors function A000203. Conjectural.
-- Upstream: formal-conjectures statements/oeis-a234285.lean:0 (declaration OMA.S_oeis_a234285.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: the fourth claim fails for r = 509202 (r + 1 = 509203 is the smallest Riesel number).
-- 2^24 = 1 modulo 5592405 = 3*5*7*13*17*241, and for every residue t of k modulo 24 one of these
-- six primes divides 2^t - 509203, hence divides 2^k - 509203. So a prime q = 2^k - 509203 is
-- one of them, q <= 241, and then 2^18 < q + 509203 = 2^k < 2^19, which is impossible.

open OMA.S_oeis_a234285 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a234285.main) := by
  intro H
  have hev : Even (509202 : ℤ) := even_iff_two_dvd.mpr (by norm_num)
  obtain ⟨k, q, hq, -, hqk⟩ := H.2.2.2.1 509202 hev
  have hq' : q + 509203 = 2 ^ k := by
    have h1 : ((q + 509203 : ℕ) : ℤ) = ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      linarith
    exact_mod_cast h1
  have hmod : 2 ^ k ≡ 2 ^ (k % 24) [MOD 5592405] := by
    have h1 : (2 : ℕ) ^ 24 ≡ 1 [MOD 5592405] := by
      unfold Nat.ModEq
      norm_num
    have h2 := (h1.pow (k / 24)).mul_right (2 ^ (k % 24))
    rw [one_pow, one_mul, ← pow_mul, ← pow_add, Nat.div_add_mod] at h2
    exact h2
  have hdvd : ∀ p : ℕ, p ∣ 5592405 → 2 ^ (k % 24) % p = 509203 % p → p ∣ q := by
    intro p hp hc
    have h := hmod.of_dvd hp
    unfold Nat.ModEq at h
    rw [hc, ← hq'] at h
    have h2 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [Nat.add_sub_cancel] at h2
    exact Nat.dvd_of_mod_eq_zero h2
  have hex : ∃ p : ℕ, 2 ≤ p ∧ p ≤ 241 ∧ p ∣ 5592405 ∧ 2 ^ (k % 24) % p = 509203 % p := by
    obtain ⟨t, ht⟩ : ∃ t, t = k % 24 := ⟨_, rfl⟩
    have ht24 : t < 24 := by omega
    rw [← ht]
    interval_cases t
    all_goals first | (refine ⟨3, ?_⟩; decide) | (refine ⟨5, ?_⟩; decide) | (refine ⟨7, ?_⟩; decide) | (refine ⟨13, ?_⟩; decide) | (refine ⟨17, ?_⟩; decide) | (refine ⟨241, ?_⟩; decide)
  obtain ⟨p, hp2, hp241, hpN, hc⟩ := hex
  have hpq := hdvd p hpN hc
  have hqle : q ≤ 241 := by
    rcases hq.eq_one_or_self_of_dvd p hpq with h1 | h1 <;> omega
  have hq2 := hq.two_le
  obtain ⟨X, hX⟩ : ∃ X, 2 ^ k = X := ⟨_, rfl⟩
  rcases Nat.lt_or_ge k 19 with hk | hk
  · have h1 : 2 ^ k ≤ 2 ^ 18 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (2 : ℕ) ^ 18 = 262144 := by norm_num
    rw [hX, h2] at h1
    rw [hX] at hq'
    omega
  · have h1 : 2 ^ 19 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    have h2 : (2 : ℕ) ^ 19 = 524288 := by norm_num
    rw [hX, h2] at h1
    rw [hX] at hq'
    omega
