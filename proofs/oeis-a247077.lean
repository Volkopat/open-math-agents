import OMAStatements.S_oeis_a247077

-- Problem: A247077: Composite numbers for which the harmonic mean of proper divisors is an integer.
-- Upstream: formal-conjectures statements/oeis-a247077.lean:0 (declaration OMA.S_oeis_a247077.main)
-- Credit: @Pampasgras (the owner of the agent is credited as the solver)
-- Refutation: k = 488966073874915261 = 29 * 31 * 967 * 137197 * 4099661 is a term that is not of
-- the form m * (sigma(m) - 1) with sigma(m) - 1 prime.

lemma OMA.A247077.sum_inv_divisors (k : ℕ) (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, (d : ℚ)⁻¹ = (ArithmeticFunction.sigma 1 k : ℚ) / k := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  rw [ArithmeticFunction.sigma_one_apply, ← Nat.sum_div_divisors k (fun d => d), Nat.cast_sum,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd' := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℚ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hd
    exact_mod_cast this.ne'
  rw [Nat.cast_div hd' hd0]
  field_simp

lemma OMA.A247077.sum_inv_properDivisors (k : ℕ) (hk : k ≠ 0) :
    ∑ d ∈ k.properDivisors, (d : ℚ)⁻¹ = ((ArithmeticFunction.sigma 1 k : ℚ) - 1) / k := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  have h := OMA.A247077.sum_inv_divisors k hk
  rw [← Nat.insert_self_properDivisors hk, Finset.sum_insert Nat.self_notMem_properDivisors] at h
  rw [sub_div, ← h, one_div]
  ring

lemma OMA.A247077.card_properDivisors_eq (k : ℕ) (hk : k ≠ 0) :
    k.properDivisors.card = k.divisors.card - 1 := by
  rw [← Nat.insert_self_properDivisors hk, Finset.card_insert_of_notMem Nat.self_notMem_properDivisors]
  simp

lemma OMA.A247077.one_lt_sigma (k : ℕ) (hk : 1 < k) : k + 1 ≤ ArithmeticFunction.sigma 1 k := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have h1 : 1 ∈ k.properDivisors := by simp [Nat.mem_properDivisors, hk]
  have h2 : (1 : ℕ) ≤ ∑ i ∈ k.properDivisors, i :=
    Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) h1
  omega

/-- The harmonic mean of the proper divisors, in closed form. -/
lemma OMA.A247077.properHarmonicMean_eq (k : ℕ) (hk : 1 < k) :
    OMA.S_oeis_a247077.properHarmonicMean k =
      ((k * (k.divisors.card - 1) : ℕ) : ℚ) / ((ArithmeticFunction.sigma 1 k - 1 : ℕ) : ℚ) := by
  have hk0 : k ≠ 0 := by omega
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk0
  have hs := OMA.A247077.one_lt_sigma k hk
  have hs' : ((ArithmeticFunction.sigma 1 k - 1 : ℕ) : ℚ) = (ArithmeticFunction.sigma 1 k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hs0 : (ArithmeticFunction.sigma 1 k : ℚ) - 1 ≠ 0 := by
    rw [← hs']; exact_mod_cast (by omega : ArithmeticFunction.sigma 1 k - 1 ≠ 0)
  unfold OMA.S_oeis_a247077.properHarmonicMean
  rw [OMA.A247077.sum_inv_properDivisors k hk0, OMA.A247077.card_properDivisors_eq k hk0, hs', Nat.cast_mul]
  field_simp

lemma OMA.A247077.rat_div_int_iff (a b : ℕ) (hb : b ≠ 0) : (∃ z : ℤ, (a : ℚ) / (b : ℚ) = z) ↔ b ∣ a := by
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  constructor
  · rintro ⟨z, hz⟩
    rw [div_eq_iff hb'] at hz
    have h2 : (a : ℤ) = z * (b : ℤ) := by exact_mod_cast hz
    have h3 : (b : ℤ) ∣ (a : ℤ) := ⟨z, by rw [h2]; ring⟩
    exact_mod_cast h3
  · rintro ⟨c, rfl⟩
    refine ⟨(c : ℤ), ?_⟩
    rw [div_eq_iff hb']
    push_cast
    ring

/-- Suteu's criterion: for `k > 1` the harmonic mean of the proper divisors is an integer iff
`sigma(k) - 1` divides `k * (tau(k) - 1)`. -/
lemma OMA.A247077.hm_int_iff (k : ℕ) (hk : 1 < k) :
    (∃ z : ℤ, OMA.S_oeis_a247077.properHarmonicMean k = z) ↔
      (ArithmeticFunction.sigma 1 k - 1) ∣ k * (k.divisors.card - 1) := by
  have hs := OMA.A247077.one_lt_sigma k hk
  rw [OMA.A247077.properHarmonicMean_eq k hk]
  exact OMA.A247077.rat_div_int_iff _ _ (by omega)


lemma OMA.A247077.sigma_prime_mul (p n : ℕ) (hp : p.Prime) (hn : ¬ p ∣ n) :
    ArithmeticFunction.sigma 1 (p * n) = (p + 1) * ArithmeticFunction.sigma 1 n := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)]
  congr 1
  have h := ArithmeticFunction.sigma_one_apply_prime_pow (p := p) (i := 1) hp
  rw [pow_one] at h
  rw [h]
  simp [Finset.sum_range_succ]
  ring

lemma OMA.A247077.card_divisors_prime_mul (p n : ℕ) (hp : p.Prime) (hn : ¬ p ∣ n) :
    (p * n).divisors.card = 2 * n.divisors.card := by
  rw [Nat.Coprime.card_divisors_mul ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)]
  congr 1
  rw [hp.divisors]
  exact Finset.card_pair hp.one_lt.ne

/-- Counterexample: k = 29 * 31 * 967 * 137197 * 4099661 = 488966073874915261. Its 31 proper divisors
have harmonic mean 29, but k is not m * (sigma(m) - 1) with sigma(m) - 1 prime: such a prime p divides
k, so p <= 4099661, and m <= sigma(m) - 1 = p gives k = m * p <= 4099661 ^ 2 < k. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a247077.main) := by
  intro h
  have h29 : Nat.Prime 29 := by norm_num
  have h31 : Nat.Prime 31 := by norm_num
  have h967 : Nat.Prime 967 := by norm_num
  have h137197 : Nat.Prime 137197 := by norm_num
  have h4099661 : Nat.Prime 4099661 := by norm_num
  have hs5 : ArithmeticFunction.sigma 1 4099661 = 4099662 := by
    have h1 := OMA.A247077.sigma_prime_mul 4099661 1 h4099661 (by norm_num)
    simpa using h1
  have hc5 : (4099661 : ℕ).divisors.card = 2 := by
    rw [h4099661.divisors]
    exact Finset.card_pair (by norm_num)
  have hsig : ArithmeticFunction.sigma 1 (29 * (31 * (967 * (137197 * 4099661)))) =
      522687872073185280 := by
    rw [OMA.A247077.sigma_prime_mul 29 _ h29 (by norm_num),
      OMA.A247077.sigma_prime_mul 31 _ h31 (by norm_num),
      OMA.A247077.sigma_prime_mul 967 _ h967 (by norm_num),
      OMA.A247077.sigma_prime_mul 137197 _ h137197 (by norm_num), hs5]
  have hcard : (29 * (31 * (967 * (137197 * 4099661)))).divisors.card = 32 := by
    rw [OMA.A247077.card_divisors_prime_mul 29 _ h29 (by norm_num),
      OMA.A247077.card_divisors_prime_mul 31 _ h31 (by norm_num),
      OMA.A247077.card_divisors_prime_mul 967 _ h967 (by norm_num),
      OMA.A247077.card_divisors_prime_mul 137197 _ h137197 (by norm_num), hc5]
  have hint : ∃ z : ℤ,
      OMA.S_oeis_a247077.properHarmonicMean (29 * (31 * (967 * (137197 * 4099661)))) = z := by
    rw [OMA.A247077.hm_int_iff _ (by norm_num), hsig, hcard]
    exact ⟨29, by norm_num⟩
  obtain ⟨m, hp, hkm⟩ := h (29 * (31 * (967 * (137197 * 4099661)))) (by norm_num)
    (Nat.not_prime_mul (by norm_num) (by norm_num)) hint
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hkm
  have hm1 : m ≠ 1 := by
    rintro rfl
    simp at hp
    exact Nat.not_prime_zero hp
  have hmp : m ≤ ArithmeticFunction.sigma 1 m - 1 := by
    have := OMA.A247077.one_lt_sigma m (by omega)
    omega
  have hdvd : (ArithmeticFunction.sigma 1 m - 1) ∣ 29 * (31 * (967 * (137197 * 4099661))) :=
    Dvd.intro_left m hkm.symm
  have hple : ArithmeticFunction.sigma 1 m - 1 ≤ 4099661 := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h1 | h1
    · exact (Nat.le_of_dvd (by norm_num) h1).trans (by norm_num)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
    rcases (Nat.Prime.dvd_mul hp).1 h2 with h3 | h3
    · exact (Nat.le_of_dvd (by norm_num) h3).trans (by norm_num)
    rcases (Nat.Prime.dvd_mul hp).1 h3 with h4 | h4
    · exact (Nat.le_of_dvd (by norm_num) h4).trans (by norm_num)
    · exact Nat.le_of_dvd (by norm_num) h4
  have hle : m * (ArithmeticFunction.sigma 1 m - 1) ≤ 4099661 * 4099661 :=
    Nat.mul_le_mul (hmp.trans hple) hple
  rw [← hkm] at hle
  norm_num at hle
