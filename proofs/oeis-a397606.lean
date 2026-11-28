import OMAStatements.S_oeis_a397606

-- Problem: A397606: a(n) = denominator of A069835(n)/2^n.
-- Upstream: formal-conjectures statements/oeis-a397606.lean:0 (declaration OMA.S_oeis_a397606.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A069835(n) is the coefficient of x^n in (4x + (x^2 + 3))^n. With E(j) the 2-adic
-- valuation of binomial(2j,j), one has E(j) + v_2(j!) = j, so E(j + d) <= E(j) + d. For n = 2m the
-- term without a factor 4 is 3^m binomial(2m,m) and every other term has more than E(m) factors 2;
-- for n = 2m+1 the term 4 (2m+1) 3^m binomial(2m,m) dominates in the same way.

open Polynomial OMA.S_oeis_a397606 in
theorem OMA.solution : type_of% @OMA.S_oeis_a397606.main := by
  -- valuations of central binomial coefficients
  have hE : ∀ j : ℕ, padicValNat 2 (Nat.centralBinom j) + padicValNat 2 j.factorial = j := by
    intro j
    have h1 : (2 * j).factorial = Nat.centralBinom j * j.factorial * j.factorial := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      have h := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * j by omega)
      rw [show 2 * j - j = j by omega] at h
      exact h.symm
    have h2 := padicValNat_factorial_mul (p := 2) j
    rw [h1, padicValNat.mul (p := 2)
      (mul_ne_zero (Nat.centralBinom_pos j).ne' (Nat.factorial_ne_zero j))
      (Nat.factorial_ne_zero j), padicValNat.mul (p := 2) (Nat.centralBinom_pos j).ne'
      (Nat.factorial_ne_zero j)] at h2
    omega
  have hfac : ∀ j : ℕ, padicValNat 2 j.factorial ≤ padicValNat 2 (j + 1).factorial := by
    intro j
    rw [Nat.factorial_succ,
      padicValNat.mul (p := 2) (by omega : j + 1 ≠ 0) (Nat.factorial_ne_zero j)]
    omega
  have hEle : ∀ j d : ℕ,
      padicValNat 2 (Nat.centralBinom (j + d)) ≤ padicValNat 2 (Nat.centralBinom j) + d := by
    intro j d
    induction d with
    | zero => simp
    | succ d ih =>
      have h1 := hE (j + d)
      have h2 := hE (j + d + 1)
      have h3 := hfac (j + d)
      rw [show j + (d + 1) = j + d + 1 by ring]
      omega
  have hdvd : ∀ j : ℕ, 2 ^ padicValNat 2 (Nat.centralBinom j) ∣ Nat.centralBinom j :=
    fun j => (padicValNat_dvd_iff (p := 2) _ _).2 (Or.inr le_rfl)
  have hodd : ∀ j : ℕ, ∃ w, Odd w ∧
      Nat.centralBinom j = 2 ^ padicValNat 2 (Nat.centralBinom j) * w := by
    intro j
    have hnd := pow_succ_padicValNat_not_dvd (p := 2) (Nat.centralBinom_pos j).ne'
    obtain ⟨w, hw⟩ := hdvd j
    generalize padicValNat 2 (Nat.centralBinom j) = v at hw hnd ⊢
    refine ⟨w, ?_, hw⟩
    rcases Nat.even_or_odd w with ⟨k, hk⟩ | ho
    · exact (hnd ⟨k, by rw [hw, hk, pow_succ]; ring⟩).elim
    · exact ho
  -- the coefficients of (x^2 + 3)^r
  have hQ : (X ^ 2 + C 3 : ℕ[X]) = expand ℕ 2 (X + C 3) := by
    rw [map_add, expand_X, expand_C]
  have hWe : ∀ j : ℕ,
      ((X ^ 2 + C 3 : ℕ[X]) ^ (2 * j)).coeff (2 * j) = 3 ^ j * Nat.centralBinom j := by
    intro j
    rw [hQ, ← map_pow, coeff_expand two_pos, if_pos (dvd_mul_right 2 j),
      show 2 * j / 2 = j by omega, coeff_X_add_C_pow, show 2 * j - j = j by omega,
      Nat.centralBinom_eq_two_mul_choose, Nat.cast_id]
  have hWo : ∀ j : ℕ, ((X ^ 2 + C 3 : ℕ[X]) ^ (2 * j + 1)).coeff (2 * j + 1) = 0 := by
    intro j
    rw [hQ, ← map_pow, coeff_expand two_pos, if_neg (show ¬ (2 ∣ 2 * j + 1) by omega)]
  -- A069835(n) as a coefficient of (4x + (x^2 + 3))^n
  have hpoly : ∀ n : ℕ, A069835 n = ∑ m ∈ Finset.range (n + 1),
      n.choose m * 4 ^ m * ((X ^ 2 + C 3 : ℕ[X]) ^ (n - m)).coeff (n - m) := by
    intro n
    have e1 : ((X + 1 : ℕ[X]) ^ n * (X + C 3) ^ n).coeff n = A069835 n := by
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      unfold A069835
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      dsimp only
      rw [coeff_X_add_one_pow, coeff_X_add_C_pow, show n - (n - k) = k by omega,
        Nat.choose_symm hk']
      simp only [Nat.cast_id]
      ring
    have e2 : ((X + 1 : ℕ[X]) ^ n * (X + C 3) ^ n) = (C 4 * X + (X ^ 2 + C 3)) ^ n := by
      rw [← mul_pow]
      congr 1
      rw [show (4 : ℕ) = 3 + 1 from rfl, C_add, C_1]
      ring
    rw [← e1, e2, add_pow, finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : m ≤ n := by
      have := Finset.mem_range.mp hm
      omega
    rw [mul_pow, ← C_pow, ← C_eq_natCast, coeff_mul_C, mul_assoc, coeff_C_mul,
      coeff_X_pow_mul', if_pos hm', Nat.cast_id]
    ring
  have hsplit : ∀ v R u : ℕ, 2 ^ (v + 1) ∣ R → Odd u → ∃ w, Odd w ∧ R + 2 ^ v * u = 2 ^ v * w := by
    intro v R u hR hu
    obtain ⟨r, rfl⟩ := hR
    exact ⟨2 * r + u, (even_two_mul r).add_odd hu, by ring⟩
  have h3odd : Odd (3 : ℕ) := ⟨1, rfl⟩
  -- even indices
  have hEven : ∀ M : ℕ, ∃ w, Odd w ∧
      A069835 (2 * M) = 2 ^ padicValNat 2 (Nat.centralBinom M) * w := by
    intro M
    obtain ⟨u, hu, hcb⟩ := hodd M
    have hR : 2 ^ (padicValNat 2 (Nat.centralBinom M) + 1) ∣ ∑ m ∈ Finset.range (2 * M),
        (2 * M).choose (m + 1) * 4 ^ (m + 1) *
          ((X ^ 2 + C 3 : ℕ[X]) ^ (2 * M - (m + 1))).coeff (2 * M - (m + 1)) := by
      apply Finset.dvd_sum
      intro m hm
      have hm' : m < 2 * M := Finset.mem_range.mp hm
      obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (2 * M - (m + 1))
      · rw [hj, hWe j]
        have h1 := hEle j (M - j)
        rw [show j + (M - j) = M by omega] at h1
        obtain ⟨c, hc⟩ := hdvd j
        generalize padicValNat 2 (Nat.centralBinom j) = ej at h1 hc
        rw [hc]
        have h3 : 2 ^ (padicValNat 2 (Nat.centralBinom M) + 1) ∣ 4 ^ (m + 1) * 2 ^ ej := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          exact pow_dvd_pow 2 (by omega)
        exact h3.trans ⟨(2 * M).choose (m + 1) * 3 ^ j * c, by ring⟩
      · rw [hj, hWo j, mul_zero]
        exact dvd_zero _
    have hsum := hpoly (2 * M)
    rw [Finset.sum_range_succ', Nat.choose_zero_right, pow_zero, Nat.sub_zero, hWe M, hcb] at hsum
    obtain ⟨w, hw, hwe⟩ := hsplit _ _ (3 ^ M * u) hR (h3odd.pow.mul hu)
    refine ⟨w, hw, ?_⟩
    rw [hsum, ← hwe]
    ring
  -- odd indices
  have hOdd : ∀ M : ℕ, ∃ w, Odd w ∧
      A069835 (2 * M + 1) = 2 ^ (padicValNat 2 (Nat.centralBinom M) + 2) * w := by
    intro M
    obtain ⟨u, hu, hcb⟩ := hodd M
    have hR : 2 ^ (padicValNat 2 (Nat.centralBinom M) + 2 + 1) ∣ ∑ m ∈ Finset.range (2 * M),
        (2 * M + 1).choose (m + 1 + 1) * 4 ^ (m + 1 + 1) *
          ((X ^ 2 + C 3 : ℕ[X]) ^ (2 * M + 1 - (m + 1 + 1))).coeff (2 * M + 1 - (m + 1 + 1)) := by
      apply Finset.dvd_sum
      intro m hm
      have hm' : m < 2 * M := Finset.mem_range.mp hm
      obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (2 * M + 1 - (m + 1 + 1))
      · rw [hj, hWe j]
        have h1 := hEle j (M - j)
        rw [show j + (M - j) = M by omega] at h1
        obtain ⟨c, hc⟩ := hdvd j
        generalize padicValNat 2 (Nat.centralBinom j) = ej at h1 hc
        rw [hc]
        have h3 : 2 ^ (padicValNat 2 (Nat.centralBinom M) + 2 + 1) ∣
            4 ^ (m + 1 + 1) * 2 ^ ej := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          exact pow_dvd_pow 2 (by omega)
        exact h3.trans ⟨(2 * M + 1).choose (m + 1 + 1) * 3 ^ j * c, by ring⟩
      · rw [hj, hWo j, mul_zero]
        exact dvd_zero _
    have hsum := hpoly (2 * M + 1)
    rw [Finset.sum_range_succ', Finset.sum_range_succ', zero_add, Nat.choose_one_right, pow_one,
      show 2 * M + 1 - 1 = 2 * M by omega, hWe M, hcb, Nat.sub_zero, hWo M, mul_zero,
      add_zero] at hsum
    obtain ⟨w, hw, hwe⟩ := hsplit _ _ ((2 * M + 1) * (3 ^ M * u)) hR
      ((odd_two_mul_add_one M).mul (h3odd.pow.mul hu))
    refine ⟨w, hw, ?_⟩
    rw [hsum, ← hwe]
    ring
  -- denominators
  have hdenc : ∀ w b : ℕ, 0 < b → Nat.Coprime w b → ((w : ℚ) / (b : ℚ)).den = b := by
    intro w b hb hc
    have h := Rat.den_div_eq_of_coprime (a := (w : ℤ)) (b := (b : ℤ)) (by exact_mod_cast hb)
      (by simpa using hc)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    exact_mod_cast h
  have hden : ∀ v w n : ℕ, Odd w → (((2 ^ v * w : ℕ) : ℚ) / 2 ^ n).den = 2 ^ (n - v) := by
    intro v w n hw
    rcases le_total v n with h | h
    · have hn : (2 : ℚ) ^ n = 2 ^ v * 2 ^ (n - v) := by
        rw [← pow_add]
        congr 1
        omega
      have e : (((2 ^ v * w : ℕ) : ℚ) / 2 ^ n) = (w : ℚ) / ((2 ^ (n - v) : ℕ) : ℚ) := by
        push_cast
        rw [hn, mul_div_mul_left _ _ (pow_ne_zero v two_ne_zero)]
      rw [e]
      exact hdenc w _ (by positivity) (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hw))
    · rw [show n - v = 0 by omega, pow_zero, show (2 : ℚ) ^ n = ((2 ^ n : ℕ) : ℚ) by norm_num]
      exact (Rat.den_div_natCast_eq_one_iff _ _ (by positivity)).2
        (Dvd.dvd.mul_right (pow_dvd_pow 2 h) w)
  -- the conjecture
  intro M
  obtain ⟨w, hw, hT⟩ := hEven M
  obtain ⟨w', hw', hT'⟩ := hOdd M
  have hEM := hE M
  have ha0 : a (2 * M) = 2 ^ (2 * M - padicValNat 2 (Nat.centralBinom M)) := by
    unfold a
    rw [hT]
    exact hden _ _ _ hw
  have ha1 : a (2 * M + 1) = 2 ^ (2 * M + 1 - (padicValNat 2 (Nat.centralBinom M) + 2)) := by
    unfold a
    rw [hT']
    exact hden _ _ _ hw'
  have hA : A005187 M = M + padicValNat 2 M.factorial := by
    unfold A005187
    rw [padicValNat_factorial_mul (p := 2)]
    ring
  refine ⟨?_, ?_⟩
  · rw [ha0, hA]
    congr 1
    omega
  · rw [ha1, ha0]
    rcases Nat.eq_zero_or_pos M with hM | hM
    · subst hM
      have h0 : padicValNat 2 (Nat.centralBinom 0) = 0 := by omega
      rw [h0, show 2 * 0 + 1 - (0 + 2) = 0 by norm_num, pow_zero, Nat.cast_one,
        max_eq_left (show (1 : ℚ) / 2 ≤ 1 by norm_num)]
    · obtain ⟨k, hk⟩ : ∃ k, 2 * M - padicValNat 2 (Nat.centralBinom M) = k + 1 :=
        ⟨2 * M - padicValNat 2 (Nat.centralBinom M) - 1, by omega⟩
      have hk' : 2 * M + 1 - (padicValNat 2 (Nat.centralBinom M) + 2) = k := by omega
      rw [hk, hk', pow_succ]
      push_cast
      rw [mul_div_cancel_right₀ _ two_ne_zero]
      exact (max_eq_right (one_le_pow₀ (by norm_num))).symm
