import FormalConjectures.ErdosProblems.«724»

/-!
Beth's lower bound follows from the finite-field, product, and truncated
transversal-design constructions together with a dimension-two interval sieve
at exponent 64/15. The first sieve call produces two consecutive orders
of size O(z^(79/15)); the second uses an interval of length comparable to
n/z^(158/15). The sum of the exponents is 74/5.

The construction and arithmetic follow the Wilson reduction by @green-notes.
-/

-- Reduction Erdos724.erdos_724.variants.beth.R1 of Erdős Problem 724
-- Credit: @PianothShaveck

namespace OMA.R_Erdos724_erdos_724_variants_beth_R1

open Filter Erdos724

def H1 : Prop :=
  ∀ p k : ℕ, p.Prime → 1 ≤ k → p ^ k - 1 ≤ Erdos724.maxMOLS (p ^ k)

def H2 : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    min (Erdos724.maxMOLS a) (Erdos724.maxMOLS b) ≤ Erdos724.maxMOLS (a * b)

def H3 : Prop :=
  ∀ m t u s : ℕ, 1 ≤ m → 1 ≤ u → u ≤ t →
    s ≤ Erdos724.maxMOLS m → s ≤ Erdos724.maxMOLS (m + 1) →
    s + 1 ≤ Erdos724.maxMOLS t → s ≤ Erdos724.maxMOLS u →
    s ≤ Erdos724.maxMOLS (m * t + u)

def H4 : Prop :=
  ∃ C : ℝ, 3 ≤ C ∧ ∀ (z : ℝ) (X L : ℕ) (a b : ℤ),
    C ≤ z → C * z ^ ((64 : ℝ) / 15) ≤ (L : ℝ) →
    (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ ((p : ℤ) ∣ a)) →
    ∃ x ∈ Finset.Ico X (X + L),
      ¬ 2 ∣ x ∧
      ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z →
        ¬ ((p : ℤ) ∣ (x : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x : ℤ) + b)

section Helpers

private lemma macneish (h1 : H1) (h2 : H2) :
    ∀ n : ℕ, 2 ≤ n → ∀ s : ℕ,
      (∀ p ∈ n.primeFactors, s + 1 ≤ p ^ (n.factorization p)) → s ≤ Erdos724.maxMOLS n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s hs
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
    have hk : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
    let q := p ^ (n.factorization p)
    have hqn : q ∣ n := Nat.ordProj_dvd n p
    let r := n / q
    have hqr : q * r = n := Nat.mul_div_cancel' hqn
    have hq_pos : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
    have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero fun hr0 => by
      rw [hr0, mul_zero] at hqr
      omega
    have hq_ge : s ≤ Erdos724.maxMOLS q := by
      have h1q := h1 p (n.factorization p) hp hk
      have hsq : s + 1 ≤ q := hs p hpmem
      dsimp only [q]
      omega
    by_cases hr1 : r = 1
    · rw [← hqr, hr1, mul_one]
      exact hq_ge
    · have hr2 : 2 ≤ r := by omega
      have hq2 : 2 ≤ q := by
        have hp2 : 2 ≤ p := hp.two_le
        have hpow : p ≤ p ^ (n.factorization p) := by
          simpa using Nat.pow_le_pow_right hp.pos hk
        simpa [q] using hp2.trans hpow
      have hrlt : r < n := by
        calc r = 1 * r := (one_mul r).symm
          _ < q * r := Nat.mul_lt_mul_of_pos_right (by omega) hr_pos
          _ = n := hqr
      have hpnr : ¬ p ∣ r := Nat.not_dvd_ordCompl hp (by omega)
      have hsr : s ≤ Erdos724.maxMOLS r := by
        refine ih r hrlt hr2 s fun p' hp' => ?_
        have hp'_prime : p'.Prime := (Nat.mem_primeFactors.mp hp').1
        have hp'_dvd_r : p' ∣ r := (Nat.mem_primeFactors.mp hp').2.1
        have hp'_ne : p' ≠ p := by
          rintro rfl
          exact hpnr hp'_dvd_r
        have hp'_dvd_n : p' ∣ n := hp'_dvd_r.trans ⟨q, by rw [← hqr, mul_comm]⟩
        have hp'_mem : p' ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp'_prime, hp'_dvd_n, by omega⟩
        have hq_not : ¬ p' ∣ q := fun hd => by
          have := (Nat.dvd_prime hp).mp (hp'_prime.dvd_of_dvd_pow hd)
          rcases this with h1' | hpeq
          · exact hp'_prime.ne_one h1'
          · exact hp'_ne hpeq
        have hfac : r.factorization p' = n.factorization p' := by
          have h := congrArg (fun x => Nat.factorization x p') hqr.symm
          rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd hq_not, zero_add] at h
          exact h.symm
        rw [hfac]
        exact hs p' hp'_mem
      calc s ≤ min (Erdos724.maxMOLS q) (Erdos724.maxMOLS r) := le_min hq_ge hsr
        _ ≤ Erdos724.maxMOLS (q * r) := h2 q r hq_pos hr_pos
        _ = Erdos724.maxMOLS n := by rw [hqr]

private lemma exists_pow_two_near {z : ℝ} (hz : 3 ≤ z) :
    ∃ k : ℕ, 2 ≤ k ∧ z < ((2 ^ k : ℕ) : ℝ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 2 * z := by
  let f : ℕ := ⌊z⌋₊
  have hf3 : 3 ≤ f := Nat.le_floor (by exact_mod_cast hz)
  have hlog : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by omega) (by omega)
  refine ⟨Nat.log 2 f + 1, by omega, ?_, ?_⟩
  · have hlt : f < 2 ^ (Nat.log 2 f + 1) := Nat.lt_pow_succ_log_self (by omega) f
    have hle : f + 1 ≤ 2 ^ (Nat.log 2 f + 1) := hlt
    have hz1 : z < (f : ℝ) + 1 := Nat.lt_floor_add_one z
    have hleR : (f : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    exact hz1.trans_le hleR
  · have hpow : 2 ^ Nat.log 2 f ≤ f := Nat.pow_log_le_self 2 (by omega)
    have hpow2 : 2 ^ (Nat.log 2 f + 1) ≤ 2 * f := by
      rw [pow_succ']
      omega
    have hfR : (f : ℝ) ≤ z := Nat.floor_le (by linarith)
    have hpowR : ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hpow2
    linarith

end Helpers

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos724.erdos_724.variants.beth := by
  intro h1 h2 h3 h4
  obtain ⟨C, hC3, hsieve⟩ := h4
  let c : ℝ := 1 / (40 * C ^ (3 : ℕ))
  have hc_pos : 0 < c := by positivity
  have hc_half : 0 < c / 2 := by positivity
  refine ⟨c / 2, hc_half, ?_⟩
  have hpow_atTop : Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / 14.8)) atTop atTop :=
    Tendsto.const_mul_atTop hc_pos
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14.8)).comp tendsto_natCast_atTop_atTop)
  have h_ev1 : ∀ᶠ n : ℕ in atTop, C ≤ c * (n : ℝ) ^ ((1 : ℝ) / 14.8) :=
    hpow_atTop.eventually (eventually_ge_atTop C)
  have h_ev2 : ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ c * (n : ℝ) ^ ((1 : ℝ) / 14.8) :=
    hpow_atTop.eventually (eventually_ge_atTop 6)
  have h_ev3 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [h_ev1, h_ev2, h_ev3] with n hzC hz6 hn2
  set z : ℝ := c * (n : ℝ) ^ ((1 : ℝ) / 14.8)
  have hz3 : 3 ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hz_times : z * z ^ ((64 : ℝ) / 15) = z ^ ((79 : ℝ) / 15) := by
    calc z * z ^ ((64 : ℝ) / 15) = z ^ ((1 : ℝ) + 64 / 15) := by
          rw [Real.rpow_add hz_pos, Real.rpow_one]
      _ = _ := by norm_num
  have hz_square : z ^ ((79 : ℝ) / 15) * z ^ ((79 : ℝ) / 15) = z ^ ((158 : ℝ) / 15) := by
    rw [← Real.rpow_add hz_pos]
    norm_num
  have hz_combined : z ^ ((64 : ℝ) / 15) * z ^ ((158 : ℝ) / 15) = z ^ ((74 : ℝ) / 5) := by
    rw [← Real.rpow_add hz_pos]
    norm_num
  obtain ⟨k, hk2, hzA, hA2z⟩ := exists_pow_two_near hz3
  let A : ℕ := 2 ^ k
  have hA_ge : 4 ≤ A := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    simpa [A] using this
  have hA_odd : ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ ((p : ℤ) ∣ (A : ℤ)) := by
    intro p hp hp3 hdiv
    have hdivN : p ∣ 2 ^ k := Int.natCast_dvd_natCast.mp hdiv
    have hp2 := hp.eq_two_or_odd
    have hdvd2 := hp.dvd_of_dvd_pow hdivN
    have := Nat.dvd_prime Nat.prime_two |>.mp hdvd2
    omega
  let Lq : ℕ := ⌈C * z ^ ((64 : ℝ) / 15)⌉₊
  have hLq : C * z ^ ((64 : ℝ) / 15) ≤ (Lq : ℝ) := Nat.le_ceil _
  let bq : ℤ := if Even n then -1 else 1
  obtain ⟨q, hq_mem, hq_odd, hq_sieve⟩ :=
    hsieve z 1 Lq (A : ℤ) bq hzC hLq (fun p hp hp3 _ => hA_odd p hp hp3)
  have hq_ge : 1 ≤ q := (Finset.mem_Ico.mp hq_mem).1
  have hq_lt : q < 1 + Lq := (Finset.mem_Ico.mp hq_mem).2
  have hLq_lt : (Lq : ℝ) < C * z ^ ((64 : ℝ) / 15) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq_leR : (q : ℝ) ≤ 2 * C * z ^ ((64 : ℝ) / 15) := by
    have hqR : (q : ℝ) < 1 + (Lq : ℝ) := by exact_mod_cast hq_lt
    have hz5 : (1 : ℝ) ≤ z ^ ((64 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCz5 : (2 : ℝ) ≤ C * z ^ ((64 : ℝ) / 15) := by nlinarith
    linarith
  let m : ℕ := if Even n then A * q - 1 else A * q
  have hAq4 : 4 ≤ A * q := Nat.mul_le_mul hA_ge hq_ge
  have hm_ge3 : 3 ≤ m := by
    dsimp only [m]
    split_ifs <;> omega
  have hm_leR : (m : ℝ) ≤ 4 * C * z ^ ((79 : ℝ) / 15) := by
    have hAqR : ((A * q : ℕ) : ℝ) ≤ 4 * C * z ^ ((79 : ℝ) / 15) := by
      calc ((A * q : ℕ) : ℝ) = (A : ℝ) * (q : ℝ) := by push_cast; ring
        _ ≤ (2 * z) * (2 * C * z ^ ((64 : ℝ) / 15)) := by gcongr
        _ = 4 * C * (z * z ^ ((64 : ℝ) / 15)) := by ring
        _ = 4 * C * z ^ ((79 : ℝ) / 15) := by rw [hz_times]
    dsimp only [m]
    split_ifs with he
    · have hsub : ((A * q - 1 : ℕ) : ℝ) ≤ ((A * q : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (A * q) 1
      linarith
    · exact hAqR
  have hAq_pos : 1 ≤ A * q := by nlinarith
  have hm_nodvd : ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ p ∣ m := by
    intro p hp hp3 hpz hpm
    have hps := hq_sieve p hp hp3 hpz
    dsimp only [m] at hpm
    split_ifs at hpm with he
    · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
        have hcast : ((A * q - 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by
          simp [bq, he]
          omega
        rw [← hcast]
        exact Int.natCast_dvd_natCast.mpr hpm
      exact hps.2 hpmZ
    · rcases hp.dvd_mul.mp hpm with hpA | hpq
      · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
      · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
  have hm_fac : ∀ p ∈ m.primeFactors, z < ((p ^ (m.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m : ¬ 2 ∣ m := by
          dsimp only [m]
          rw [if_pos he]
          omega
        exact False.elim (hodd_m hpm)
      · have hm_eq : m = A * q := by simp [m, he]
        have hpow_dvd : 2 ^ k ∣ m := by
          rw [hm_eq]
          exact dvd_mul_right A q
        have hk_le : k ≤ m.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ m.factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        have h2leR : (A : ℝ) ≤ ((2 ^ m.factorization 2 : ℕ) : ℝ) := by exact_mod_cast h2le
        exact hzA.trans_le h2leR
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        exact hm_nodvd p hp hp3 hle hpm
      have hk1 : 1 ≤ m.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm
      have hpp : p ≤ p ^ m.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ m.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  have hm1_fac : ∀ p ∈ (m + 1).primeFactors, z < ((p ^ ((m + 1).factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm1 := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have hm1_eq : m + 1 = A * q := by
          dsimp only [m]
          rw [if_pos he]
          omega
        have hpow_dvd : 2 ^ k ∣ m + 1 := by
          rw [hm1_eq]
          exact dvd_mul_right A q
        have hk_le : k ≤ (m + 1).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ (m + 1).factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        have h2leR : (A : ℝ) ≤ ((2 ^ (m + 1).factorization 2 : ℕ) : ℝ) := by exact_mod_cast h2le
        exact hzA.trans_le h2leR
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m1 : ¬ 2 ∣ m + 1 := by
          dsimp only [m]
          rw [if_neg he]
          omega
        exact False.elim (hodd_m1 hpm1)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        have hps := hq_sieve p hp hp3 hle
        dsimp only [m] at hpm1
        split_ifs at hpm1 with he
        · have hsub1 : A * q - 1 + 1 = A * q := Nat.sub_add_cancel hAq_pos
          have hpAq : p ∣ A * q := by rwa [hsub1] at hpm1
          rcases hp.dvd_mul.mp hpAq with hpA | hpq
          · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
          · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
        · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
            have hcast : ((A * q + 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by
              simp [bq, he]
            rw [← hcast]
            exact Int.natCast_dvd_natCast.mpr hpm1
          exact hps.2 hpmZ
      have hk1 : 1 ≤ (m + 1).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm1
      have hpp : p ≤ p ^ (m + 1).factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ (m + 1).factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  let Xt : ℕ := ⌈(n : ℝ) / ((m : ℝ) + 1)⌉₊
  let Yt : ℕ := (n - 2) / m + 1
  have hn_scale : (n : ℝ) = z ^ ((74 : ℝ) / 5) / c ^ ((74 : ℝ) / 5) := by
    have hz_pow : z ^ ((74 : ℝ) / 5) = c ^ ((74 : ℝ) / 5) * (n : ℝ) := by
      dsimp only [z]
      rw [Real.mul_rpow hc_pos.le (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hz_pow]
    field_simp [hc_pos.ne']
  have hmm1_le : (m : ℝ) * ((m : ℝ) + 1) ≤ 20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15) := by
    have hm1_le : (m : ℝ) + 1 ≤ 5 * C * z ^ ((79 : ℝ) / 15) := by
      have h1Cz6 : (1 : ℝ) ≤ C * z ^ ((79 : ℝ) / 15) := by
        have : (1 : ℝ) ≤ C := by linarith
        have : (1 : ℝ) ≤ z ^ ((79 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
        nlinarith
      linarith
    calc (m : ℝ) * ((m : ℝ) + 1) ≤ (4 * C * z ^ ((79 : ℝ) / 15)) * (5 * C * z ^ ((79 : ℝ) / 15)) := by gcongr
      _ = 20 * C ^ (2 : ℕ) * (z ^ ((79 : ℝ) / 15) * z ^ ((79 : ℝ) / 15)) := by ring
      _ = 20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15) := by rw [hz_square]
  have hc_coefficient : 20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5) ≤ 1 / (2 * C) := by
    have h40 : (1 : ℝ) ≤ 40 * C ^ (3 : ℕ) := by nlinarith
    have hc_le1 : c ≤ 1 := by
      dsimp only [c]
      rw [div_le_one (by positivity)]
      exact h40
    have hc_power_le : c ^ ((74 : ℝ) / 5) ≤ c := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        hc_pos hc_le1 (by norm_num : (1 : ℝ) ≤ 74 / 5)
    calc 20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5) ≤ 20 * C ^ (2 : ℕ) * c := by gcongr
      _ = 1 / (2 * C) := by
        dsimp only [c]
        field_simp
        ring
  have hdiff_ge : C * z ^ ((64 : ℝ) / 15) ≤ (Yt : ℝ) - (Xt : ℝ) := by
    have hYt_gt : ((n : ℝ) - 2) / (m : ℝ) < (Yt : ℝ) := by
      have hm_pos : 0 < m := by omega
      have hdiv : n - 2 < m * ((n - 2) / m + 1) := by
        have := Nat.lt_div_mul_add hm_pos (a := n - 2)
        linarith
      have hdivR : ((n - 2 : ℕ) : ℝ) < (m : ℝ) * (((n - 2) / m + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      have hn2R : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hn2]
        norm_num
      rw [hn2R]
      exact (div_lt_iff₀' (by positivity)).mpr (by simpa [Yt] using hdivR)
    have hXt_lt : (Xt : ℝ) < (n : ℝ) / ((m : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hn_gap : 2 * C * z ^ ((64 : ℝ) / 15) ≤ (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      rw [hn_scale, div_div]
      have hden_pos : 0 < c ^ ((74 : ℝ) / 5) * ((m : ℝ) * ((m : ℝ) + 1)) := by positivity
      rw [le_div_iff₀ hden_pos]
      calc 2 * C * z ^ ((64 : ℝ) / 15) * (c ^ ((74 : ℝ) / 5) * ((m : ℝ) * ((m : ℝ) + 1)))
          ≤ 2 * C * z ^ ((64 : ℝ) / 15) * (c ^ ((74 : ℝ) / 5) * (20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15))) := by
            gcongr
        _ = 2 * C * (20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5)) *
            (z ^ ((64 : ℝ) / 15) * z ^ ((158 : ℝ) / 15)) := by ring
        _ = 2 * C * (20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5)) * z ^ ((74 : ℝ) / 5) := by
          rw [hz_combined]
        _ ≤ 2 * C * (1 / (2 * C)) * z ^ ((74 : ℝ) / 5) := by gcongr
        _ = z ^ ((74 : ℝ) / 5) := by
          field_simp
    have hsub_id : (n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1) =
        (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hm10 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    have h2m : 2 / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have hCz5_ge3 : 3 ≤ C * z ^ ((64 : ℝ) / 15) := by
      have hz5 : 1 ≤ z ^ ((64 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
      nlinarith
    have hpart : ((n : ℝ) - 2) / (m : ℝ) - ((n : ℝ) / ((m : ℝ) + 1) + 1) =
        ((n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)) - 2 / (m : ℝ) - 1 := by ring
    linarith
  have hXY_le : Xt ≤ Yt := by
    have hpos : (0 : ℝ) ≤ (Yt : ℝ) - (Xt : ℝ) := by
      have : 0 ≤ C * z ^ ((64 : ℝ) / 15) := by positivity
      linarith
    exact_mod_cast (sub_nonneg.mp hpos)
  let Lt : ℕ := Yt - Xt
  have hLt_eq : Xt + Lt = Yt := Nat.add_sub_cancel' hXY_le
  have hLtR : C * z ^ ((64 : ℝ) / 15) ≤ (Lt : ℝ) := by
    have : (Lt : ℝ) = (Yt : ℝ) - (Xt : ℝ) := by
      dsimp only [Lt]
      rw [Nat.cast_sub hXY_le]
    linarith
  obtain ⟨t, ht_mem, ht_odd, ht_sieve⟩ :=
    hsieve z Xt Lt (-(m : ℤ)) (n : ℤ) hzC hLtR fun p hp hp3 hpz hdiv => by
      have hpm : p ∣ m := Int.natCast_dvd_natCast.mp (dvd_neg.mp hdiv)
      exact hm_nodvd p hp hp3 hpz hpm
  have ht_ge : Xt ≤ t := (Finset.mem_Ico.mp ht_mem).1
  have ht_lt : t < Yt := by
    rw [← hLt_eq]
    exact (Finset.mem_Ico.mp ht_mem).2
  have hut : n - m * t ≤ t := by
    have h1' : (n : ℝ) / ((m : ℝ) + 1) ≤ (Xt : ℝ) := Nat.le_ceil _
    have h2' : (Xt : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge
    have h3' : (n : ℝ) ≤ (t : ℝ) * ((m : ℝ) + 1) := (div_le_iff₀ (by positivity)).mp (h1'.trans h2')
    have h3N : n ≤ (m + 1) * t := by exact_mod_cast (by linarith : (n : ℝ) ≤ ((m : ℝ) + 1) * (t : ℝ))
    have h3N' : n ≤ m * t + t := by linarith
    omega
  have hmt_le : m * t ≤ n - 2 := by
    have htle : t ≤ (n - 2) / m := by omega
    calc m * t ≤ m * ((n - 2) / m) := Nat.mul_le_mul_left m htle
      _ ≤ n - 2 := Nat.mul_div_le (n - 2) m
  let u : ℕ := n - m * t
  have hu2 : 2 ≤ u := by omega
  have ht2 : 2 ≤ t := by omega
  have hn_eq : n = m * t + u := by omega
  have ht_fac : ∀ p ∈ t.primeFactors, z < ((p ^ (t.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpt := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      exact False.elim (ht_odd hpt)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        exact (ht_sieve p hp hp3 hle).1 (Int.natCast_dvd_natCast.mpr hpt)
      have hk1 : 1 ≤ t.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpt
      have hpp : p ≤ p ^ t.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ t.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  have hu_odd : ¬ 2 ∣ u := by
    by_cases he : Even n
    · have hm_odd : ¬ 2 ∣ m := by
        have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        dsimp only [m]
        rw [if_pos he]
        omega
      obtain ⟨r, hr⟩ := he
      intro h2u
      have h2mt : 2 ∣ m * t := by omega
      rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp h2mt with h2m | h2t
      · exact hm_odd h2m
      · exact ht_odd h2t
    · have hm_even : 2 ∣ m := by
        dsimp only [m]
        rw [if_neg he]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
      intro h2u
      have h2mt : 2 ∣ m * t := dvd_mul_of_dvd_left hm_even t
      have h2n : 2 ∣ n := by
        rw [hn_eq]
        exact dvd_add h2mt h2u
      exact he (even_iff_two_dvd.mpr h2n)
  have hu_fac : ∀ p ∈ u.primeFactors, z < ((p ^ (u.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpu := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      exact False.elim (hu_odd hpu)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        have hpuZ : (p : ℤ) ∣ -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
          have hcast : (u : ℤ) = -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
            dsimp only [u]
            zify [show m * t ≤ n by omega]
            ring
          rw [← hcast]
          exact Int.natCast_dvd_natCast.mpr hpu
        exact (ht_sieve p hp hp3 hle).2 hpuZ
      have hk1 : 1 ≤ u.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpu
      have hpp : p ≤ p ^ u.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ u.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  let s : ℕ := ⌊z⌋₊ - 2
  have hs_le_z : (s : ℝ) + 2 ≤ z := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    rw [hs2R]
    exact Nat.floor_le (by linarith)
  have hmac := macneish h1 h2
  have hsm : s ≤ Erdos724.maxMOLS m := by
    refine hmac m (by omega) s fun p hp => ?_
    have hz_lt := hm_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ m.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ m.factorization p := by exact_mod_cast hltR
    omega
  have hsm1 : s ≤ Erdos724.maxMOLS (m + 1) := by
    refine hmac (m + 1) (by omega) s fun p hp => ?_
    have hz_lt := hm1_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ (m + 1).factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ (m + 1).factorization p := by exact_mod_cast hltR
    omega
  have hst : s + 1 ≤ Erdos724.maxMOLS t := by
    refine hmac t ht2 (s + 1) fun p hp => ?_
    have hz_lt := ht_fac p hp
    have hltR : (s : ℝ) + 2 < ((p ^ t.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 2 < p ^ t.factorization p := by exact_mod_cast hltR
    omega
  have hsu : s ≤ Erdos724.maxMOLS u := by
    refine hmac u hu2 s fun p hp => ?_
    have hz_lt := hu_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ u.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ u.factorization p := by exact_mod_cast hltR
    omega
  have hs_n : s ≤ Erdos724.maxMOLS n := by
    rw [hn_eq]
    exact h3 m t u s (by omega) (by omega) hut hsm hsm1 hst hsu
  have hs_lower : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 14.8) ≤ (s : ℝ) := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    have hfl_gt : z - 1 < (⌊z⌋₊ : ℝ) := Nat.sub_one_lt_floor z
    have h1' : z - 3 < (s : ℝ) := by linarith
    have h2' : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 14.8) = z / 2 := by
      dsimp only [z]
      ring
    linarith
  have hs_nR : (s : ℝ) ≤ (Erdos724.maxMOLS n : ℝ) := by exact_mod_cast hs_n
  exact hs_lower.trans hs_nR

end OMA.R_Erdos724_erdos_724_variants_beth_R1
