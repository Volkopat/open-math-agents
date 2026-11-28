import OMAStatements.S_oeis_a397578
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

namespace OMA.P_oeis_a397578

open OMA.S_oeis_a397578

private lemma sigma_eq_arith (k : ℕ) : sigma k = ArithmeticFunction.sigma 1 k := by
  simp [sigma, ArithmeticFunction.sigma_apply]

private lemma sigma_mul_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    sigma (a * b) = sigma a * sigma b := by
  simp only [sigma_eq_arith]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

private lemma sigma_prime_pow_bound {P q e : ℕ} (hq : q.Prime) (hPq : P < q) :
    P * sigma (q ^ e) ≤ (P + 1) * q ^ e := by
  have hgeom : ∀ m : ℕ, (q - 1) * (∑ i ∈ Finset.range (m + 1), q ^ i) = q ^ (m + 1) - 1 := by
    intro m
    induction m with
    | zero =>
      simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have h1 : 1 ≤ q ^ (m + 1) := Nat.one_le_pow _ _ hq.pos
      have hmul : (q - 1) * q ^ (m + 1) = q ^ (m + 1 + 1) - q ^ (m + 1) := by
        rw [Nat.sub_mul, one_mul, ← pow_succ']
      rw [hmul]
      have hle : q ^ (m + 1) ≤ q ^ (m + 1 + 1) := Nat.pow_le_pow_right hq.pos (by omega)
      omega
  have hsum : sigma (q ^ e) = ∑ i ∈ Finset.range (e + 1), q ^ i := by
    simp [sigma, Nat.divisors_prime_pow hq]
  have hq1_pos : 0 < q - 1 := by have := hq.two_le; omega
  have hPq_ineq : P * q ≤ (P + 1) * (q - 1) := by
    have : (P + 1) * (q - 1) + (P + 1) = (P + 1) * q := by
      have hq1 : q - 1 + 1 = q := by have := hq.two_le; omega
      calc (P + 1) * (q - 1) + (P + 1) = (P + 1) * (q - 1 + 1) := by ring
        _ = (P + 1) * q := by rw [hq1]
    nlinarith
  have hmul_ineq : (q - 1) * (P * sigma (q ^ e)) ≤ (q - 1) * ((P + 1) * q ^ e) := by
    calc (q - 1) * (P * sigma (q ^ e))
        = P * ((q - 1) * ∑ i ∈ Finset.range (e + 1), q ^ i) := by rw [hsum]; ring
      _ = P * (q ^ (e + 1) - 1) := by rw [hgeom e]
      _ ≤ P * q ^ (e + 1) := Nat.mul_le_mul_left P (Nat.sub_le _ _)
      _ = (P * q) * q ^ e := by rw [pow_succ']; ring
      _ ≤ ((P + 1) * (q - 1)) * q ^ e := Nat.mul_le_mul_right _ hPq_ineq
      _ = (q - 1) * ((P + 1) * q ^ e) := by ring
  exact Nat.le_of_mul_le_mul_left hmul_ineq hq1_pos

private lemma sigma_smooth_upper_aux {P : ℕ} (_hP : 1 ≤ P) :
    ∀ m : ℕ, 1 ≤ m → (∀ q : ℕ, q.Prime → q ∣ m → P < q) →
      ∃ ω : ℕ, P ^ ω ≤ m ∧ P ^ ω * sigma m ≤ (P + 1) ^ ω * m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm hprimes
    by_cases hm1 : m = 1
    · subst hm1
      exact ⟨0, by simp, by simp [sigma]⟩
    · set q := m.minFac
      have hq : q.Prime := Nat.minFac_prime hm1
      have hqm : q ∣ m := Nat.minFac_dvd m
      have hPq : P < q := hprimes q hq hqm
      set e := m.factorization q
      have he : 1 ≤ e := by
        have hne : m ≠ 0 := by omega
        exact Nat.Prime.factorization_pos_of_dvd hq hne hqm
      have hqe_dvd : q ^ e ∣ m := Nat.ordProj_dvd m q
      set m' := m / q ^ e
      have hm_eq : m = q ^ e * m' := (Nat.mul_div_cancel' hqe_dvd).symm
      have hqe_pos : 0 < q ^ e := pow_pos hq.pos e
      have hm'_pos : 1 ≤ m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | hpos
        · rw [h0, mul_zero] at hm_eq; omega
        · exact hpos
      have hm'_lt : m' < m := by
        have hqe_gt1 : 1 < q ^ e := one_lt_pow₀ hq.one_lt (by omega)
        calc m' = 1 * m' := (one_mul m').symm
          _ < q ^ e * m' := Nat.mul_lt_mul_of_pos_right hqe_gt1 hm'_pos
          _ = m := hm_eq.symm
      have hcop : Nat.Coprime (q ^ e) m' := by
        apply Nat.Coprime.pow_left
        rw [hq.coprime_iff_not_dvd]
        exact Nat.not_dvd_ordCompl hq (by omega)
      have hprimes' : ∀ r : ℕ, r.Prime → r ∣ m' → P < r := by
        intro r hr hrm'
        exact hprimes r hr (dvd_trans hrm' (hm_eq ▸ dvd_mul_left m' (q ^ e)))
      obtain ⟨ω', hpow', hsig'⟩ := ih m' hm'_lt hm'_pos hprimes'
      refine ⟨ω' + 1, ?_, ?_⟩
      · have hq_le_qe : q ≤ q ^ e := by
          calc q = q ^ 1 := (pow_one q).symm
            _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he
        calc P ^ (ω' + 1) = P * P ^ ω' := by rw [pow_succ']
          _ ≤ q ^ e * m' := Nat.mul_le_mul (le_trans (le_of_lt hPq) hq_le_qe) hpow'
          _ = m := hm_eq.symm
      · have hqbound := sigma_prime_pow_bound hq hPq (e := e)
        calc P ^ (ω' + 1) * sigma m
            = P * P ^ ω' * (sigma (q ^ e) * sigma m') := by
                rw [pow_succ', hm_eq, sigma_mul_coprime hcop]
          _ = (P * sigma (q ^ e)) * (P ^ ω' * sigma m') := by ring
          _ ≤ ((P + 1) * q ^ e) * ((P + 1) ^ ω' * m') := Nat.mul_le_mul hqbound hsig'
          _ = (P + 1) ^ (ω' + 1) * (q ^ e * m') := by rw [pow_succ']; ring
          _ = (P + 1) ^ (ω' + 1) * m := by rw [hm_eq]

private lemma two_pow_le_factorial (j : ℕ) : 2 ^ j ≤ (j + 1).factorial := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ', Nat.factorial_succ]
    exact Nat.mul_le_mul (by omega) ih

private lemma succ_pow_lt_three_mul_pow {P : ℕ} (hP : 1 ≤ P) :
    (P + 1) ^ P < 3 * P ^ P := by
  suffices hQ : ((P + 1 : ℚ) / (P : ℚ)) ^ P < 3 by
    have hPpos : (0 : ℚ) < (P : ℚ) := by exact_mod_cast hP
    have hPP : (0 : ℚ) < (P : ℚ) ^ P := pow_pos hPpos P
    rw [div_pow, div_lt_iff₀ hPP] at hQ
    exact_mod_cast hQ
  have hPne : (P : ℚ) ≠ 0 := by positivity
  have h1 : ((P + 1 : ℚ) / (P : ℚ)) = 1 / (P : ℚ) + 1 := by field_simp; ring
  rw [h1, add_pow]
  have hterm : ∀ j ∈ Finset.range (P + 1),
      (1 / (P : ℚ)) ^ j * (1 : ℚ) ^ (P - j) * (P.choose j : ℚ) ≤
        if j = 0 then 1 else 1 / ((2 : ℚ) ^ (j - 1)) := by
    intro j _
    simp only [one_pow, mul_one, one_div, inv_pow]
    by_cases hj0 : j = 0
    · subst hj0; simp
    · rw [if_neg hj0]
      have hdesc : P.descFactorial j = j.factorial * P.choose j := Nat.descFactorial_eq_factorial_mul_choose P j
      have hdesc_le : P.descFactorial j ≤ P ^ j := Nat.descFactorial_le_pow P j
      have h2le : 2 ^ (j - 1) ≤ j.factorial := by
        have := two_pow_le_factorial (j - 1)
        rwa [show j - 1 + 1 = j by omega] at this
      have hnat : P.choose j * 2 ^ (j - 1) ≤ P ^ j := by
        calc P.choose j * 2 ^ (j - 1) ≤ P.choose j * j.factorial := Nat.mul_le_mul_left _ h2le
          _ = j.factorial * P.choose j := mul_comm _ _
          _ = P.descFactorial j := hdesc.symm
          _ ≤ P ^ j := hdesc_le
      have hQnat : (P.choose j : ℚ) * (2 : ℚ) ^ (j - 1) ≤ (P : ℚ) ^ j := by exact_mod_cast hnat
      have hPj_pos : (0 : ℚ) < (P : ℚ) ^ j := pow_pos (by exact_mod_cast hP) j
      have h2j_pos : (0 : ℚ) < (2 : ℚ) ^ (j - 1) := by positivity
      rw [← div_eq_inv_mul, ← one_div, div_le_div_iff₀ hPj_pos h2j_pos]
      linarith
  have hsum_le :
      ∑ j ∈ Finset.range (P + 1), (1 / (P : ℚ)) ^ j * (1 : ℚ) ^ (P - j) * (P.choose j : ℚ) ≤
        ∑ j ∈ Finset.range (P + 1), if j = 0 then (1 : ℚ) else 1 / ((2 : ℚ) ^ (j - 1)) :=
    Finset.sum_le_sum hterm
  have hgeo : ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.range n, (1 : ℚ) / (2 : ℚ) ^ j = 2 - 1 / (2 : ℚ) ^ (n - 1) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => norm_num
      | succ n' =>
        rw [Finset.sum_range_succ, ih (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [pow_succ]
        field_simp
        ring
  have hsplit :
      (∑ j ∈ Finset.range (P + 1), if j = 0 then (1 : ℚ) else 1 / ((2 : ℚ) ^ (j - 1))) =
        1 + ∑ j ∈ Finset.range P, (1 : ℚ) / (2 : ℚ) ^ j := by
    rw [Finset.sum_range_succ']
    simp [add_comm]
  rw [hsplit, hgeo P hP] at hsum_le
  have hpos2 : (0 : ℚ) < 1 / (2 : ℚ) ^ (P - 1) := by positivity
  linarith

private lemma sigma_lt_three_mul {P m : ℕ} (hP : 1 ≤ P) (hm : 1 ≤ m) (hm_lt : m < P ^ P)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ m → P < q) :
    sigma m < 3 * m := by
  obtain ⟨ω, hpow, hsig⟩ := sigma_smooth_upper_aux hP m hm hprimes
  have hω_le : ω ≤ P := by
    by_contra hgt
    have hge : P ^ P ≤ P ^ ω := Nat.pow_le_pow_right hP (by omega)
    omega
  have hPP_pos : 0 < P ^ P := pow_pos hP P
  have hmul : P ^ P * sigma m < P ^ P * (3 * m) := by
    calc P ^ P * sigma m
        = P ^ (P - ω) * (P ^ ω * sigma m) := by
            rw [← mul_assoc, ← pow_add, show P - ω + ω = P by omega]
      _ ≤ P ^ (P - ω) * ((P + 1) ^ ω * m) := Nat.mul_le_mul_left _ hsig
      _ ≤ (P + 1) ^ (P - ω) * ((P + 1) ^ ω * m) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = (P + 1) ^ P * m := by
            rw [← mul_assoc, ← pow_add, show P - ω + ω = P by omega]
      _ < (3 * P ^ P) * m := Nat.mul_lt_mul_of_pos_right (succ_pow_lt_three_mul_pow hP) hm
      _ = P ^ P * (3 * m) := by ring
  exact Nat.lt_of_mul_lt_mul_left hmul

private lemma squarefree_mul_sq_decomp (m : ℕ) (hm : 1 ≤ m) :
    ∃ s r : ℕ, Squarefree s ∧ 1 ≤ r ∧ r ≤ m ∧ s ≤ m ∧ m = s * r ^ 2 := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hsf : Squarefree m
    · exact ⟨m, 1, hsf, le_refl 1, hm, le_refl m, by ring⟩
    · rw [Nat.squarefree_iff_prime_squarefree] at hsf
      push Not at hsf
      obtain ⟨p, hp, hpp⟩ := hsf
      set m' := m / (p * p)
      have hm_eq : m = m' * (p * p) := (Nat.div_mul_cancel hpp).symm
      have hm'_pos : 1 ≤ m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | hpos
        · rw [h0, zero_mul] at hm_eq; omega
        · exact hpos
      have hp2 : 4 ≤ p * p := by have := hp.two_le; nlinarith
      have hm'_lt : m' < m := by nlinarith
      obtain ⟨s, r, hsf_s, hr1, hrm', hsm', hm'_eq⟩ := ih m' hm'_lt hm'_pos
      refine ⟨s, r * p, hsf_s, by nlinarith [hp.two_le], ?_, le_trans hsm' (le_of_lt hm'_lt), ?_⟩
      · calc r * p ≤ m' * p := Nat.mul_le_mul_right p hrm'
          _ ≤ m' * (p * p) := Nat.mul_le_mul_left m' (by nlinarith [hp.two_le])
          _ = m := hm_eq.symm
      · rw [hm_eq, hm'_eq]; ring

private lemma harmonic_dyadic_lower (t : ℕ) :
    (1 : ℚ) + (t : ℚ) / 2 ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ t), (1 : ℚ) / (m : ℚ) := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    have hsplit : Finset.Icc 1 (2 ^ (t + 1)) =
        Finset.Icc 1 (2 ^ t) ∪ Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1)) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      have hle : 2 ^ t ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by decide)
      omega
    have hdisj : Disjoint (Finset.Icc 1 (2 ^ t)) (Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_Icc, Finset.mem_Ioc] at hx1 hx2
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail : (1 : ℚ) / 2 ≤ ∑ m ∈ Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1)), (1 : ℚ) / (m : ℚ) := by
      have hle_each : ∀ m ∈ Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1)),
          (1 : ℚ) / ((2 ^ (t + 1) : ℕ) : ℚ) ≤ (1 : ℚ) / (m : ℚ) := by
        intro m hm
        rw [Finset.mem_Ioc] at hm
        have hmpos : (0 : ℚ) < (m : ℚ) := by
          have : 0 < m := lt_of_le_of_lt (Nat.zero_le _) hm.1
          exact_mod_cast this
        have hleQ : (m : ℚ) ≤ ((2 ^ (t + 1) : ℕ) : ℚ) := by exact_mod_cast hm.2
        exact one_div_le_one_div_of_le hmpos hleQ
      calc (1 : ℚ) / 2
          = ((2 ^ t : ℕ) : ℚ) * ((1 : ℚ) / ((2 ^ (t + 1) : ℕ) : ℚ)) := by
              push_cast; rw [pow_succ]; field_simp
        _ = ∑ _m ∈ Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1)), (1 : ℚ) / ((2 ^ (t + 1) : ℕ) : ℚ) := by
              rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
              congr 1
              have : 2 ^ (t + 1) - 2 ^ t = 2 ^ t := by rw [pow_succ]; omega
              exact_mod_cast this.symm
        _ ≤ ∑ m ∈ Finset.Ioc (2 ^ t : ℕ) (2 ^ (t + 1)), (1 : ℚ) / (m : ℚ) :=
              Finset.sum_le_sum hle_each
    push_cast
    linarith

private lemma inv_sq_sum_lt_two (P : ℕ) (hP : 1 ≤ P) :
    ∑ r ∈ Finset.Icc 1 P, (1 : ℚ) / ((r : ℚ) ^ 2) ≤ 2 - 1 / (P : ℚ) := by
  induction P with
  | zero => omega
  | succ P ih =>
    cases P with
    | zero => norm_num
    | succ P' =>
      set n := P' + 1
      have hn : 1 ≤ n := by omega
      have hsplit : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnotmem : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hsplit, Finset.sum_insert hnotmem]
      have hprev := ih hn
      have hstep : (1 : ℚ) / ((n + 1 : ℕ) : ℚ) ^ 2 ≤ 1 / (n : ℚ) - 1 / ((n + 1 : ℕ) : ℚ) := by
        have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
        have hn1Q : (0 : ℚ) < (n : ℚ) + 1 := by positivity
        push_cast
        have hdiff : 1 / (n : ℚ) - 1 / ((n : ℚ) + 1) = 1 / ((n : ℚ) * ((n : ℚ) + 1)) := by
          field_simp; ring
        rw [hdiff]
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      linarith

private lemma sum_inv_divisors_eq {k : ℕ} (hk : 0 < k) :
    ∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ) = (sigma k : ℚ) / (k : ℚ) := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  rw [eq_div_iff hkQ, Finset.sum_mul]
  have h1 : ∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ) * (k : ℚ) =
      ∑ d ∈ k.divisors, ((k / d : ℕ) : ℚ) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
    have hmul : (d : ℚ) * ((k / d : ℕ) : ℚ) = (k : ℚ) := by
      exact_mod_cast Nat.mul_div_cancel' hdvd
    field_simp
    linarith
  rw [h1]
  have h2 : ∑ d ∈ k.divisors, (k / d : ℕ) = ∑ d ∈ k.divisors, d := by
    refine Finset.sum_bij (fun d _ => k / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hk.ne'⟩
    · intro a ha b hb hab
      have ha_dvd := Nat.dvd_of_mem_divisors ha
      have hb_dvd := Nat.dvd_of_mem_divisors hb
      have ha_pos := Nat.pos_of_mem_divisors ha
      have hb_pos := Nat.pos_of_mem_divisors hb
      have hka := Nat.mul_div_cancel' ha_dvd
      have hkb := Nat.mul_div_cancel' hb_dvd
      have hkd_pos : 0 < k / a := Nat.div_pos (Nat.le_of_dvd hk ha_dvd) ha_pos
      rw [← hab] at hkb
      have : a * (k / a) = b * (k / a) := hka.trans hkb.symm
      exact Nat.eq_of_mul_eq_mul_right hkd_pos this
    · intro b hb
      refine ⟨k / b, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hb), hk.ne'⟩, ?_⟩
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hb) hk.ne'
    · intro d _; rfl
  unfold sigma
  exact_mod_cast h2

private lemma primorial_sigma_lower (t : ℕ) :
    (t + 2) * primorial (2 ^ t) ≤ 4 * sigma (primorial (2 ^ t)) := by
  set P := 2 ^ t
  set k := primorial P
  have hP1 : 1 ≤ P := Nat.one_le_pow t 2 (by decide)
  have hk_pos : 0 < k := primorial_pos P
  -- Map each m ∈ Icc 1 P to (s m, r m) ∈ k.divisors ×ˢ Icc 1 P
  have hdecomp : ∀ m ∈ Finset.Icc 1 P,
      ∃ p ∈ k.divisors ×ˢ Finset.Icc 1 P, p.1 * p.2 ^ 2 = m := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    obtain ⟨s, r, hsf, hr1, hrm, hsm, hm_eq⟩ := squarefree_mul_sq_decomp m hm.1
    have hs_dvd : s ∣ k := dvd_trans hsf.dvd_primorial (primorial_dvd_primorial (le_trans hsm hm.2))
    refine ⟨(s, r), Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hs_dvd, hk_pos.ne'⟩,
      Finset.mem_Icc.mpr ⟨hr1, le_trans hrm hm.2⟩⟩, hm_eq.symm⟩
  let f : ℕ → ℕ × ℕ := fun m =>
    if hm : m ∈ Finset.Icc 1 P then Classical.choose (hdecomp m hm) else (1, 1)
  have hf_mem : ∀ m ∈ Finset.Icc 1 P, f m ∈ k.divisors ×ˢ Finset.Icc 1 P := by
    intro m hm
    simp only [f, dif_pos hm]
    exact (Classical.choose_spec (hdecomp m hm)).1
  have hf_eq : ∀ m ∈ Finset.Icc 1 P, (f m).1 * (f m).2 ^ 2 = m := by
    intro m hm
    simp only [f, dif_pos hm]
    exact (Classical.choose_spec (hdecomp m hm)).2
  have hf_inj : Set.InjOn f (Finset.Icc 1 P) := by
    intro a ha b hb hab
    have h1 := hf_eq a ha
    have h2 := hf_eq b hb
    rw [hab] at h1
    omega
  have hsum_le : ∑ m ∈ Finset.Icc 1 P, (1 : ℚ) / (m : ℚ) ≤
      ∑ p ∈ k.divisors ×ˢ Finset.Icc 1 P, (1 : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ) ^ 2) := by
    have himg : ∑ m ∈ Finset.Icc 1 P, (1 : ℚ) / (m : ℚ) =
        ∑ p ∈ (Finset.Icc 1 P).image f, (1 : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ) ^ 2) := by
      rw [Finset.sum_image hf_inj]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmeq := hf_eq m hm
      have hQ : ((f m).1 : ℚ) * ((f m).2 : ℚ) ^ 2 = (m : ℚ) := by exact_mod_cast hmeq
      rw [hQ]
    rw [himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro p hp
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hp
      exact hf_mem m hm
    · intro p _ _; positivity
  have hprod : ∑ p ∈ k.divisors ×ˢ Finset.Icc 1 P, (1 : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ) ^ 2) =
      (∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ)) * (∑ r ∈ Finset.Icc 1 P, (1 : ℚ) / (r : ℚ) ^ 2) := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hharm := harmonic_dyadic_lower t
  have hsq := inv_sq_sum_lt_two P hP1
  have hPposQ : (0 : ℚ) < 1 / (P : ℚ) := by positivity
  have hsq2 : ∑ r ∈ Finset.Icc 1 P, (1 : ℚ) / (r : ℚ) ^ 2 ≤ 2 := by linarith
  have hdiv_nonneg : 0 ≤ ∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ) :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hboundQ : (1 : ℚ) + (t : ℚ) / 2 ≤ ((sigma k : ℚ) / (k : ℚ)) * 2 := by
    calc (1 : ℚ) + (t : ℚ) / 2
        ≤ ∑ m ∈ Finset.Icc 1 P, (1 : ℚ) / (m : ℚ) := hharm
      _ ≤ ∑ p ∈ k.divisors ×ˢ Finset.Icc 1 P, (1 : ℚ) / ((p.1 : ℚ) * (p.2 : ℚ) ^ 2) := hsum_le
      _ = (∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ)) * (∑ r ∈ Finset.Icc 1 P, (1 : ℚ) / (r : ℚ) ^ 2) := hprod
      _ ≤ (∑ d ∈ k.divisors, (1 : ℚ) / (d : ℚ)) * 2 := mul_le_mul_of_nonneg_left hsq2 hdiv_nonneg
      _ = ((sigma k : ℚ) / (k : ℚ)) * 2 := by rw [sum_inv_divisors_eq hk_pos]
  have hkQ : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk_pos
  have hmulQ : ((t + 2 : ℕ) : ℚ) * (k : ℚ) ≤ 4 * (sigma k : ℚ) := by
    have h4 : (1 + (t : ℚ) / 2) * (k : ℚ) ≤ (sigma k : ℚ) * 2 := by
      have := mul_le_mul_of_nonneg_right hboundQ (le_of_lt hkQ)
      field_simp at this ⊢
      linarith
    push_cast
    linarith
  exact_mod_cast hmulQ

private theorem prove_main : type_of% @OMA.S_oeis_a397578.main := by
  intro n hn
  set t := 16 * n + 4
  set P := 2 ^ t
  set k := primorial P
  have hP5 : 5 ≤ P := by
    have : 2 ^ 4 ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hk_ge6 : 6 ≤ k := by
    have h2 : 2 ∣ k := (by decide : Nat.Prime 2).dvd_primorial_iff.mpr (by omega)
    have h3 : 3 ∣ k := (by decide : Nat.Prime 3).dvd_primorial_iff.mpr (by omega)
    have h6 : 6 ∣ k := (by decide : Nat.Coprime 2 3).mul_dvd_of_dvd_of_dvd h2 h3
    exact Nat.le_of_dvd (primorial_pos P) h6
  have hk_lt_PP : k + 1 < P ^ P := by
    have h4P : k < 4 ^ P := primorial_lt_four_pow P (by omega)
    have h4_5 : 4 ^ P + 1 ≤ 5 ^ P := by
      have hpow : 4 ^ P + 1 ≤ (4 + 1) ^ P := by
        have h1 : 4 ^ (P - 1) ≥ 1 := Nat.one_le_pow _ 4 (by decide)
        have hstep : ∀ r : ℕ, 1 ≤ r → 4 ^ r + 1 ≤ 5 ^ r := by
          intro r hr
          induction r with
          | zero => omega
          | succ r ih =>
            cases r with
            | zero => decide
            | succ r' =>
              have hprev := ih (by omega)
              have h4ge := Nat.one_le_pow (r' + 1) 4 (by decide)
              rw [pow_succ, pow_succ]
              omega
        exact hstep P (by omega)
      exact hpow
    have h5_P : 5 ^ P ≤ P ^ P := Nat.pow_le_pow_left hP5 P
    omega
  have hprimes_sub : ∀ q : ℕ, q.Prime → q ∣ k - 1 → P < q := by
    intro q hq hqdvd
    by_contra hle
    have hqk : q ∣ k := hq.dvd_primorial_iff.mpr (by omega)
    have h1 : q ∣ k - (k - 1) := Nat.dvd_sub hqk hqdvd
    rw [show k - (k - 1) = 1 by omega] at h1
    exact hq.not_dvd_one h1
  have hprimes_add : ∀ q : ℕ, q.Prime → q ∣ k + 1 → P < q := by
    intro q hq hqdvd
    by_contra hle
    have hqk : q ∣ k := hq.dvd_primorial_iff.mpr (by omega)
    have h1 : q ∣ (k + 1) - k := Nat.dvd_sub hqdvd hqk
    rw [Nat.add_sub_cancel_left] at h1
    exact hq.not_dvd_one h1
  have hsig_sub : sigma (k - 1) < 3 * (k - 1) :=
    sigma_lt_three_mul (by omega) (by omega) (by omega) hprimes_sub
  have hsig_add : sigma (k + 1) < 3 * (k + 1) :=
    sigma_lt_three_mul (by omega) (by omega) hk_lt_PP hprimes_add
  have hsig_k := primorial_sigma_lower t
  refine ⟨k, by omega, ?_, ?_⟩
  · -- sigma k > sigma (k - 1) * n
    have h1 : sigma (k - 1) * n ≤ (3 * k) * n := Nat.mul_le_mul_right n (by omega)
    have h2 : (16 * n + 6) * k ≤ 4 * sigma k := hsig_k
    nlinarith
  · -- sigma k > sigma (k + 1) * n
    have h1 : sigma (k + 1) ≤ 4 * k := by omega
    have h2 : sigma (k + 1) * n ≤ (4 * k) * n := Nat.mul_le_mul_right n h1
    have h3 : (16 * n + 6) * k ≤ 4 * sigma k := hsig_k
    nlinarith

end OMA.P_oeis_a397578

theorem OMA.solution : type_of% @OMA.S_oeis_a397578.main :=
  OMA.P_oeis_a397578.prove_main
