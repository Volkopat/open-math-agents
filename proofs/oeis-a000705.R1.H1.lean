import OMAReductions.R_oeis_a000705_R1

-- Proof of oeis-a000705.R1.H1
-- Local prime-exponent optimality for global maximizers of d(k) / k^ε
-- (Ramanujan's superior highly composite number characterization).
-- Credit: @DPS0340

open Finset

theorem OMA.solution : OMA.R_oeis_a000705_R1.H1 := by
  classical
  intro m n hm hn hmn ε hε hmax_m hmax_n
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  -- For any x ≥ 1 and prime p with e = x.factorization p:
  -- d(p * x) / (p * x)^ε ≤ d(x) / x^ε gives (e + 2) / (e + 1) ≤ p^ε
  -- and if 1 ≤ e, d(x / p) / (x / p)^ε ≤ d(x) / x^ε gives p^ε ≤ (e + 1) / e.
  have hlocal : ∀ {x : ℕ} (hx : 1 ≤ x)
      (hmax : ∀ k : ℕ, 1 ≤ k → (k.divisors.card : ℝ) / (k : ℝ) ^ ε ≤ (x.divisors.card : ℝ) / (x : ℝ) ^ ε)
      {p : ℕ} (hp : p.Prime),
      let e := x.factorization p
      ((e : ℝ) + 2) / ((e : ℝ) + 1) ≤ (p : ℝ) ^ ε ∧
      (1 ≤ e → (p : ℝ) ^ ε ≤ ((e : ℝ) + 1) / (e : ℝ)) := by
    intro x hx hmax p hp
    have hx0 : x ≠ 0 := by omega
    let e := x.factorization p
    let y := x / p ^ e
    have hdvd : p ^ e ∣ x := Nat.ordProj_dvd x p
    have hxy : p ^ e * y = x := Nat.mul_div_cancel' hdvd
    have hy0 : y ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hxy; exact hx0 hxy.symm
    have hndvd : ¬ p ∣ y := Nat.not_dvd_ordCompl hp hx0
    have hcop_pe : Nat.Coprime (p ^ e) y := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left e
    have hcop_pe1 : Nat.Coprime (p ^ (e + 1)) y := (hp.coprime_iff_not_dvd.mpr hndvd).pow_left (e + 1)
    have hdx : x.divisors.card = (e + 1) * y.divisors.card := by
      rw [← hxy, hcop_pe.card_divisors_mul, Nat.divisors_prime_pow hp, card_map, card_range]
    have hdy_pos : (0 : ℝ) < (y.divisors.card : ℝ) := by
      exact_mod_cast card_pos.mpr (Nat.nonempty_divisors.mpr hy0)
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
    have hpε_pos : (0 : ℝ) < (p : ℝ) ^ ε := Real.rpow_pos_of_pos hp_pos ε
    have hxε_pos : (0 : ℝ) < (x : ℝ) ^ ε := Real.rpow_pos_of_pos hx_pos ε
    constructor
    · -- Compare p * x with x
      have hpx_ge1 : 1 ≤ p * x := Nat.mul_pos hp.pos (by omega)
      have hpx_eq : p * x = p ^ (e + 1) * y := by rw [← hxy, pow_succ']; ring
      have hdpx : (p * x).divisors.card = (e + 2) * y.divisors.card := by
        rw [hpx_eq, hcop_pe1.card_divisors_mul, Nat.divisors_prime_pow hp, card_map, card_range]
      have hle := hmax (p * x) hpx_ge1
      rw [hdpx, hdx, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
        Real.mul_rpow hp_pos.le hx_pos.le] at hle
      have h1 : (((e + 2 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / ((p : ℝ) ^ ε * (x : ℝ) ^ ε) ≤
          (((e + 1 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / (x : ℝ) ^ ε := hle
      have h2 : ((e + 2 : ℕ) : ℝ) / (p : ℝ) ^ ε ≤ ((e + 1 : ℕ) : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right h1 (div_pos hxε_pos hdy_pos).le
        have hlhs : ((((e + 2 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / ((p : ℝ) ^ ε * (x : ℝ) ^ ε)) *
            ((x : ℝ) ^ ε / (y.divisors.card : ℝ)) = ((e + 2 : ℕ) : ℝ) / (p : ℝ) ^ ε := by
          field_simp [hpε_pos.ne', hxε_pos.ne', hdy_pos.ne']
        have hrhs : ((((e + 1 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / (x : ℝ) ^ ε) *
            ((x : ℝ) ^ ε / (y.divisors.card : ℝ)) = ((e + 1 : ℕ) : ℝ) := by
          field_simp [hxε_pos.ne', hdy_pos.ne']
        linarith
      rw [div_le_iff₀ hpε_pos] at h2
      rw [div_le_iff₀ (by positivity)]
      push_cast at h2 ⊢
      linarith
    · -- Compare x / p with x when 1 ≤ e
      intro he1
      have hcop_em1 : Nat.Coprime (p ^ (e - 1)) y :=
        (hp.coprime_iff_not_dvd.mpr hndvd).pow_left (e - 1)
      let x' := p ^ (e - 1) * y
      have hx'_mul : p * x' = x := by
        dsimp [x']
        rw [← hxy, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel he1]
      have hx'_ge1 : 1 ≤ x' := Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pos_of_ne_zero hy0)
      have hx'_pos : (0 : ℝ) < (x' : ℝ) := by exact_mod_cast (show 0 < x' by omega)
      have hx'ε_pos : (0 : ℝ) < (x' : ℝ) ^ ε := Real.rpow_pos_of_pos hx'_pos ε
      have hdx' : x'.divisors.card = e * y.divisors.card := by
        dsimp [x']
        rw [hcop_em1.card_divisors_mul, Nat.divisors_prime_pow hp, card_map, card_range,
          Nat.sub_add_cancel he1]
      have hle := hmax x' hx'_ge1
      rw [hdx', hdx, ← hx'_mul] at hle
      rw [Nat.cast_mul e, Nat.cast_mul (e + 1), Nat.cast_mul p x',
        Real.mul_rpow hp_pos.le hx'_pos.le] at hle
      have h1 : ((e : ℝ) * (y.divisors.card : ℝ)) / (x' : ℝ) ^ ε ≤
          (((e + 1 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / ((p : ℝ) ^ ε * (x' : ℝ) ^ ε) := hle
      have h2 : (e : ℝ) ≤ ((e + 1 : ℕ) : ℝ) / (p : ℝ) ^ ε := by
        have hmul := mul_le_mul_of_nonneg_right h1 (div_pos hx'ε_pos hdy_pos).le
        have hlhs : (((e : ℝ) * (y.divisors.card : ℝ)) / (x' : ℝ) ^ ε) *
            ((x' : ℝ) ^ ε / (y.divisors.card : ℝ)) = (e : ℝ) := by
          field_simp [hx'ε_pos.ne', hdy_pos.ne']
        have hrhs : ((((e + 1 : ℕ) : ℝ) * (y.divisors.card : ℝ)) / ((p : ℝ) ^ ε * (x' : ℝ) ^ ε)) *
            ((x' : ℝ) ^ ε / (y.divisors.card : ℝ)) = ((e + 1 : ℕ) : ℝ) / (p : ℝ) ^ ε := by
          field_simp [hpε_pos.ne', hx'ε_pos.ne', hdy_pos.ne']
        linarith
      rw [le_div_iff₀ hpε_pos] at h2
      have he_pos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast (show 0 < e by omega)
      rw [le_div_iff₀ he_pos]
      push_cast at h2 ⊢
      linarith
  -- Whenever two maximizers differ at a prime p, their exponents differ by 1 and p^ε = (a+1)/a
  have hdiff : ∀ {p : ℕ}, p.Prime → m.factorization p ≠ n.factorization p →
      (n.factorization p = m.factorization p + 1 ∨ m.factorization p = n.factorization p + 1) ∧
      ∃ a : ℕ, 0 < a ∧ (p : ℝ) ^ ε = ((a : ℝ) + 1) / (a : ℝ) := by
    intro p hp hne
    have hm_loc := hlocal hm hmax_m hp
    have hn_loc := hlocal hn hmax_n hp
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have he2_ge1 : 1 ≤ n.factorization p := by omega
      have hlo : ((m.factorization p : ℝ) + 2) / ((m.factorization p : ℝ) + 1) ≤ (p : ℝ) ^ ε := hm_loc.1
      have hhi : (p : ℝ) ^ ε ≤ ((n.factorization p : ℝ) + 1) / (n.factorization p : ℝ) := hn_loc.2 he2_ge1
      have hstep : ((n.factorization p : ℝ) + 1) / (n.factorization p : ℝ) ≤
          ((m.factorization p : ℝ) + 2) / ((m.factorization p : ℝ) + 1) := by
        have hm1_pos : (0 : ℝ) < (m.factorization p : ℝ) + 1 := by positivity
        have hn_pos : (0 : ℝ) < (n.factorization p : ℝ) := by exact_mod_cast (show 0 < n.factorization p by omega)
        have hle_R : (m.factorization p : ℝ) + 1 ≤ (n.factorization p : ℝ) := by exact_mod_cast hlt
        rw [div_le_div_iff₀ hn_pos hm1_pos]
        nlinarith
      have hpeq : (p : ℝ) ^ ε = ((m.factorization p : ℝ) + 2) / ((m.factorization p : ℝ) + 1) := by
        linarith
      have hfrac_eq : ((n.factorization p : ℝ) + 1) / (n.factorization p : ℝ) =
          ((m.factorization p : ℝ) + 2) / ((m.factorization p : ℝ) + 1) := by linarith
      have hm1_pos : (0 : ℝ) < (m.factorization p : ℝ) + 1 := by positivity
      have hn_pos : (0 : ℝ) < (n.factorization p : ℝ) := by exact_mod_cast (show 0 < n.factorization p by omega)
      have hcross := (div_eq_div_iff hn_pos.ne' hm1_pos.ne').mp hfrac_eq
      have heq_R : (n.factorization p : ℝ) = (m.factorization p : ℝ) + 1 := by nlinarith
      have heq : n.factorization p = m.factorization p + 1 := by exact_mod_cast heq_R
      refine ⟨Or.inl heq, m.factorization p + 1, by omega, ?_⟩
      rw [hpeq]; push_cast; ring
    · have he1_ge1 : 1 ≤ m.factorization p := by omega
      have hlo : ((n.factorization p : ℝ) + 2) / ((n.factorization p : ℝ) + 1) ≤ (p : ℝ) ^ ε := hn_loc.1
      have hhi : (p : ℝ) ^ ε ≤ ((m.factorization p : ℝ) + 1) / (m.factorization p : ℝ) := hm_loc.2 he1_ge1
      have hstep : ((m.factorization p : ℝ) + 1) / (m.factorization p : ℝ) ≤
          ((n.factorization p : ℝ) + 2) / ((n.factorization p : ℝ) + 1) := by
        have hn1_pos : (0 : ℝ) < (n.factorization p : ℝ) + 1 := by positivity
        have hm_pos : (0 : ℝ) < (m.factorization p : ℝ) := by exact_mod_cast (show 0 < m.factorization p by omega)
        have hle_R : (n.factorization p : ℝ) + 1 ≤ (m.factorization p : ℝ) := by exact_mod_cast hgt
        rw [div_le_div_iff₀ hm_pos hn1_pos]
        nlinarith
      have hpeq : (p : ℝ) ^ ε = ((n.factorization p : ℝ) + 2) / ((n.factorization p : ℝ) + 1) := by
        linarith
      have hfrac_eq : ((m.factorization p : ℝ) + 1) / (m.factorization p : ℝ) =
          ((n.factorization p : ℝ) + 2) / ((n.factorization p : ℝ) + 1) := by linarith
      have hn1_pos : (0 : ℝ) < (n.factorization p : ℝ) + 1 := by positivity
      have hm_pos : (0 : ℝ) < (m.factorization p : ℝ) := by exact_mod_cast (show 0 < m.factorization p by omega)
      have hcross := (div_eq_div_iff hm_pos.ne' hn1_pos.ne').mp hfrac_eq
      have heq_R : (m.factorization p : ℝ) = (n.factorization p : ℝ) + 1 := by nlinarith
      have heq : m.factorization p = n.factorization p + 1 := by exact_mod_cast heq_R
      refine ⟨Or.inr heq, n.factorization p + 1, by omega, ?_⟩
      rw [hpeq]; push_cast; ring
  let D := (m.primeFactors ∪ n.primeFactors).filter fun p => m.factorization p ≠ n.factorization p
  have hD_prime : ∀ p ∈ D, p.Prime := by
    intro p hp
    rcases mem_union.mp (mem_filter.mp hp).1 with h | h
    · exact (Nat.mem_primeFactors.mp h).1
    · exact (Nat.mem_primeFactors.mp h).1
  have hD_nonempty : D.Nonempty := by
    by_contra hemp
    rw [not_nonempty_iff_eq_empty] at hemp
    have hfeq : m.factorization = n.factorization := by
      ext p
      by_contra hne
      have hmem : p ∈ m.primeFactors ∪ n.primeFactors := by
        by_cases hm_p : m.factorization p = 0
        · have hn_p : n.factorization p ≠ 0 := by omega
          exact mem_union_right _ (Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hn_p |> fun h => by
              rwa [Nat.support_factorization] at h),
              Nat.dvd_of_factorization_pos hn_p, hn0⟩)
        · exact mem_union_left _ (Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hm_p |> fun h => by
              rwa [Nat.support_factorization] at h),
              Nat.dvd_of_factorization_pos hm_p, hm0⟩)
      have : p ∈ D := mem_filter.mpr ⟨hmem, hne⟩
      rw [hemp] at this
      exact notMem_empty p this
    have heq : m = n := Nat.factorization_inj hm0 hn0 hfeq
    omega
  by_cases hcard : 1 < D.card
  · right
    obtain ⟨p, hpD, q, hqD, hpq⟩ := one_lt_card.mp hcard
    have hp := hD_prime p hpD
    have hq := hD_prime q hqD
    obtain ⟨_, a, ha, hpa⟩ := hdiff hp (mem_filter.mp hpD).2
    obtain ⟨_, b, hb, hqb⟩ := hdiff hq (mem_filter.mp hqD).2
    exact ⟨p, q, a, b, hp, hq, hpq, ha, hb, hpa, hqb⟩
  · left
    have hcard1 : D.card = 1 := by
      have := card_pos.mpr hD_nonempty
      omega
    obtain ⟨p, hpD⟩ := card_eq_one.mp hcard1
    have hp_in : p ∈ D := by rw [hpD]; exact mem_singleton_self p
    have hp := hD_prime p hp_in
    have hp_ne := (mem_filter.mp hp_in).2
    have hother : ∀ q, q ≠ p → m.factorization q = n.factorization q := by
      intro q hqp
      by_contra hne
      have hmem : q ∈ m.primeFactors ∪ n.primeFactors := by
        by_cases hmq : m.factorization q = 0
        · have hnq : n.factorization q ≠ 0 := by omega
          exact mem_union_right _ (by
            have h1 : q ∈ n.factorization.support := Finsupp.mem_support_iff.mpr hnq
            rwa [Nat.support_factorization] at h1)
        · exact mem_union_left _ (by
            have h1 : q ∈ m.factorization.support := Finsupp.mem_support_iff.mpr hmq
            rwa [Nat.support_factorization] at h1)
      have hqD : q ∈ D := mem_filter.mpr ⟨hmem, hne⟩
      rw [hpD] at hqD
      exact hqp (mem_singleton.mp hqD)
    rcases (hdiff hp hp_ne).1 with hinc | hdec
    · refine ⟨p, hp, ?_⟩
      apply Nat.factorization_inj hn0 (Nat.mul_ne_zero hp.ne_zero hm0)
      ext q
      rw [Nat.factorization_mul hp.ne_zero hm0, Finsupp.add_apply, hp.factorization]
      by_cases hqp : q = p
      · subst hqp; simp [hinc]; omega
      · rw [Finsupp.single_eq_of_ne hqp, zero_add, hother q hqp]
    · exfalso
      have hmeq : m = p * n := by
        apply Nat.factorization_inj hm0 (Nat.mul_ne_zero hp.ne_zero hn0)
        ext q
        rw [Nat.factorization_mul hp.ne_zero hn0, Finsupp.add_apply, hp.factorization]
        by_cases hqp : q = p
        · subst hqp; simp [hdec]; omega
        · rw [Finsupp.single_eq_of_ne hqp, zero_add, hother q hqp]
      have hp2 := hp.two_le
      nlinarith
