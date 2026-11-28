import OMAReductions.R_Erdos977_erdos_977_variants_stewart_R1
import Mathlib

namespace OMA.Erdos977StewartH2

open Polynomial Finset Real ArithmeticFunction

/-- `Φ_n(2) > 0` for every positive integer `n`. -/
private lemma eval_cyclotomic_two_pos : ∀ n : ℕ, 0 < n → 0 < eval (2 : ℤ) (cyclotomic n ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    have hprod : ∏ d ∈ n.divisors, eval (2 : ℤ) (cyclotomic d ℤ) = (2 : ℤ) ^ n - 1 := by
      have h := congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)
      simpa [eval_prod] using h
    have hsplit : ∏ d ∈ n.divisors, eval (2 : ℤ) (cyclotomic d ℤ) =
        eval (2 : ℤ) (cyclotomic n ℤ) *
          ∏ d ∈ n.properDivisors, eval (2 : ℤ) (cyclotomic d ℤ) := by
      rw [← Nat.insert_self_properDivisors hn.ne', prod_insert (by simp)]
    have hprop_pos : 0 < ∏ d ∈ n.properDivisors, eval (2 : ℤ) (cyclotomic d ℤ) := by
      apply Finset.prod_pos
      intro d hd
      exact ih d (Nat.mem_properDivisors.mp hd).2 (Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd).1 hn)
    have hrhs_pos : (0 : ℤ) < (2 : ℤ) ^ n - 1 := by
      have : (2 : ℤ) ≤ (2 : ℤ) ^ n := by
        calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
          _ ≤ (2 : ℤ) ^ n := pow_le_pow_right₀ (by norm_num) hn
      omega
    rw [hsplit] at hprod
    nlinarith

/-- Lower bound `∏_{d=2}^n (1 - 2^{-d}) ≥ 1/2 + 2^{-n}` for all `n ≥ 1`. -/
private lemma prod_one_sub_inv_two_pow_ge :
    ∀ n : ℕ, 1 ≤ n → (1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ n ≤ ∏ d ∈ Icc 2 n, (1 - (2 : ℝ)⁻¹ ^ d) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp
    norm_num
  | succ k hk ih =>
    have hIcc : Icc 2 (k + 1) = insert (k + 1) (Icc 2 k) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [hIcc, prod_insert (by simp)]
    have hpow_pos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
    have hpow_le : (2 : ℝ)⁻¹ ^ (k + 1) ≤ 1 / 4 := by
      calc (2 : ℝ)⁻¹ ^ (k + 1) ≤ (2 : ℝ)⁻¹ ^ 2 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    have hfac_nonneg : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ (k + 1) := by linarith
    have hmul := mul_le_mul_of_nonneg_left ih hfac_nonneg
    have halg : (1 - (2 : ℝ)⁻¹ ^ (k + 1)) * ((1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ k) =
        (1 / 2 : ℝ) + (2 : ℝ)⁻¹ ^ (k + 1) + (2 : ℝ)⁻¹ ^ (k + 1) * (1 / 2 - (2 : ℝ)⁻¹ ^ k) := by
      rw [pow_succ]
      ring
    have hrem : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (k + 1) * (1 / 2 - (2 : ℝ)⁻¹ ^ k) := by
      apply mul_nonneg (by positivity)
      have : (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) hk
      linarith
    linarith

/-- `∏_{d=1}^n (1 - 2^{-d}) ≥ 1/4` for all `n ≥ 1`. -/
private lemma prod_one_sub_ge_quarter (n : ℕ) (hn : 1 ≤ n) :
    (1 / 4 : ℝ) ≤ ∏ d ∈ Icc 1 n, (1 - (2 : ℝ)⁻¹ ^ d) := by
  have hIcc : Icc 1 n = insert 1 (Icc 2 n) := by
    ext x
    simp only [mem_Icc, mem_insert]
    omega
  rw [hIcc, prod_insert (by simp)]
  have h2 := prod_one_sub_inv_two_pow_ge n hn
  have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

/-- Lower bound `2^φ(n) ≤ 4 * Φ_n(2)` for every `n ≥ 1`. -/
private lemma two_pow_totient_le_four_mul_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℝ) ^ n.totient ≤ 4 * ((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) := by
  let f : ℕ → ℝ := fun d =>
    if d = 0 then 0 else Real.log (((eval (2 : ℤ) (cyclotomic d ℤ) : ℤ) : ℝ) / (2 : ℝ) ^ d.totient)
  let g : ℕ → ℝ := fun m =>
    if m = 0 then 0 else Real.log (1 - (2 : ℝ)⁻¹ ^ m)
  have hsum : ∀ m : ℕ, ∑ d ∈ m.divisors, f d = g m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [f, g]
    · have hprod : ∏ d ∈ m.divisors, ((eval (2 : ℤ) (cyclotomic d ℤ) : ℤ) : ℝ) = (2 : ℝ) ^ m - 1 := by
        have h := congr_arg (fun z : ℤ => (z : ℝ))
          (congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hm ℤ))
        simpa [eval_prod] using h
      have htot : ∏ d ∈ m.divisors, (2 : ℝ) ^ d.totient = (2 : ℝ) ^ m := by
        rw [Finset.prod_pow_eq_pow_sum, Nat.sum_totient]
      have hlog_eq : ∑ d ∈ m.divisors, f d =
          Real.log (∏ d ∈ m.divisors, (((eval (2 : ℤ) (cyclotomic d ℤ) : ℤ) : ℝ) / (2 : ℝ) ^ d.totient)) := by
        rw [Real.log_prod]
        · apply Finset.sum_congr rfl
          intro d hd
          have hd0 : d ≠ 0 := (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hm).ne'
          simp [f, hd0]
        · intro d hd
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hm
          have hcp : (0 : ℝ) < ((eval (2 : ℤ) (cyclotomic d ℤ) : ℤ) : ℝ) := by
            exact_mod_cast eval_cyclotomic_two_pos d hdpos
          positivity
      rw [hlog_eq, Finset.prod_div_distrib, hprod, htot]
      have hdiv : ((2 : ℝ) ^ m - 1) / (2 : ℝ) ^ m = 1 - (2 : ℝ)⁻¹ ^ m := by
        rw [sub_div, div_self (by positivity), one_div, inv_pow]
      rw [hdiv]
      simp [g, hm.ne']
  have hmob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (f := f) (g := g)).mp (fun m _ => hsum m) n hn
  have hge_div : ∑ d ∈ n.divisors, Real.log (1 - (2 : ℝ)⁻¹ ^ d) ≤ f n := by
    rw [← hmob, Nat.sum_divisorsAntidiagonal' (f := fun a b => (moebius a : ℝ) * g b)]
    apply Finset.sum_le_sum
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn
    have hgd : g d = Real.log (1 - (2 : ℝ)⁻¹ ^ d) := by simp [g, hdpos.ne']
    rw [hgd]
    have hlog_neg : Real.log (1 - (2 : ℝ)⁻¹ ^ d) ≤ 0 := by
      apply Real.log_nonpos
      · have : (2 : ℝ)⁻¹ ^ d ≤ (2 : ℝ)⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) hdpos
        linarith
      · have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
        linarith
    have hmu_le : (moebius (n / d) : ℝ) ≤ 1 := by
      have h : moebius (n / d) ≤ 1 := by
        by_cases hs : Squarefree (n / d)
        · rw [ArithmeticFunction.moebius_apply_of_squarefree hs]
          rcases neg_one_pow_eq_or ℤ (cardFactors (n / d)) with h1 | h2 <;> omega
        · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
          omega
      exact_mod_cast h
    nlinarith
  have hge_Icc : ∑ d ∈ Icc 1 n, Real.log (1 - (2 : ℝ)⁻¹ ^ d) ≤
      ∑ d ∈ n.divisors, Real.log (1 - (2 : ℝ)⁻¹ ^ d) := by
    have hsub : n.divisors ⊆ Icc 1 n := by
      intro d hd
      rw [mem_Icc]
      exact ⟨Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn,
        Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1⟩
    rw [← Finset.sum_sdiff hsub]
    have hnonpos : ∑ d ∈ Icc 1 n \ n.divisors, Real.log (1 - (2 : ℝ)⁻¹ ^ d) ≤ 0 := by
      apply Finset.sum_nonpos
      intro d hd
      have hd1 : 1 ≤ d := (mem_Icc.mp (mem_sdiff.mp hd).1).1
      apply Real.log_nonpos
      · have : (2 : ℝ)⁻¹ ^ d ≤ (2 : ℝ)⁻¹ ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) hd1
        linarith
      · have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ d := by positivity
        linarith
    linarith
  have hprod_log : Real.log (1 / 4 : ℝ) ≤ ∑ d ∈ Icc 1 n, Real.log (1 - (2 : ℝ)⁻¹ ^ d) := by
    rw [← Real.log_prod]
    · exact Real.log_le_log (by norm_num) (prod_one_sub_ge_quarter n hn)
    · intro d hd
      have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
      have : (2 : ℝ)⁻¹ ^ d ≤ (2 : ℝ)⁻¹ ^ 1 :=
        pow_le_pow_of_le_one (by positivity) (by norm_num) hd1
      linarith
  have hlog_bound : Real.log (1 / 4 : ℝ) ≤
      Real.log (((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) / (2 : ℝ) ^ n.totient) := by
    have : f n = Real.log (((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) / (2 : ℝ) ^ n.totient) := by
      simp [f, (Nat.pos_of_ne_zero (by omega) : 0 < n).ne']
    linarith
  have hcpos : (0 : ℝ) < ((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) := by
    exact_mod_cast eval_cyclotomic_two_pos n hn
  have hratio : (1 / 4 : ℝ) ≤ ((eval (2 : ℤ) (cyclotomic n ℤ) : ℤ) : ℝ) / (2 : ℝ) ^ n.totient :=
    (Real.log_le_log_iff (by norm_num) (by positivity)).mp hlog_bound
  rw [le_div_iff₀ (by positivity)] at hratio
  linarith

/-- If a prime `p` divides `Φ_n(2)` and `p % n ≠ 1`, then `p ∣ n`. -/
private lemma prime_dvd_of_dvd_cyclotomic_not_mod_one {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hdvd : (p : ℤ) ∣ eval (2 : ℤ) (cyclotomic n ℤ)) (hmod : p % n ≠ 1) : p ∣ n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hphi_dvd : eval (2 : ℤ) (cyclotomic n ℤ) ∣ (2 : ℤ) ^ n - 1 := by
    have h : ∏ d ∈ n.divisors, eval (2 : ℤ) (cyclotomic d ℤ) = (2 : ℤ) ^ n - 1 := by
      simpa [eval_prod] using congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < n) ℤ)
    rw [← h]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)
  have hp_dvd_pow : (p : ℤ) ∣ (2 : ℤ) ^ n - 1 := hdvd.trans hphi_dvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : (2 : ℤ) ∣ (2 : ℤ) ^ n := dvd_pow_self 2 (by omega)
    have : (2 : ℤ) ∣ 1 := by
      have h1 := dvd_sub this hp_dvd_pow
      simpa using h1
    omega
  have h2ne0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    have := (Nat.dvd_prime Nat.prime_two).mp this
    rcases this with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have h2pow : (2 : ZMod p) ^ n = 1 := by
    have h0 : ((2 : ℤ) ^ n - 1 : ZMod p) = 0 := by
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ n - 1) p).mpr hp_dvd_pow
    exact sub_eq_zero.mp (by simpa using h0)
  set d := orderOf (2 : ZMod p) with hd_def
  have hd_dvd_n : d ∣ n := orderOf_dvd_of_pow_eq_one h2pow
  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd_n (by omega)
  have hd_ne_n : d ≠ n := by
    intro heq
    have hd_dvd_pm1 : d ∣ p - 1 := by
      apply orderOf_dvd_of_pow_eq_one
      exact ZMod.pow_card_sub_one_eq_one h2ne0
    rw [heq] at hd_dvd_pm1
    obtain ⟨k, hk⟩ := hd_dvd_pm1
    have hp_ge : 2 ≤ p := hp.two_le
    have hpm1 : p = n * k + 1 := by omega
    rw [hpm1, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega : 1 < n)] at hmod
    exact hmod rfl
  have hd_lt_n : d < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd_dvd_n) hd_ne_n
  -- In (ZMod p)[X], both (X^d - 1) and Φ_n(X) divide X^n - 1, and they are distinct factors in ∏_{k|n} Φ_k
  have hdiv_sub : d.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd (by omega) hd_dvd_n
  have hn_not_mem : n ∉ d.divisors := by
    intro hm
    exact absurd (Nat.le_of_dvd hd_pos (Nat.mem_divisors.mp hm).1) (not_le_of_gt hd_lt_n)
  have hsplit : (X ^ n - 1 : (ZMod p)[X]) =
      (X ^ d - 1) * (cyclotomic n (ZMod p) *
        ∏ k ∈ (n.divisors \ d.divisors).erase n, cyclotomic k (ZMod p)) := by
    rw [← prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < n) (ZMod p),
      ← prod_cyclotomic_eq_X_pow_sub_one hd_pos (ZMod p),
      ← Finset.prod_sdiff hdiv_sub]
    have hn_mem_sdiff : n ∈ n.divisors \ d.divisors :=
      mem_sdiff.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, hn_not_mem⟩
    rw [← Finset.mul_prod_erase _ _ hn_mem_sdiff]
    ring
  have hroot_d : (X - C (2 : ZMod p)) ∣ (X ^ d - 1 : (ZMod p)[X]) := by
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_pow, eval_X, eval_one,
      hd_def, pow_orderOf_eq_one, sub_self]
  have hroot_phi : (X - C (2 : ZMod p)) ∣ cyclotomic n (ZMod p) := by
    rw [dvd_iff_isRoot, IsRoot]
    have hmap : cyclotomic n (ZMod p) = (cyclotomic n ℤ).map (Int.castRingHom (ZMod p)) :=
      (Polynomial.map_cyclotomic n (Int.castRingHom (ZMod p))).symm
    rw [hmap, show (2 : ZMod p) = Int.castRingHom (ZMod p) 2 by simp, Polynomial.eval_map_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
  have hsq : (X - C (2 : ZMod p)) ^ 2 ∣ (X ^ n - 1 : (ZMod p)[X]) := by
    rw [hsplit, sq]
    exact mul_dvd_mul hroot_d (dvd_mul_of_dvd_left hroot_phi _)
  obtain ⟨Q, hQ⟩ := hsq
  have hderiv := congr_arg Polynomial.derivative hQ
  have hlhs : Polynomial.derivative (X ^ n - 1 : (ZMod p)[X]) = C (n : ZMod p) * X ^ (n - 1) := by
    simp [Polynomial.derivative_X_pow]
  have hrhs : eval (2 : ZMod p)
      (Polynomial.derivative ((X - C (2 : ZMod p)) ^ 2 * Q)) = 0 := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_pow]
  rw [hlhs] at hderiv
  have hev := congr_arg (eval (2 : ZMod p)) hderiv
  rw [hrhs] at hev
  simp only [eval_mul, eval_C, eval_pow, eval_X] at hev
  have hpow_ne : (2 : ZMod p) ^ (n - 1) ≠ 0 := pow_ne_zero _ h2ne0
  have hn0 : (n : ZMod p) = 0 := (mul_eq_zero.mp hev).resolve_right hpow_ne
  exact (ZMod.natCast_eq_zero_iff n p).mp hn0

/-- If an odd prime `p` divides both `n` and `Φ_n(2)`, then `p^2 ∤ Φ_n(2)`. -/
private lemma not_sq_dvd_cyclotomic_of_dvd_n {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hdvd_n : p ∣ n) (hdvd_phi : (p : ℤ) ∣ eval (2 : ℤ) (cyclotomic n ℤ)) :
    ¬ ((p : ℤ) ^ 2 ∣ eval (2 : ℤ) (cyclotomic n ℤ)) := by
  have hphi_dvd : eval (2 : ℤ) (cyclotomic n ℤ) ∣ (2 : ℤ) ^ n - 1 := by
    have h : ∏ d ∈ n.divisors, eval (2 : ℤ) (cyclotomic d ℤ) = (2 : ℤ) ^ n - 1 := by
      simpa [eval_prod] using congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < n) ℤ)
    rw [← h]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)
  have hp_dvd_pow : (p : ℤ) ∣ (2 : ℤ) ^ n - 1 := hdvd_phi.trans hphi_dvd
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : (2 : ℤ) ∣ (2 : ℤ) ^ n := dvd_pow_self 2 (by omega)
    have : (2 : ℤ) ∣ 1 := by
      have h1 := dvd_sub this hp_dvd_pow
      simp at h1
    omega
  set m := n / p with hm_def
  have hpm : m * p = n := Nat.div_mul_cancel hdvd_n
  have hm_pos : 0 < m := by
    have := hp.pos
    nlinarith
  have hm_lt : m < n := Nat.div_lt_self (by omega) hp.one_lt
  have hsub : m.divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd (by omega) ⟨p, hpm.symm⟩
  have hn_not_mem : n ∉ m.divisors := by
    intro h
    exact absurd (Nat.le_of_dvd hm_pos (Nat.mem_divisors.mp h).1) (not_le_of_gt hm_lt)
  -- Show Φ_n(2) ∣ ∑ j ∈ range p, (2^m)^j
  set y : ℤ := (2 : ℤ) ^ m with hy_def
  have hgeom : (y - 1) * (∑ j ∈ range p, y ^ j) = (2 : ℤ) ^ n - 1 := by
    rw [mul_geom_sum, ← pow_mul, hpm]
  have hprod_n : ∏ k ∈ n.divisors, eval (2 : ℤ) (cyclotomic k ℤ) = (2 : ℤ) ^ n - 1 := by
    have h := congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one (by omega : 0 < n) ℤ)
    simpa [eval_prod] using h
  have hprod_m : ∏ k ∈ m.divisors, eval (2 : ℤ) (cyclotomic k ℤ) = y - 1 := by
    have h := congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hm_pos ℤ)
    simpa [eval_prod, hy_def] using h
  have hquot : ∏ k ∈ n.divisors \ m.divisors, eval (2 : ℤ) (cyclotomic k ℤ) =
      ∑ j ∈ range p, y ^ j := by
    have hmul : (y - 1) * (∏ k ∈ n.divisors \ m.divisors, eval (2 : ℤ) (cyclotomic k ℤ)) =
        (y - 1) * (∑ j ∈ range p, y ^ j) := by
      rw [hgeom, ← hprod_n, ← hprod_m, mul_comm, Finset.prod_sdiff hsub]
    have hy1 : y - 1 ≠ 0 := by
      have : (2 : ℤ) ≤ y := by
        calc (2 : ℤ) = (2 : ℤ) ^ 1 := by ring
          _ ≤ (2 : ℤ) ^ m := pow_le_pow_right₀ (by norm_num) hm_pos
      omega
    exact mul_left_cancel₀ hy1 hmul
  have hphi_dvd_sum : eval (2 : ℤ) (cyclotomic n ℤ) ∣ ∑ j ∈ range p, y ^ j := by
    rw [← hquot]
    exact Finset.dvd_prod_of_mem _ (mem_sdiff.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩, hn_not_mem⟩)
  -- Show p ∣ y - 1 (since y^p = 2^n ≡ 1 (mod p) and y^p ≡ y (mod p))
  have hp_dvd_y1 : (p : ℤ) ∣ y - 1 := by
    have : Fact p.Prime := ⟨hp⟩
    have hy_pow : (y : ZMod p) ^ p = 1 := by
      have h0 : ((2 : ℤ) ^ n - 1 : ZMod p) = 0 := by
        simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd ((2 : ℤ) ^ n - 1) p).mpr hp_dvd_pow
      have h1 : (2 : ZMod p) ^ n = 1 := sub_eq_zero.mp (by simpa using h0)
      rw [hy_def]
      push_cast
      rw [← pow_mul, hpm]
      exact h1
    have hflt : (y : ZMod p) ^ p = (y : ZMod p) := ZMod.pow_card (y : ZMod p)
    have hy_eq : (y : ZMod p) = 1 := hflt.symm.trans hy_pow
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (y - 1) p).mp (by simp [hy_eq])
  obtain ⟨k, hk⟩ := hp_dvd_y1
  have hy_eq : y = 1 + (p : ℤ) * k := by linarith
  -- Compute ∑_{j < p} (1 + p*k)^j ≡ p (mod p^2)
  have hterm : ∀ j : ℕ, ((p : ℤ) ^ 2) ∣ (1 + (p : ℤ) * k) ^ j - (1 + (j : ℤ) * ((p : ℤ) * k)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q * (1 + (p : ℤ) * k) + (j : ℤ) * k ^ 2, ?_⟩
      have hpow : (1 + (p : ℤ) * k) ^ j = 1 + (j : ℤ) * ((p : ℤ) * k) + (p : ℤ) ^ 2 * q := by
        linarith
      rw [pow_succ, hpow]
      push_cast
      ring
  have hsum_mod : ((p : ℤ) ^ 2) ∣ (∑ j ∈ range p, y ^ j) - (p : ℤ) := by
    have h1 : ((p : ℤ) ^ 2) ∣
        ∑ j ∈ range p, (y ^ j - (1 + (j : ℤ) * ((p : ℤ) * k))) := by
      apply Finset.dvd_sum
      intro j _
      rw [hy_eq]
      exact hterm j
    have h2 : ∑ j ∈ range p, (1 + (j : ℤ) * ((p : ℤ) * k)) =
        (p : ℤ) + ((p : ℤ) * k) * (∑ j ∈ range p, (j : ℤ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
        ← Finset.sum_mul, mul_comm ((p : ℤ) * k)]
    have htri : (p : ℤ) ∣ ∑ j ∈ range p, (j : ℤ) := by
      have hnat : ∑ j ∈ range p, j = p * (p - 1) / 2 := Finset.sum_range_id p
      have hodd : 2 ∣ p - 1 := by
        have := hp.odd_of_ne_two hp2
        obtain ⟨r, hr⟩ := this
        exact ⟨r, by omega⟩
      obtain ⟨r, hr⟩ := hodd
      have hsum_eq : ∑ j ∈ range p, (j : ℤ) = (p : ℤ) * (r : ℤ) := by
        have hnat2 : ∑ j ∈ range p, j = p * r := by
          rw [hnat, hr, ← Nat.mul_assoc, Nat.mul_comm p 2, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by omega)]
        rw [← Nat.cast_sum, hnat2]
        push_cast
        rfl
      exact ⟨r, hsum_eq⟩
    obtain ⟨r, hr⟩ := htri
    have hrew : (∑ j ∈ range p, y ^ j) - (p : ℤ) =
        (∑ j ∈ range p, (y ^ j - (1 + (j : ℤ) * ((p : ℤ) * k)))) + (p : ℤ) ^ 2 * (k * r) := by
      rw [Finset.sum_sub_distrib, h2, hr]
      ring
    rw [hrew]
    exact dvd_add h1 (dvd_mul_right _ _)
  intro hsq_phi
  have hsq_sum : (p : ℤ) ^ 2 ∣ ∑ j ∈ range p, y ^ j := hsq_phi.trans hphi_dvd_sum
  have hsq_p : (p : ℤ) ^ 2 ∣ (p : ℤ) := by
    have := dvd_sub hsq_sum hsum_mod
    simpa using this
  have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hle := Int.le_of_dvd hp_pos hsq_p
  have hp_ge2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
  nlinarith

theorem main_proof : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H2 := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  set cZ : ℤ := eval (2 : ℤ) (cyclotomic n ℤ) with hcZ_def
  have hcZ_pos : 0 < cZ := eval_cyclotomic_two_pos n hn1
  set c : ℕ := cZ.toNat with hc_def
  have hc_cast : (c : ℤ) = cZ := Int.toNat_of_nonneg hcZ_pos.le
  have hc_pos : 0 < c := by omega
  have hpow_le_4c : 2 ^ n.totient ≤ 4 * c := by
    have hR := two_pow_totient_le_four_mul_cyclotomic n hn1
    have hR' : ((2 ^ n.totient : ℕ) : ℝ) ≤ ((4 * c : ℕ) : ℝ) := by
      push_cast
      have : (c : ℝ) = (cZ : ℝ) := by exact_mod_cast hc_cast
      rw [this]
      exact hR
    exact_mod_cast hR'
  -- c divides 2^n - 1
  have hc_dvd : c ∣ 2 ^ n - 1 := by
    have h : ∏ d ∈ n.divisors, eval (2 : ℤ) (cyclotomic d ℤ) = (2 : ℤ) ^ n - 1 := by
      simpa [eval_prod] using congr_arg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn1 ℤ)
    have hdvdZ : cZ ∣ (2 : ℤ) ^ n - 1 := by
      rw [hcZ_def, ← h]
      exact Finset.dvd_prod_of_mem _ (Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩)
    rw [← hc_cast] at hdvdZ
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hcast : ((2 ^ n - 1 : ℕ) : ℤ) = (2 : ℤ) ^ n - 1 := by
      rw [Nat.cast_sub h2n]; norm_num
    rw [← hcast] at hdvdZ
    exact Int.ofNat_dvd.mp hdvdZ
  have h2n1_ne : 2 ^ n - 1 ≠ 0 := by
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  -- Split c.primeFactors into (p % n = 1) and (p % n ≠ 1)
  have hc_fac : c = ∏ p ∈ c.primeFactors, p ^ padicValNat p c := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hc_pos.ne']
    rw [Finsupp.prod, Nat.support_factorization]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have : Fact p.Prime := ⟨hpp⟩
    rw [Nat.factorization_def c hpp]
  have hsplit : c = (∏ p ∈ c.primeFactors.filter (fun p => p % n ≠ 1), p ^ padicValNat p c) *
      (∏ p ∈ c.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p c) := by
    conv_lhs => rw [hc_fac]
    rw [← Finset.prod_filter_mul_prod_filter_not c.primeFactors (fun p => p % n ≠ 1)]
    congr 2
    ext p
    simp
  -- Part 1: non-(1 mod n) prime factors of c all divide n with exponent 1, so their product divides n
  have hbad_dvd_n : (∏ p ∈ c.primeFactors.filter (fun p => p % n ≠ 1), p ^ padicValNat p c) ∣ n := by
    have heq_p : ∏ p ∈ c.primeFactors.filter (fun p => p % n ≠ 1), p ^ padicValNat p c =
        ∏ p ∈ c.primeFactors.filter (fun p => p % n ≠ 1), p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hpc : p ∣ c := Nat.dvd_of_mem_primeFactors hp.1
      have hpcZ : (p : ℤ) ∣ cZ := by rw [← hc_cast]; exact Int.ofNat_dvd.mpr hpc
      have hpn : p ∣ n := prime_dvd_of_dvd_cyclotomic_not_mod_one hn hpp hpcZ hp.2
      have hnsq : ¬ ((p : ℤ) ^ 2 ∣ cZ) := not_sq_dvd_cyclotomic_of_dvd_n hn hpp hpn hpcZ
      have hnsqN : ¬ (p ^ 2 ∣ c) := fun h => hnsq (by rw [← hc_cast]; exact_mod_cast Int.ofNat_dvd.mpr h)
      have : Fact p.Prime := ⟨hpp⟩
      have hv_ge : 1 ≤ padicValNat p c := one_le_padicValNat_of_dvd hc_pos.ne' hpc
      have hv_le : padicValNat p c ≤ 1 := by
        by_contra! hgt
        apply hnsqN
        exact (padicValNat_dvd_iff_le hc_pos.ne').mpr hgt
      have hv1 : padicValNat p c = 1 := by omega
      rw [hv1, pow_one]
    rw [heq_p]
    have hsub : c.primeFactors.filter (fun p => p % n ≠ 1) ⊆ n.primeFactors := by
      intro p hp
      rw [mem_filter] at hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
      have hpc : p ∣ c := Nat.dvd_of_mem_primeFactors hp.1
      have hpcZ : (p : ℤ) ∣ cZ := by rw [← hc_cast]; exact Int.ofNat_dvd.mpr hpc
      have hpn : p ∣ n := prime_dvd_of_dvd_cyclotomic_not_mod_one hn hpp hpcZ hp.2
      exact Nat.mem_primeFactors.mpr ⟨hpp, hpn, by omega⟩
    exact (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans (Nat.prod_primeFactors_dvd n)
  have hbad_le : ∏ p ∈ c.primeFactors.filter (fun p => p % n ≠ 1), p ^ padicValNat p c ≤ n :=
    Nat.le_of_dvd (by omega) hbad_dvd_n
  -- Part 2: (1 mod n) prime factors of c are a subset of those of 2^n - 1 with ≤ valuation
  have hgood_le : ∏ p ∈ c.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p c ≤
      ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p (2 ^ n - 1) := by
    have hsub : c.primeFactors.filter (fun p => p % n = 1) ⊆
        (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1) := by
      intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp.1,
        (Nat.dvd_of_mem_primeFactors hp.1).trans hc_dvd, h2n1_ne⟩, hp.2⟩
    have hle1 : ∏ p ∈ c.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p c ≤
        ∏ p ∈ c.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p (2 ^ n - 1) := by
      apply Finset.prod_le_prod'
      intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1
      have : Fact p.Prime := ⟨hpp⟩
      exact Nat.pow_le_pow_right hpp.pos ((padicValNat_dvd_iff_le h2n1_ne).mp
        (((padicValNat_dvd_iff_le hc_pos.ne').mpr le_rfl).trans hc_dvd))
    have hle2 : ∏ p ∈ c.primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p (2 ^ n - 1) ≤
        ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1), p ^ padicValNat p (2 ^ n - 1) := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hsub
      intro p hp _
      exact Nat.one_le_pow _ _ (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).pos
    exact hle1.trans hle2
  have hc_le : c ≤ n * ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1),
      p ^ padicValNat p (2 ^ n - 1) := by
    rw [hsplit]
    exact Nat.mul_le_mul hbad_le hgood_le
  have h1 : 2 ^ n.totient ≤ 4 * (n * ∏ p ∈ (2 ^ n - 1).primeFactors.filter (fun p => p % n = 1),
      p ^ padicValNat p (2 ^ n - 1)) := hpow_le_4c.trans (Nat.mul_le_mul_left 4 hc_le)
  simpa [Nat.mul_assoc] using h1

end OMA.Erdos977StewartH2

theorem OMA.solution : OMA.R_Erdos977_erdos_977_variants_stewart_R1.H2 :=
  OMA.Erdos977StewartH2.main_proof
