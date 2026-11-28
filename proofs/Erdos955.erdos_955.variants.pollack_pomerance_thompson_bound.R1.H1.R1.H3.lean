import OMAReductions.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1
import Mathlib

open Filter Topology Finset Real ArithmeticFunction
open scoped Classical ArithmeticFunction.sigma

private lemma s_eq_sum_properDivisors {n : ℕ} (hn : 0 < n) :
    Erdos955.s n = ∑ t ∈ n.properDivisors, t := by
  have hsig : σ 1 n = ∑ t ∈ n.divisors, t := by
    simp [sigma_one_apply]
  have hins := Nat.insert_self_properDivisors hn.ne'
  have hsum : ∑ t ∈ n.divisors, t = n + ∑ t ∈ n.properDivisors, t := by
    rw [← hins, sum_insert Nat.self_notMem_properDivisors]
  unfold Erdos955.s
  omega

private lemma s_add_self {n : ℕ} (hn : 0 < n) : Erdos955.s n + n = σ 1 n := by
  have hle : n ≤ σ 1 n := by
    rw [sigma_one_apply]
    exact single_le_sum (f := id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne'⟩)
  unfold Erdos955.s
  omega

private lemma s_mul_of_coprime {d e : ℕ} (hd : 0 < d) (he : 0 < e) (hcop : d.Coprime e) :
    Erdos955.s (d * e) = σ 1 d * Erdos955.s e + Erdos955.s d * e := by
  have hmul : σ 1 (d * e) = σ 1 d * σ 1 e :=
    isMultiplicative_sigma.map_mul_of_coprime hcop
  have h1 := s_add_self (Nat.mul_pos hd he)
  have h2 := s_add_self hd
  have h3 := s_add_self he
  nlinarith

private lemma s_le_sq {n : ℕ} (hn : 0 < n) : Erdos955.s n ≤ n ^ 2 := by
  rw [s_eq_sum_properDivisors hn]
  have hsub : n.properDivisors ⊆ Icc 1 n := fun t ht =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_properDivisors ht, (Nat.mem_properDivisors.mp ht).2.le⟩
  calc ∑ t ∈ n.properDivisors, t
      ≤ ∑ _t ∈ n.properDivisors, n :=
        sum_le_sum fun t ht => (Nat.mem_properDivisors.mp ht).2.le
    _ = n.properDivisors.card * n := by simp
    _ ≤ (Icc 1 n).card * n := Nat.mul_le_mul_right n (card_le_card hsub)
    _ = n ^ 2 := by rw [Nat.card_Icc]; simp [sq]

private lemma card_mod_le {M v : ℕ} (hv : 0 < v) {S : Finset ℕ}
    (hS : ∀ y ∈ S, y ≤ M) (hmod : ∀ y ∈ S, ∀ z ∈ S, y % v = z % v) :
    S.card ≤ M / v + 1 := by
  have hsub : S.image (fun y => y / v) ⊆ range (M / v + 1) := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hq
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hS y hy)))
  have hinj : Set.InjOn (fun y => y / v) (S : Set ℕ) := by
    intro y hy z hz hdiv
    have hm := hmod y hy z hz
    have e1 := Nat.div_add_mod y v
    have e2 := Nat.div_add_mod z v
    dsimp at hdiv
    rw [hdiv, hm] at e1
    exact e1.symm.trans e2
  rw [← card_image_of_injOn hinj]
  exact (card_le_card hsub).trans (by rw [card_range])

private lemma divisor_bound_ev :
    ∀ᶠ x : ℕ in atTop,
      let L := Real.log (x : ℝ)
      let ℓ := Real.log L
      ∀ t : ℕ, 1 ≤ t → t ≤ x ^ 2 →
        (t.divisors.card : ℝ) ≤ Real.exp (4 * L / ℓ) := by
  have hL_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hℓ_top : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_top
  -- Use exponent 1/8 so 2 * L^(1/4) * sqrt L ≤ L directly
  have hsmall_clean : ∀ᶠ L : ℝ in atTop,
      Real.sqrt L * Real.log (4 * L) * Real.log L ≤ L := by
    have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)
    have h2 : ∀ᶠ L : ℝ in atTop, Real.log L ≤ L ^ (1 / 8 : ℝ) := by
      filter_upwards [h1.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (4 : ℝ)] with L hL hL4
      have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      have hrp0 : 0 ≤ L ^ (1 / 8 : ℝ) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrp0, one_mul] at hL
      exact hL
    filter_upwards [h2, eventually_ge_atTop (16 : ℝ)] with L hL2 hL16
    have hL0 : 0 < L := by linarith
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
    have hlog4 : Real.log (4 * L) ≤ 2 * Real.log L := by
      rw [Real.log_mul (by norm_num) hL0.ne']
      linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ L)]
    have h18 : (L ^ (1 / 8 : ℝ)) ^ 2 = L ^ (1 / 4 : ℝ) := by
      rw [sq, ← Real.rpow_add hL0]; norm_num
    have h2le : (2 : ℝ) ≤ L ^ (1 / 4 : ℝ) := by
      have h16 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
          ← Real.rpow_mul (by norm_num)]
        norm_num
      rw [h16]
      exact Real.rpow_le_rpow (by norm_num) hL16 (by norm_num)
    have hcombine : Real.sqrt L * (2 * L ^ (1 / 4 : ℝ)) ≤ L := by
      calc Real.sqrt L * (2 * L ^ (1 / 4 : ℝ))
          ≤ Real.sqrt L * (L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ)) := by
            gcongr
        _ = L ^ (1 / 2 : ℝ) * (L ^ (1 / 4 : ℝ) * L ^ (1 / 4 : ℝ)) := by rw [Real.sqrt_eq_rpow]
        _ = L ^ ((1 / 2 : ℝ) + ((1 / 4 : ℝ) + (1 / 4 : ℝ))) := by
            rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
        _ = L := by
            rw [show (1 / 2 : ℝ) + ((1 / 4 : ℝ) + (1 / 4 : ℝ)) = 1 by norm_num, Real.rpow_one]
    have hsq : (Real.log L) ^ 2 ≤ L ^ (1 / 4 : ℝ) := by
      rw [← h18]
      exact pow_le_pow_left₀ hlog0 hL2 2
    calc Real.sqrt L * Real.log (4 * L) * Real.log L
        ≤ Real.sqrt L * (2 * Real.log L) * Real.log L :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog4 (Real.sqrt_nonneg L)) hlog0
      _ = Real.sqrt L * (2 * (Real.log L) ^ 2) := by ring
      _ ≤ Real.sqrt L * (2 * L ^ (1 / 4 : ℝ)) := by
          gcongr
      _ ≤ L := hcombine
  filter_upwards [hL_top.eventually hsmall_clean, hL_top.eventually (eventually_ge_atTop (16 : ℝ)),
    hℓ_top.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop 2] with x hx_small hL16 hℓ2 hx2
  intro L ℓ t ht1 htx2
  have hL_pos : 0 < L := by dsimp [L]; linarith
  have hℓ_pos : 0 < ℓ := by dsimp [ℓ]; linarith
  have ht0 : t ≠ 0 := by omega
  have hcard : (t.divisors.card : ℝ) =
      ∏ p ∈ t.primeFactors, ((t.factorization p : ℝ) + 1) := by
    have h := Nat.card_divisors ht0
    have hR : (t.divisors.card : ℝ) = ((∏ p ∈ t.primeFactors, (t.factorization p + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hR, Nat.cast_prod]
    apply prod_congr rfl
    intro p _
    push_cast
    rfl
  rw [hcard]
  let S1 := t.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ Real.sqrt L)
  let S2 := t.primeFactors.filter (fun p : ℕ => Real.sqrt L < (p : ℝ))
  have hsplit : (∏ p ∈ t.primeFactors, ((t.factorization p : ℝ) + 1)) =
      (∏ p ∈ S1, ((t.factorization p : ℝ) + 1)) *
      (∏ p ∈ S2, ((t.factorization p : ℝ) + 1)) := by
    have h1 := prod_filter_mul_prod_filter_not t.primeFactors (fun p : ℕ => (p : ℝ) ≤ Real.sqrt L)
      (fun p : ℕ => ((t.factorization p : ℝ) + 1))
    have h2 : S2 = t.primeFactors.filter (fun p : ℕ => ¬ (p : ℝ) ≤ Real.sqrt L) := by
      ext p; simp [S2, not_le]
    rw [← h2] at h1
    exact h1.symm
  rw [hsplit]
  -- Bound on S1
  have hS1_card : (S1.card : ℝ) ≤ Real.sqrt L := by
    have hsub : S1 ⊆ Icc 1 ⌊Real.sqrt L⌋₊ := by
      intro p hp
      obtain ⟨hpf, hple⟩ := mem_filter.mp hp
      exact mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpf).pos, Nat.le_floor hple⟩
    have h1 : S1.card ≤ ⌊Real.sqrt L⌋₊ := by
      simpa [Nat.card_Icc] using card_le_card hsub
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (Real.sqrt_nonneg L))
  have hS1_prod : (∏ p ∈ S1, ((t.factorization p : ℝ) + 1)) ≤ Real.exp (L / ℓ) := by
    have hterm : ∀ p ∈ S1, ((t.factorization p : ℝ) + 1) ≤ 4 * L := by
      intro p hp
      have hpf : p ∈ t.primeFactors := (mem_filter.mp hp).1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpf
      have hpow_dvd : p ^ t.factorization p ∣ t := Nat.ordProj_dvd t p
      have hpow_le : (p ^ t.factorization p : ℕ) ≤ x ^ 2 :=
        (Nat.le_of_dvd (by omega) hpow_dvd).trans htx2
      have h2_le : (2 : ℝ) ^ t.factorization p ≤ (x : ℝ) ^ 2 := by
        have h1 : 2 ^ t.factorization p ≤ p ^ t.factorization p :=
          Nat.pow_le_pow_left hpp.two_le _
        exact_mod_cast h1.trans hpow_le
      have hlog : (t.factorization p : ℝ) * Real.log 2 ≤ 2 * L := by
        have h := Real.log_le_log (by positivity) h2_le
        rw [Real.log_pow, Real.log_pow] at h
        push_cast at h
        exact h
      have hlog2 : (0.69 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      nlinarith
    have h4L_pos : 0 < 4 * L := by positivity
    calc ∏ p ∈ S1, ((t.factorization p : ℝ) + 1)
        ≤ ∏ _p ∈ S1, (4 * L) := prod_le_prod (fun _ _ => by positivity) hterm
      _ = (4 * L) ^ S1.card := by simp
      _ = Real.exp ((S1.card : ℝ) * Real.log (4 * L)) := by
          rw [Real.exp_nat_mul, Real.exp_log h4L_pos]
      _ ≤ Real.exp (L / ℓ) := by
          apply Real.exp_le_exp.mpr
          rw [le_div_iff₀ hℓ_pos]
          have hlog4_pos : 0 ≤ Real.log (4 * L) := Real.log_nonneg (by linarith)
          calc (S1.card : ℝ) * Real.log (4 * L) * ℓ
              ≤ Real.sqrt L * Real.log (4 * L) * ℓ := by gcongr
            _ ≤ L := hx_small
  -- Bound on S2
  have hS2_prod : (∏ p ∈ S2, ((t.factorization p : ℝ) + 1)) ≤ Real.exp (3 * L / ℓ) := by
    have hb_le : ∀ b : ℕ, ((b : ℝ) + 1) ≤ (2 : ℝ) ^ b := by
      intro b
      induction b with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ, Nat.cast_succ]
        have : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
        linarith
    have hprod_le_2 : (∏ p ∈ S2, ((t.factorization p : ℝ) + 1)) ≤
        (2 : ℝ) ^ (∑ p ∈ S2, t.factorization p) := by
      calc ∏ p ∈ S2, ((t.factorization p : ℝ) + 1)
          ≤ ∏ p ∈ S2, (2 : ℝ) ^ t.factorization p :=
            prod_le_prod (fun _ _ => by positivity) (fun p _ => hb_le _)
        _ = (2 : ℝ) ^ (∑ p ∈ S2, t.factorization p) := by rw [← prod_pow_eq_pow_sum]
    -- Bound ∑_{p ∈ S2} factorization p ≤ 4 * L / ℓ
    have hpow_prod : (Real.sqrt L) ^ (∑ p ∈ S2, t.factorization p) ≤ (x : ℝ) ^ 2 := by
      rw [← prod_pow_eq_pow_sum]
      have hle1 : (∏ p ∈ S2, (Real.sqrt L) ^ t.factorization p) ≤
          ∏ p ∈ S2, (p : ℝ) ^ t.factorization p := by
        apply prod_le_prod (fun _ _ => by positivity)
        intro p hp
        exact pow_le_pow_left₀ (Real.sqrt_nonneg L) (mem_filter.mp hp).2.le _
      have hle2 : (∏ p ∈ S2, p ^ t.factorization p) ≤ t := by
        have hdvd : (∏ p ∈ S2, p ^ t.factorization p) ∣ ∏ p ∈ t.primeFactors, p ^ t.factorization p :=
          prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
        have hdvd' : (∏ p ∈ S2, p ^ t.factorization p) ∣ t :=
          hdvd.trans (by rw [← Nat.prod_primeFactors_pow_factorization ht0])
        exact Nat.le_of_dvd (by omega : 0 < t) hdvd'
      have hle2R : (∏ p ∈ S2, (p : ℝ) ^ t.factorization p) ≤ (x : ℝ) ^ 2 := by
        have hcast : ((∏ p ∈ S2, p ^ t.factorization p : ℕ) : ℝ) ≤ ((x ^ 2 : ℕ) : ℝ) :=
          Nat.cast_le.mpr (hle2.trans htx2)
        push_cast at hcast
        exact hcast
      exact hle1.trans hle2R
    have hsum_le : ((∑ p ∈ S2, t.factorization p : ℕ) : ℝ) ≤ 4 * L / ℓ := by
      have hsq_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL_pos
      have hlog := Real.log_le_log (pow_pos hsq_pos _) hpow_prod
      rw [Real.log_pow, Real.log_sqrt hL_pos.le, Real.log_pow] at hlog
      rw [le_div_iff₀ hℓ_pos]
      dsimp only [L, ℓ] at *
      linarith
    have hlog2_le : Real.log 2 ≤ 3 / 4 := by
      have := Real.log_two_lt_d9
      linarith
    calc ∏ p ∈ S2, ((t.factorization p : ℝ) + 1)
        ≤ (2 : ℝ) ^ (∑ p ∈ S2, t.factorization p) := hprod_le_2
      _ = Real.exp (((∑ p ∈ S2, t.factorization p : ℕ) : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (3 * L / ℓ) := by
          apply Real.exp_le_exp.mpr
          calc ((∑ p ∈ S2, t.factorization p : ℕ) : ℝ) * Real.log 2
              ≤ (4 * L / ℓ) * (3 / 4) :=
                mul_le_mul hsum_le hlog2_le (Real.log_nonneg (by norm_num)) (by positivity)
            _ = 3 * L / ℓ := by ring
  calc (∏ p ∈ S1, ((t.factorization p : ℝ) + 1)) *
        (∏ p ∈ S2, ((t.factorization p : ℝ) + 1))
      ≤ Real.exp (L / ℓ) * Real.exp (3 * L / ℓ) :=
        mul_le_mul hS1_prod hS2_prod (prod_nonneg fun _ _ => by positivity) (Real.exp_pos _).le
    _ = Real.exp (4 * L / ℓ) := by rw [← Real.exp_add]; congr 1; ring

set_option maxHeartbeats 1200000 in
theorem OMA.solution :
    OMA.R_Erdos955_erdos_955_variants_pollack_pomerance_thompson_bound_R1_H1_R1.H3 := by
  classical
  intro ε hε δ hδ
  have hL_top : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hℓ_top : Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL_top
  -- Eventually ε x ≤ 1 / 40 and 1 / ℓ ≤ 1 / 40, so η ≤ 1 / 40
  have hε_small : ∀ᶠ x : ℕ in atTop, ε x ≤ 1 / 40 :=
    hε.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 40))
  have hℓ_ge40 : ∀ᶠ x : ℕ in atTop, (40 : ℝ) ≤ Real.log (Real.log (x : ℝ)) :=
    hℓ_top.eventually (eventually_ge_atTop 40)
  -- Eventually 2 * (1 + L)^2 / exp(L / ℓ) ≤ δ / 2
  have hexp_dom : ∀ᶠ L : ℝ in atTop,
      2 * (1 + L) ^ 2 ≤ (δ / 2) * Real.exp (L / Real.log L) := by
    have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : ∀ᶠ L : ℝ in atTop, Real.log L ≤ L ^ (1 / 2 : ℝ) := by
      filter_upwards [h1.bound (show (0 : ℝ) < 1 by norm_num), eventually_ge_atTop (4 : ℝ)] with L hL hL4
      have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
      have hrp0 : 0 ≤ L ^ (1 / 2 : ℝ) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrp0, one_mul] at hL
      exact hL
    have h3 : ∀ᶠ L : ℝ in atTop, 2 * (1 + L) ^ 2 ≤ (δ / 2) * Real.exp (Real.sqrt L) := by
      filter_upwards [eventually_ge_atTop (max 4 ((1920 / δ) ^ 2))] with L hL
      have hL4 : 4 ≤ L := (le_max_left _ _).trans hL
      have hLu : (1920 / δ) ^ 2 ≤ L := (le_max_right _ _).trans hL
      have hu_ge : 1920 / δ ≤ Real.sqrt L := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 1920 / δ)]
        exact Real.sqrt_le_sqrt hLu
      have hu0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
      have hexp5 : Real.sqrt L ^ 5 / (Nat.factorial 5 : ℝ) ≤ Real.exp (Real.sqrt L) :=
        Real.pow_div_factorial_le_exp (Real.sqrt L) hu0 5
      have hsq4 : Real.sqrt L ^ 4 = L ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (by linarith)]
      have hL1 : 2 * (1 + L) ^ 2 ≤ 8 * L ^ 2 := by nlinarith
      have hfac5 : (Nat.factorial 5 : ℝ) = 120 := by norm_num
      rw [hfac5] at hexp5
      have h5 : Real.sqrt L ^ 5 = Real.sqrt L * L ^ 2 := by
        rw [pow_succ', hsq4]
      rw [h5] at hexp5
      have hδu : 1920 ≤ δ * Real.sqrt L := by linarith [(div_le_iff₀ hδ).mp hu_ge]
      have h8 : 8 * L ^ 2 ≤ (δ / 2) * (Real.sqrt L * L ^ 2 / 120) := by
        have : 1920 * L ^ 2 ≤ (δ * Real.sqrt L) * L ^ 2 :=
          mul_le_mul_of_nonneg_right hδu (sq_nonneg L)
        linarith
      exact hL1.trans (h8.trans (mul_le_mul_of_nonneg_left hexp5 (by positivity)))
    filter_upwards [h2, h3, eventually_ge_atTop (4 : ℝ)] with L hL2 hL3 hL4
    have hL0 : 0 < L := by linarith
    have hlog0 : 0 < Real.log L := Real.log_pos (by linarith)
    have hdiv : Real.sqrt L ≤ L / Real.log L := by
      rw [le_div_iff₀ hlog0]
      calc Real.sqrt L * Real.log L
          ≤ Real.sqrt L * L ^ (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hL2 (Real.sqrt_nonneg L)
        _ = Real.sqrt L * Real.sqrt L := by rw [Real.sqrt_eq_rpow]
        _ = L := Real.mul_self_sqrt hL0.le
    exact hL3.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdiv) (by positivity))
  -- Eventually 2 ≤ δ * x^(1/4) so ⌊δ * x^(1/2 - ε x)⌋₊ ≥ (δ / 2) * x^(1/2 - ε x)
  have hK_large : ∀ᶠ x : ℕ in atTop, 2 ≤ δ * (x : ℝ) ^ (1 / 4 : ℝ) := by
    have ht : Tendsto (fun x : ℕ => δ * (x : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
      Tendsto.const_mul_atTop hδ ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
    exact ht.eventually (eventually_ge_atTop 2)
  -- Proof of L < exp(20 * L / log L) using (log L)^2 < 20 * L (since log L ≤ 2 * sqrt L):
  have hL_lt_X20' : ∀ᶠ L : ℝ in atTop, L < Real.exp (20 * L / Real.log L) := by
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with L hL4
    have hL0 : 0 < L := by linarith
    have hlog0 : 0 < Real.log L := Real.log_pos (by linarith)
    have hsq_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
    have hlog_sq : Real.log L ≤ 2 * Real.sqrt L := by
      have h1 : Real.log (Real.sqrt L) ≤ Real.sqrt L := by
        linarith [Real.log_le_sub_one_of_pos hsq_pos]
      rw [Real.log_sqrt hL0.le] at h1
      linarith
    have hsq_lt : (Real.log L) ^ 2 < 20 * L := by
      have h1 : (Real.log L) ^ 2 ≤ (2 * Real.sqrt L) ^ 2 := pow_le_pow_left₀ hlog0.le hlog_sq 2
      rw [mul_pow, Real.sq_sqrt hL0.le] at h1
      linarith
    have hlt : Real.log L < 20 * L / Real.log L := by
      rw [lt_div_iff₀ hlog0]
      nlinarith [hsq_lt]
    conv_lhs => rw [← Real.exp_log hL0]
    exact Real.exp_lt_exp.mpr hlt
  filter_upwards [divisor_bound_ev, hε_small, hℓ_ge40, hL_top.eventually hexp_dom,
    hK_large, hL_top.eventually hL_lt_X20', eventually_ge_atTop 16] with
    x hdiv hε40 hℓ40 hexp_d hK2 hL_X20 hx16
  intro η window other good
  set L : ℝ := Real.log (x : ℝ) with hL_def
  set ℓ : ℝ := Real.log L with hℓ_def
  have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (show 0 < x by omega)
  have hx_gt1 : (1 : ℝ) < (x : ℝ) := by exact_mod_cast (show 1 < x by omega)
  have hL_pos : 0 < L := Real.log_pos hx_gt1
  have hℓ_pos : 0 < ℓ := by linarith
  have hη_ge_inv : 1 / ℓ ≤ η := le_max_right _ _
  have hη_ge_ε : ε x ≤ η := le_max_left _ _
  have hη_pos : 0 < η := lt_of_lt_of_le (by positivity) hη_ge_inv
  have hη_le : η ≤ 1 / 40 := max_le hε40 (by rw [div_le_iff₀ hℓ_pos]; linarith)
  set X : ℝ := (x : ℝ) ^ η with hX_def
  set D : ℝ := (x : ℝ) ^ ((1 / 2 : ℝ) - 10 * η) with hD_def
  have hX_pos : 0 < X := Real.rpow_pos_of_pos hx_pos _
  have hD_pos : 0 < D := Real.rpow_pos_of_pos hx_pos _
  have hX_ge_exp : Real.exp (L / ℓ) ≤ X := by
    rw [hX_def, Real.rpow_def_of_pos hx_pos, ← hL_def]
    apply Real.exp_le_exp.mpr
    calc L / ℓ = (1 / ℓ) * L := by ring
      _ ≤ η * L := mul_le_mul_of_nonneg_right hη_ge_inv hL_pos.le
      _ = L * η := by ring
  have hX_gt1 : 1 < X := by
    have : 1 < Real.exp (L / ℓ) := Real.one_lt_exp_iff.mpr (by positivity)
    linarith
  have hD_ge1 : 1 ≤ D := by
    rw [hD_def]
    exact Real.one_le_rpow hx_gt1.le (by linarith)
  have hdiv_X4 : ∀ t : ℕ, 1 ≤ t → t ≤ x ^ 2 → (t.divisors.card : ℝ) ≤ X ^ 4 := by
    intro t ht1 htx2
    have h1 := hdiv t ht1 htx2
    have h2 : Real.exp (4 * L / ℓ) = (Real.exp (L / ℓ)) ^ 4 := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [h2] at h1
    exact h1.trans (pow_le_pow_left₀ (Real.exp_pos _).le hX_ge_exp 4)
  -- Choose K = ⌊δ * x^(1/2 - ε x)⌋₊
  let K : ℕ := ⌊δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x)⌋₊
  refine ⟨K, ?_, ?_⟩
  · -- x^(1/2 + ε x) * K ≤ δ * x
    have hK_le : (K : ℝ) ≤ δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) :=
      Nat.floor_le (by positivity)
    calc (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * (K : ℝ)
        ≤ (x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * (δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x)) :=
          mul_le_mul_of_nonneg_left hK_le (by positivity)
      _ = δ * ((x : ℝ) ^ ((1 / 2 : ℝ) + ε x) * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x)) := by ring
      _ = δ * (x : ℝ) ^ (((1 / 2 : ℝ) + ε x) + ((1 / 2 : ℝ) - ε x)) := by
          rw [← Real.rpow_add hx_pos]
      _ = δ * (x : ℝ) := by norm_num
  · -- Uniform fiber bound for every a > 0
    intro a ha
    let F := good.filter (fun n => Erdos955.s n = a)
    change F.card ≤ K
    by_cases hFempty : F = ∅
    · rw [hFempty, card_empty]; exact Nat.zero_le K
    have hFne : F.Nonempty := nonempty_iff_ne_empty.mpr hFempty
    obtain ⟨n0, hn0⟩ := hFne
    have hn0_good : n0 ∈ good := (mem_filter.mp hn0).1
    have hn0_s : Erdos955.s n0 = a := (mem_filter.mp hn0).2
    have hn0_Icc : n0 ∈ Icc 1 x := (mem_filter.mp hn0_good).1
    have ha_le_x2 : a ≤ x ^ 2 := by
      rw [← hn0_s]
      exact (s_le_sq (mem_Icc.mp hn0_Icc).1).trans (Nat.pow_le_pow_left (mem_Icc.mp hn0_Icc).2 2)
    have htau_a : (a.divisors.card : ℝ) ≤ X ^ 4 := hdiv_X4 a ha ha_le_x2
    -- Define the canonical split d(n) = sup {d ∈ n.divisors | d ≤ √x}
    let splitD' (n : ℕ) : ℕ :=
      (n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.sqrt (x : ℝ))).sup id
    have hsplit_props : ∀ n ∈ F,
        let d := splitD' n
        let e := n / d
        let g := Nat.gcd (σ 1 d) (Erdos955.s d)
        d ∈ n.divisors ∧ (d : ℝ) ≤ D ∧ 1 < d ∧ d * e = n ∧ 1 < e ∧ d.Coprime e ∧
        (d : ℝ) / L ≤ (Erdos955.s d : ℝ) ∧ (Erdos955.s e : ℝ) ≤ D * X ^ 4 ∧
        g ∣ a ∧ g ∣ d ∧ 0 < g ∧
        a = σ 1 d * Erdos955.s e + Erdos955.s d * e := by
      intro n hn
      have hn_good : n ∈ good := (mem_filter.mp hn).1
      have hn_sa : Erdos955.s n = a := (mem_filter.mp hn).2
      obtain ⟨hn_Icc, hn_nw, hn_no⟩ := mem_filter.mp hn_good
      have hn1 : 1 ≤ n := (mem_Icc.mp hn_Icc).1
      have hnx : n ≤ x := (mem_Icc.mp hn_Icc).2
      have hn0' : n ≠ 0 := by omega
      dsimp only [other] at hn_no
      push Not at hn_no
      obtain ⟨⟨q0, hq0_p, hq0_dvd, hq0_le⟩, hno_pow, hnsq⟩ := hn_no
      -- d = splitD' n is attained in S = n.divisors.filter (d ≤ √x)
      let S : Finset ℕ := n.divisors.filter (fun d : ℕ => (d : ℝ) ≤ Real.sqrt (x : ℝ))
      have h1S : 1 ∈ S := mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn0', by
        simpa using Real.one_le_sqrt.mpr hx_gt1.le⟩
      have hSne : S.Nonempty := ⟨1, h1S⟩
      obtain ⟨d0, hd0S, hd0max⟩ := S.exists_max_image id hSne
      have hd_eq : splitD' n = d0 := by
        apply le_antisymm
        · exact Finset.sup_le fun y hy => hd0max y hy
        · exact Finset.le_sup (f := id) hd0S
      let d := splitD' n
      have hdS : d ∈ S := by
        change splitD' n ∈ S
        rw [hd_eq]
        exact hd0S
      have hd_div : d ∈ n.divisors := (mem_filter.mp hdS).1
      have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd_div
      have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd_div
      have hd_le_sq : (d : ℝ) ≤ Real.sqrt (x : ℝ) := (mem_filter.mp hdS).2
      -- d ≤ D (since n ∉ window and d ≤ √x < x^(1/2 + 10η))
      have hsqrt_lt : Real.sqrt (x : ℝ) < (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_lt_rpow_of_exponent_lt hx_gt1 (by linarith)
      have hd_le_D : (d : ℝ) ≤ D := by
        by_contra hgt
        push_neg at hgt
        exact hn_nw ⟨d, hd_div, hgt, hd_le_sq.trans_lt hsqrt_lt⟩
      -- e = n / d > 1
      let e := n / d
      have hde : d * e = n := Nat.mul_div_cancel' hd_dvd
      have hsq_lt_n : Real.sqrt (x : ℝ) < (n : ℝ) := by
        rw [Real.sqrt_lt' (by positivity)]
        exact_mod_cast hnsq
      have hd_lt_n : d < n := by
        have : (d : ℝ) < (n : ℝ) := hd_le_sq.trans_lt hsq_lt_n
        exact_mod_cast this
      have he_gt1 : 1 < e := by
        by_contra hle
        have : e ≤ 1 := by omega
        nlinarith [hde, hd_pos]
      -- For every prime p ∣ e: d * p ≥ x^(1/2 + 10η) and p ≥ X^20
      have hprime_e : ∀ p : ℕ, p.Prime → p ∣ e →
          (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) ≤ (d : ℝ) * (p : ℝ) ∧ X ^ 20 ≤ (p : ℝ) := by
        intro p hp hpe
        have hdp_dvd : d * p ∣ n := hde ▸ Nat.mul_dvd_mul_left d hpe
        have hdp_div : d * p ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdp_dvd, hn0'⟩
        have hdp_gt_sq : Real.sqrt (x : ℝ) < ((d * p : ℕ) : ℝ) := by
          by_contra hle
          push_neg at hle
          have hmem : d * p ∈ S := mem_filter.mpr ⟨hdp_div, hle⟩
          have hle_d : d * p ≤ d := by
            have := hd0max (d * p) hmem
            dsimp at this
            omega
          have : d < d * p := lt_mul_of_one_lt_right hd_pos hp.one_lt
          omega
        have hD_lt_sq : D < Real.sqrt (x : ℝ) := by
          rw [hD_def, Real.sqrt_eq_rpow]
          exact Real.rpow_lt_rpow_of_exponent_lt hx_gt1 (by linarith)
        have hdp_ge : (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) ≤ (d : ℝ) * (p : ℝ) := by
          by_contra hlt
          push_neg at hlt
          have hcast : ((d * p : ℕ) : ℝ) = (d : ℝ) * (p : ℝ) := by push_cast; rfl
          exact hn_nw ⟨d * p, hdp_div, hD_lt_sq.trans hdp_gt_sq, hcast.symm ▸ hlt⟩
        have hp_ge : X ^ 20 ≤ (p : ℝ) := by
          have hX20 : X ^ 20 = (x : ℝ) ^ (20 * η) := by
            rw [hX_def, ← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
            congr 1; push_cast; ring
          have hprod : D * (x : ℝ) ^ (20 * η) = (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) := by
            rw [hD_def, ← Real.rpow_add hx_pos]; congr 1; ring
          rw [hX20]
          have h1 : D * (x : ℝ) ^ (20 * η) ≤ D * (p : ℝ) :=
            hprod.symm ▸ hdp_ge.trans (mul_le_mul_of_nonneg_right hd_le_D (Nat.cast_nonneg p))
          exact le_of_mul_le_mul_left h1 hD_pos
        exact ⟨hdp_ge, hp_ge⟩
      -- Coprimality of d and e
      have hcop : d.Coprime e := by
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne1
        let p := (Nat.gcd d e).minFac
        have hp : p.Prime := Nat.minFac_prime hne1
        have hpd : p ∣ d := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left d e)
        have hpe : p ∣ e := (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right d e)
        have hp2_dvd : p ^ 2 ∣ n := hde ▸ (by rw [sq]; exact Nat.mul_dvd_mul hpd hpe)
        have hp2_div : p ^ 2 ∈ n.divisors := Nat.mem_divisors.mpr ⟨hp2_dvd, hn0'⟩
        have hp_ge := (hprime_e p hp hpe).2
        have hX2_lt : (x : ℝ) ^ (2 * η) < ((p ^ 2 : ℕ) : ℝ) := by
          have hX2 : (x : ℝ) ^ (2 * η) = X ^ 2 := by
            rw [hX_def, ← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le]
            congr 1; push_cast; ring
          have h1 : X ^ 2 < X ^ 40 := pow_lt_pow_right₀ hX_gt1 (by norm_num)
          have h2 : X ^ 40 ≤ (p : ℝ) ^ 2 := by
            have := pow_le_pow_left₀ (by positivity) hp_ge 2
            rw [← pow_mul] at this
            exact this
          push_cast
          linarith
        have hpow_full : ∀ r : ℕ, r.Prime → r ∣ p ^ 2 → r ^ 2 ∣ p ^ 2 := by
          intro r hr hrdvd
          have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow hrdvd)
          rw [hrp]
        obtain ⟨r, hr, hrdvd, hnot⟩ := hno_pow (p ^ 2) hp2_div hX2_lt
        exact hnot (hpow_full r hr hrdvd)
      -- Small prime q0 ≤ L divides d
      have hq0_dvd_d : q0 ∣ d := by
        rcases hq0_p.dvd_mul.mp (hde.symm ▸ hq0_dvd) with h | h
        · exact h
        · exfalso
          have hge := (hprime_e q0 hq0_p h).2
          have hX20_ge : Real.exp (20 * L / ℓ) ≤ X ^ 20 := by
            rw [show (20 * L / ℓ : ℝ) = ((20 : ℕ) : ℝ) * (L / ℓ) by push_cast; ring, Real.exp_nat_mul]
            exact pow_le_pow_left₀ (Real.exp_pos _).le hX_ge_exp 20
          linarith [hL_X20]
      have hd_gt1 : 1 < d := lt_of_lt_of_le hq0_p.one_lt (Nat.le_of_dvd hd_pos hq0_dvd_d)
      -- s(d) ≥ d / L
      have hsd_lb : (d : ℝ) / L ≤ (Erdos955.s d : ℝ) := by
        have hmem : d / q0 ∈ d.properDivisors := by
          rw [Nat.mem_properDivisors]
          exact ⟨Nat.div_dvd_of_dvd hq0_dvd_d, Nat.div_lt_self hd_pos hq0_p.one_lt⟩
        have hle : d / q0 ≤ Erdos955.s d := by
          rw [s_eq_sum_properDivisors hd_pos]
          exact single_le_sum (f := fun t : ℕ => t) (fun _ _ => Nat.zero_le _) hmem
        have hmul_eq : (d / q0 : ℕ) * q0 = d := Nat.div_mul_cancel hq0_dvd_d
        have hmulR : ((d / q0 : ℕ) : ℝ) * (q0 : ℝ) = (d : ℝ) := by exact_mod_cast hmul_eq
        rw [div_le_iff₀ hL_pos]
        calc (d : ℝ) = ((d / q0 : ℕ) : ℝ) * (q0 : ℝ) := hmulR.symm
          _ ≤ (Erdos955.s d : ℝ) * L :=
            mul_le_mul (by exact_mod_cast hle) hq0_le (by positivity) (Nat.cast_nonneg _)
      -- s(e) ≤ D * X^4
      have hse_ub : (Erdos955.s e : ℝ) ≤ D * X ^ 4 := by
        let P := e.minFac
        have hP : P.Prime := Nat.minFac_prime (by omega)
        have hPe : P ∣ e := Nat.minFac_dvd e
        have hdP_ge := (hprime_e P hP hPe).1
        have heP_le_D : ((e / P : ℕ) : ℝ) ≤ D := by
          have h1 : (d * P) * (e / P) = n := by
            rw [mul_assoc, Nat.mul_div_cancel' hPe, hde]
          have h1R : ((d : ℝ) * (P : ℝ)) * ((e / P : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast h1
          have hDx : (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) * D = (x : ℝ) := by
            rw [hD_def, ← Real.rpow_add hx_pos]; norm_num
          have hnxR : (n : ℝ) ≤ (x : ℝ) := by exact_mod_cast hnx
          have h2 : (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) * ((e / P : ℕ) : ℝ) ≤
              (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) * D := by
            calc (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) * ((e / P : ℕ) : ℝ)
                ≤ ((d : ℝ) * (P : ℝ)) * ((e / P : ℕ) : ℝ) :=
                  mul_le_mul_of_nonneg_right hdP_ge (Nat.cast_nonneg _)
              _ = (n : ℝ) := h1R
              _ ≤ (x : ℝ) := hnxR
              _ = (x : ℝ) ^ ((1 / 2 : ℝ) + 10 * η) * D := hDx.symm
          exact le_of_mul_le_mul_left h2 (Real.rpow_pos_of_pos hx_pos _)
        have hproper_le : ∀ t ∈ e.properDivisors, t ≤ e / P := by
          intro t ht
          obtain ⟨htd, htlt⟩ := Nat.mem_properDivisors.mp ht
          have hq_gt1 : 1 < e / t := by
            have htpos : 0 < t := Nat.pos_of_mem_properDivisors ht
            have := Nat.mul_div_cancel' htd
            by_contra hle; nlinarith
          have hP_le : P ≤ e / t := Nat.minFac_le_of_dvd hq_gt1 (Nat.div_dvd_of_dvd htd)
          have hmul : t * P ≤ e := by
            calc t * P ≤ t * (e / t) := Nat.mul_le_mul_left t hP_le
              _ = e := Nat.mul_div_cancel' htd
          exact (Nat.le_div_iff_mul_le hP.pos).mpr hmul
        have hsum_le : Erdos955.s e ≤ e.divisors.card * (e / P) := by
          rw [s_eq_sum_properDivisors (by omega)]
          calc ∑ t ∈ e.properDivisors, t
              ≤ ∑ _t ∈ e.properDivisors, (e / P) := sum_le_sum hproper_le
            _ = e.properDivisors.card * (e / P) := by simp
            _ ≤ e.divisors.card * (e / P) :=
              Nat.mul_le_mul_right _ (card_le_card Nat.properDivisors_subset_divisors)
        have he_le_x2 : e ≤ x ^ 2 := by
          have : e ≤ n := hde ▸ Nat.le_mul_of_pos_left e hd_pos
          exact this.trans (hnx.trans (Nat.le_self_pow (by norm_num) x))
        have htau_e : (e.divisors.card : ℝ) ≤ X ^ 4 := hdiv_X4 e (by omega) he_le_x2
        calc (Erdos955.s e : ℝ)
            ≤ (e.divisors.card : ℝ) * ((e / P : ℕ) : ℝ) := by exact_mod_cast hsum_le
          _ ≤ X ^ 4 * D := mul_le_mul htau_e heP_le_D (Nat.cast_nonneg _) (by positivity)
          _ = D * X ^ 4 := by ring
      -- Equation a = σ(d) * s(e) + s(d) * e and g = gcd(σ(d), s(d))
      have ha_eq : a = σ 1 d * Erdos955.s e + Erdos955.s d * e := by
        rw [← hn_sa, ← hde]
        exact s_mul_of_coprime hd_pos (by omega) hcop
      let g := Nat.gcd (σ 1 d) (Erdos955.s d)
      have hg_sig : g ∣ σ 1 d := Nat.gcd_dvd_left _ _
      have hg_sd : g ∣ Erdos955.s d := Nat.gcd_dvd_right _ _
      have hg_a : g ∣ a := ha_eq ▸ dvd_add (dvd_mul_of_dvd_left hg_sig _) (dvd_mul_of_dvd_left hg_sd _)
      have hg_d : g ∣ d := by
        have h1 := s_add_self hd_pos
        exact (Nat.dvd_add_right hg_sd).mp (h1.symm ▸ hg_sig)
      have hg_pos : 0 < g := Nat.pos_of_dvd_of_pos hg_d hd_pos
      exact ⟨hd_div, hd_le_D, hd_gt1, hde, he_gt1, hcop, hsd_lb, hse_ub, hg_a, hg_d, hg_pos, ha_eq⟩
    -- Count fiber elements with a fixed d
    have hfixed_d : ∀ d : ℕ, 1 < d → (d : ℝ) ≤ D →
        let g := Nat.gcd (σ 1 d) (Erdos955.s d)
        ((F.filter (fun n => splitD' n = d)).card : ℝ) ≤
          1 + D * X ^ 4 * L * (g : ℝ) / (d : ℝ) := by
      intro d hd1 hdD g
      let Fd := F.filter (fun n => splitD' n = d)
      change (Fd.card : ℝ) ≤ 1 + D * X ^ 4 * L * (g : ℝ) / (d : ℝ)
      by_cases hFd_empty : Fd = ∅
      · rw [hFd_empty, card_empty]
        simp only [Nat.cast_zero]
        have : 0 ≤ D * X ^ 4 * L * (g : ℝ) / (d : ℝ) := by positivity
        linarith
      obtain ⟨n1, hn1⟩ := nonempty_iff_ne_empty.mpr hFd_empty
      have hn1F : n1 ∈ F := (mem_filter.mp hn1).1
      have hn1d : splitD' n1 = d := (mem_filter.mp hn1).2
      have hp1 := hsplit_props n1 hn1F
      rw [hn1d] at hp1
      have hsd_lb : (d : ℝ) / L ≤ (Erdos955.s d : ℝ) := hp1.2.2.2.2.2.2.1
      have hg_pos : 0 < g := hp1.2.2.2.2.2.2.2.2.2.2.1
      have hsd_pos : 0 < Erdos955.s d := by
        have : (0 : ℝ) < (Erdos955.s d : ℝ) := lt_of_lt_of_le (by positivity) hsd_lb
        exact_mod_cast this
      have hg_sd : g ∣ Erdos955.s d := Nat.gcd_dvd_right _ _
      have hg_sig : g ∣ σ 1 d := Nat.gcd_dvd_left _ _
      let u := σ 1 d / g
      let v := Erdos955.s d / g
      have hv_pos : 0 < v := Nat.div_pos (Nat.le_of_dvd hsd_pos hg_sd) hg_pos
      have hcop_uv : u.Coprime v := Nat.coprime_div_gcd_div_gcd hg_pos
      -- Map n ↦ Erdos955.s (n / d) is injective on Fd, bounded by ⌊D * X^4⌋₊, and constant mod v
      let φ : ℕ → ℕ := fun n => Erdos955.s (n / d)
      have hφ_inj : Set.InjOn φ (Fd : Set ℕ) := by
        intro n hn m hm hφeq
        have hp_n := hsplit_props n (mem_filter.mp hn).1
        have hp_m := hsplit_props m (mem_filter.mp hm).1
        rw [(mem_filter.mp hn).2] at hp_n
        rw [(mem_filter.mp hm).2] at hp_m
        have heq_n := hp_n.2.2.2.2.2.2.2.2.2.2.2
        have heq_m := hp_m.2.2.2.2.2.2.2.2.2.2.2
        have hse_eq : Erdos955.s (n / d) = Erdos955.s (m / d) := hφeq
        have hmul_eq : Erdos955.s d * (n / d) = Erdos955.s d * (m / d) := by
          rw [hse_eq] at heq_n
          omega
        have he_eq : n / d = m / d := Nat.eq_of_mul_eq_mul_left hsd_pos hmul_eq
        rw [← hp_n.2.2.2.1, ← hp_m.2.2.2.1, he_eq]
      have hφ_ub : ∀ y ∈ Fd.image φ, y ≤ ⌊D * X ^ 4⌋₊ := by
        intro y hy
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
        have hp_n := hsplit_props n (mem_filter.mp hn).1
        rw [(mem_filter.mp hn).2] at hp_n
        exact Nat.le_floor hp_n.2.2.2.2.2.2.2.1
      have hφ_mod : ∀ y ∈ Fd.image φ, ∀ z ∈ Fd.image φ, y % v = z % v := by
        intro y hy z hz
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
        obtain ⟨m, hm, rfl⟩ := mem_image.mp hz
        have hp_n := hsplit_props n (mem_filter.mp hn).1
        have hp_m := hsplit_props m (mem_filter.mp hm).1
        rw [(mem_filter.mp hn).2] at hp_n
        rw [(mem_filter.mp hm).2] at hp_m
        have heq_n := hp_n.2.2.2.2.2.2.2.2.2.2.2
        have heq_m := hp_m.2.2.2.2.2.2.2.2.2.2.2
        have hgu : g * u = σ 1 d := Nat.mul_div_cancel' hg_sig
        have hgv : g * v = Erdos955.s d := Nat.mul_div_cancel' hg_sd
        have hcomb : u * φ n + v * (n / d) = u * φ m + v * (m / d) := by
          apply Nat.eq_of_mul_eq_mul_left hg_pos
          calc g * (u * φ n + v * (n / d))
              = (g * u) * φ n + (g * v) * (n / d) := by ring
            _ = a := by rw [hgu, hgv]; exact heq_n.symm
            _ = (g * u) * φ m + (g * v) * (m / d) := by rw [hgu, hgv]; exact heq_m
            _ = g * (u * φ m + v * (m / d)) := by ring
        have hmod_u : u * φ n ≡ u * φ m [MOD v] := by
          change (u * φ n) % v = (u * φ m) % v
          have h1 : (u * φ n + v * (n / d)) % v = (u * φ n) % v := Nat.add_mul_mod_self_left _ _ _
          have h2 : (u * φ m + v * (m / d)) % v = (u * φ m) % v := Nat.add_mul_mod_self_left _ _ _
          rw [← h1, hcomb, h2]
        exact Nat.ModEq.cancel_left_of_coprime hcop_uv.symm hmod_u
      have hcard_le : Fd.card ≤ ⌊D * X ^ 4⌋₊ / v + 1 := by
        rw [← card_image_of_injOn hφ_inj]
        exact card_mod_le hv_pos hφ_ub hφ_mod
      have hvR : (v : ℝ) = (Erdos955.s d : ℝ) / (g : ℝ) := by
        have hgv : g * v = Erdos955.s d := Nat.mul_div_cancel' hg_sd
        have hgposR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
        rw [eq_div_iff hgposR.ne']
        exact_mod_cast (mul_comm v g ▸ hgv)
      have hdiv_le : ((⌊D * X ^ 4⌋₊ / v : ℕ) : ℝ) ≤ D * X ^ 4 * L * (g : ℝ) / (d : ℝ) := by
        have hv_posR : (0 : ℝ) < (v : ℝ) := by exact_mod_cast hv_pos
        have hd_posR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
        have hsd_posR : (0 : ℝ) < (Erdos955.s d : ℝ) := by exact_mod_cast hsd_pos
        calc ((⌊D * X ^ 4⌋₊ / v : ℕ) : ℝ)
            ≤ (⌊D * X ^ 4⌋₊ : ℝ) / (v : ℝ) := Nat.cast_div_le
          _ ≤ (D * X ^ 4) / (v : ℝ) := div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) hv_posR.le
          _ = D * X ^ 4 * (g : ℝ) / (Erdos955.s d : ℝ) := by
              rw [hvR]; field_simp [hsd_posR.ne', (show (g : ℝ) ≠ 0 by exact_mod_cast hg_pos.ne')]
          _ ≤ D * X ^ 4 * (g : ℝ) / ((d : ℝ) / L) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) hsd_lb
          _ = D * X ^ 4 * L * (g : ℝ) / (d : ℝ) := by field_simp [hd_posR.ne', hL_pos.ne']
      have hcast : (Fd.card : ℝ) ≤ ((⌊D * X ^ 4⌋₊ / v : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_le
      linarith
    -- Sum over all pairs (g, h) with g ∈ a.divisors and h ∈ Icc 1 ⌊D⌋₊
    let P := a.divisors ×ˢ Icc 1 ⌊D⌋₊
    let bucket (g h : ℕ) :=
      F.filter (fun n => splitD' n = g * h ∧ Nat.gcd (σ 1 (splitD' n)) (Erdos955.s (splitD' n)) = g)
    have hF_cover : F ⊆ P.biUnion (fun p => bucket p.1 p.2) := by
      intro n hn
      have hp := hsplit_props n hn
      let d := splitD' n
      let g := Nat.gcd (σ 1 d) (Erdos955.s d)
      have hg_a : g ∈ a.divisors := Nat.mem_divisors.mpr ⟨hp.2.2.2.2.2.2.2.2.1, ha.ne'⟩
      have hg_d : g ∣ d := hp.2.2.2.2.2.2.2.2.2.1
      have hg_pos : 0 < g := hp.2.2.2.2.2.2.2.2.2.2.1
      have hd_pos : 0 < d := by have := hp.2.2.1; omega
      let h := d / g
      have hgh : g * h = d := Nat.mul_div_cancel' hg_d
      have hh1 : 1 ≤ h := Nat.div_pos (Nat.le_of_dvd hd_pos hg_d) hg_pos
      have hhD : h ≤ ⌊D⌋₊ := Nat.le_floor ((by exact_mod_cast (hgh ▸ Nat.le_mul_of_pos_left h hg_pos) : (h : ℝ) ≤ (d : ℝ)).trans hp.2.1)
      exact mem_biUnion.mpr ⟨(g, h), mem_product.mpr ⟨hg_a, mem_Icc.mpr ⟨hh1, hhD⟩⟩,
        mem_filter.mpr ⟨hn, hgh.symm, rfl⟩⟩
    have hF_sum : (F.card : ℝ) ≤
        ∑ g ∈ a.divisors, ∑ h ∈ Icc 1 ⌊D⌋₊, ((bucket g h).card : ℝ) := by
      have h1 : F.card ≤ ∑ p ∈ P, (bucket p.1 p.2).card :=
        (card_le_card hF_cover).trans card_biUnion_le
      have h2 : (F.card : ℝ) ≤ ∑ p ∈ P, ((bucket p.1 p.2).card : ℝ) := by
        exact_mod_cast h1
      rwa [sum_product] at h2
    -- Harmonic sum bound ∑_{h=1}^{⌊D⌋₊} 1/h ≤ 1 + L
    have hharm : ∑ h ∈ Icc 1 ⌊D⌋₊, ((h : ℝ)⁻¹) ≤ 1 + L := by
      have h1 := harmonic_le_one_add_log ⌊D⌋₊
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h1
      have hD_le_x : (⌊D⌋₊ : ℝ) ≤ (x : ℝ) := by
        have h2 : D ≤ (x : ℝ) := by
          rw [hD_def]
          simpa using Real.rpow_le_rpow_of_exponent_le hx_gt1.le (show (1 / 2 : ℝ) - 10 * η ≤ 1 by linarith)
        exact (Nat.floor_le hD_pos.le).trans h2
      have hfloor_pos : 0 < (⌊D⌋₊ : ℝ) := by
        have : 1 ≤ ⌊D⌋₊ := Nat.le_floor (by exact_mod_cast hD_ge1)
        exact_mod_cast this
      exact h1.trans (by linarith [Real.log_le_log hfloor_pos hD_le_x])
    -- Bound each inner sum over h ∈ Icc 1 ⌊D⌋₊
    have hinner : ∀ g ∈ a.divisors,
        (∑ h ∈ Icc 1 ⌊D⌋₊, ((bucket g h).card : ℝ)) ≤
          2 * D * X ^ 4 * (1 + L) ^ 2 := by
      intro g hg
      have hg_pos : 0 < g := Nat.pos_of_mem_divisors hg
      have hg_posR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hg_pos
      have hterm : ∀ h ∈ Icc 1 ⌊D⌋₊,
          ((bucket g h).card : ℝ) ≤ 1 + D * X ^ 4 * L * (h : ℝ)⁻¹ := by
        intro h hh
        have hh1 : 1 ≤ h := (mem_Icc.mp hh).1
        have hh_posR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh1
        by_cases hne : (bucket g h).Nonempty
        · obtain ⟨n, hn⟩ := hne
          obtain ⟨hnF, hnd, hng⟩ := mem_filter.mp hn
          have hp := hsplit_props n hnF
          rw [hnd] at hp hng
          have hsub : bucket g h ⊆ F.filter (fun m => splitD' m = g * h) :=
            fun m hm => mem_filter.mpr ⟨(mem_filter.mp hm).1, (mem_filter.mp hm).2.1⟩
          have hbd := hfixed_d (g * h) hp.2.2.1 hp.2.1
          dsimp only at hbd
          rw [hng] at hbd
          have hsimp : D * X ^ 4 * L * (g : ℝ) / ((g * h : ℕ) : ℝ) = D * X ^ 4 * L * (h : ℝ)⁻¹ := by
            push_cast
            field_simp [hg_posR.ne', hh_posR.ne']
          rw [hsimp] at hbd
          exact (by exact_mod_cast card_le_card hsub : ((bucket g h).card : ℝ) ≤ _).trans hbd
        · rw [not_nonempty_iff_eq_empty] at hne
          rw [hne, card_empty]; simp only [Nat.cast_zero]; positivity
      calc ∑ h ∈ Icc 1 ⌊D⌋₊, ((bucket g h).card : ℝ)
          ≤ ∑ h ∈ Icc 1 ⌊D⌋₊, (1 + D * X ^ 4 * L * (h : ℝ)⁻¹) := sum_le_sum hterm
        _ = ((Icc 1 ⌊D⌋₊).card : ℝ) + (D * X ^ 4 * L) * ∑ h ∈ Icc 1 ⌊D⌋₊, (h : ℝ)⁻¹ := by
            rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
        _ ≤ D + (D * X ^ 4 * L) * (1 + L) := by
            have hcD : ((Icc 1 ⌊D⌋₊).card : ℝ) ≤ D := by
              rw [Nat.card_Icc]
              exact Nat.floor_le hD_pos.le
            have hm := mul_le_mul_of_nonneg_left hharm (by positivity : 0 ≤ D * X ^ 4 * L)
            linarith
        _ ≤ 2 * D * X ^ 4 * (1 + L) ^ 2 := by
            have hX4 : 1 ≤ X ^ 4 := one_le_pow₀ hX_gt1.le
            have hL1 : 1 ≤ 1 + L := by linarith
            have hmul1 : 1 ≤ X ^ 4 * (1 + L) ^ 2 := one_le_mul_of_one_le_of_one_le hX4 (one_le_pow₀ hL1)
            have hD1 : D ≤ D * (X ^ 4 * (1 + L) ^ 2) := le_mul_of_one_le_right hD_pos.le hmul1
            have hD2 : D * X ^ 4 * L * (1 + L) ≤ D * X ^ 4 * (1 + L) ^ 2 := by
              have hDX4 : 0 ≤ D * X ^ 4 := by positivity
              have hLL : L * (1 + L) ≤ (1 + L) ^ 2 := by nlinarith
              nlinarith [mul_le_mul_of_nonneg_left hLL hDX4]
            linarith
    have hF_ub : (F.card : ℝ) ≤ 2 * D * X ^ 8 * (1 + L) ^ 2 := by
      calc (F.card : ℝ)
          ≤ ∑ g ∈ a.divisors, ∑ h ∈ Icc 1 ⌊D⌋₊, ((bucket g h).card : ℝ) := hF_sum
        _ ≤ ∑ _g ∈ a.divisors, (2 * D * X ^ 4 * (1 + L) ^ 2) := sum_le_sum hinner
        _ = (a.divisors.card : ℝ) * (2 * D * X ^ 4 * (1 + L) ^ 2) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ X ^ 4 * (2 * D * X ^ 4 * (1 + L) ^ 2) :=
            mul_le_mul_of_nonneg_right htau_a (by positivity)
        _ = 2 * D * X ^ 8 * (1 + L) ^ 2 := by ring
    -- Compare 2 * D * X^8 * (1 + L)^2 with K = ⌊δ * x^(1/2 - ε x)⌋₊
    have hDX8 : D * X ^ 8 ≤ (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) / Real.exp (L / ℓ) := by
      have h1 : D * X ^ 8 = (x : ℝ) ^ ((1 / 2 : ℝ) - 2 * η) := by
        rw [hD_def, hX_def, ← Real.rpow_natCast, ← Real.rpow_mul hx_pos.le, ← Real.rpow_add hx_pos]
        congr 1; ring
      have h2 : (x : ℝ) ^ ((1 / 2 : ℝ) - 2 * η) = (x : ℝ) ^ ((1 / 2 : ℝ) - η) / X := by
        rw [hX_def, ← Real.rpow_sub hx_pos]; congr 1; ring
      have h3 : (x : ℝ) ^ ((1 / 2 : ℝ) - η) ≤ (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) :=
        Real.rpow_le_rpow_of_exponent_le hx_gt1.le (by linarith)
      rw [h1, h2]
      calc (x : ℝ) ^ ((1 / 2 : ℝ) - η) / X
          ≤ (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) / X := div_le_div_of_nonneg_right h3 hX_pos.le
        _ ≤ (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) / Real.exp (L / ℓ) :=
            div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hX_ge_exp
    have hF_half : (F.card : ℝ) ≤ (δ / 2) * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) := by
      calc (F.card : ℝ)
          ≤ 2 * D * X ^ 8 * (1 + L) ^ 2 := hF_ub
        _ = (2 * (1 + L) ^ 2) * (D * X ^ 8) := by ring
        _ ≤ (2 * (1 + L) ^ 2) * ((x : ℝ) ^ ((1 / 2 : ℝ) - ε x) / Real.exp (L / ℓ)) :=
            mul_le_mul_of_nonneg_left hDX8 (by positivity)
        _ = (2 * (1 + L) ^ 2 / Real.exp (L / ℓ)) * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) := by ring
        _ ≤ (δ / 2) * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) := by
            have hle : 2 * (1 + L) ^ 2 / Real.exp (L / ℓ) ≤ δ / 2 :=
              (div_le_iff₀ (Real.exp_pos _)).mpr hexp_d
            exact mul_le_mul_of_nonneg_right hle (by positivity)
    have hK_ge : (δ / 2) * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) ≤ (K : ℝ) := by
      have hge2 : 2 ≤ δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) := by
        have hpow : (x : ℝ) ^ (1 / 4 : ℝ) ≤ (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) :=
          Real.rpow_le_rpow_of_exponent_le hx_gt1.le (by linarith)
        exact hK2.trans (mul_le_mul_of_nonneg_left hpow hδ.le)
      have hfl := Nat.sub_one_lt_floor (δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x))
      change δ * (x : ℝ) ^ ((1 / 2 : ℝ) - ε x) - 1 < (K : ℝ) at hfl
      linarith
    exact_mod_cast hF_half.trans hK_ge
