import OMAReductions.R_Erdos325_erdos_325_variants_wooley_R1
import Mathlib

/-! Fixed-power smooth numbers have positive lower density. Chebyshev bounds
and Abel summation give positive reciprocal weight in a prime band. A
finite incidence argument then increases the smoothness parameter by one
induction step while bounding every product's multiplicity. -/

open MeasureTheory Finset Filter Real
open scoped Topology BigOperators

namespace WooleyPrimeBand

private theorem eventually_linear_theta :
    ∀ᶠ x : ℝ in atTop, (Real.log 2 / 2) * x ≤ Chebyshev.theta x := by
  have hsmall := (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num)).bound
    (show 0 < Real.log 2 / 16 by positivity)
  filter_upwards [hsmall, eventually_ge_atTop (4 : ℝ)] with x hx hx4
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 ≤ log x := log_nonneg (by linarith)
  have hsqrt : 1 ≤ √x := by
    simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ x by linarith)
  have hsq : (√x)^2 = x := Real.sq_sqrt hx0
  have hs : log x ≤ log 2 / 16 * √x := by
    rw [Real.norm_of_nonneg hlog, ← Real.sqrt_eq_rpow,
      Real.norm_of_nonneg (Real.sqrt_nonneg x)] at hx
    exact hx
  have hlog2 : log (x + 2) ≤ 2 * log x := by
    calc
      _ ≤ log (x ^ 2) := by
        apply Real.log_le_log (by linarith)
        nlinarith [mul_nonneg (show 0 ≤ x - 2 by linarith) (show 0 ≤ x + 1 by linarith)]
      _ = _ := by simp [Real.log_pow]
  have hsub : 2 * √x * log x ≤ (log 2 / 8) * x := by
    have h := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg x)
    nlinarith
  have hlog3 : log (x + 2) ≤ 2 * √x * log x := by
    exact hlog2.trans (mul_le_mul_of_nonneg_right (by linarith) hlog)
  have hlog2pos : 0 < log 2 := by positivity
  have hbase : (3 / 4 * log 2) * x ≤ (x - 1) * log 2 := by
    have h := mul_le_mul_of_nonneg_right (show 3 / 4 * x ≤ x - 1 by linarith) hlog2pos.le
    nlinarith
  linarith [Chebyshev.theta_ge' (show 1 ≤ x by linarith)]

private theorem log_weighted_prime_band (A B c : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hTheta : ∀ t ∈ Set.Icc A B, c * t ≤ Chebyshev.theta t) :
    c * Real.log (B / A) - Real.log 4 ≤
      ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) := by
  let f (t : ℝ) := t⁻¹
  let w (p : ℕ) : ℝ := if p.Prime then log p else 0
  have hsum (t : ℝ) : ∑ p ∈ Icc 0 ⌊t⌋₊, w p = Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc, sum_filter]
  have hpos (t : ℝ) (ht : t ∈ Set.Icc A B) : 0 < t := hA.trans_le ht.1
  have hf (t : ℝ) (ht : t ∈ Set.Icc A B) : HasDerivAt f (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv (hpos t ht).ne'
  have hfCont : ContinuousOn (deriv f) (Set.Icc A B) := by
    refine (((continuousOn_id.pow 2).inv₀ fun t ht => pow_ne_zero 2 (hpos t ht).ne').neg).congr ?_
    exact fun t ht => (hf t ht).deriv
  have hfInt : IntegrableOn (deriv f) (Set.Icc A B) := hfCont.integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul (f := f) w hA.le hAB
    (fun t ht => (hf t ht).differentiableAt) hfInt
  simp_rw [hsum] at hAbel
  have hfTheta : IntegrableOn (fun t => deriv f t * Chebyshev.theta t) (Set.Icc A B) := by
    simpa only [hsum] using integrableOn_mul_sum_Icc (m := 0) w hA.le hfInt
  have hcInv : ContinuousOn (fun t : ℝ => -c * t⁻¹) (Set.Icc A B) :=
    continuousOn_const.mul (continuousOn_id.inv₀ fun t ht => (hpos t ht).ne')
  have hInt : (∫ t in Set.Ioc A B, deriv f t * Chebyshev.theta t) ≤
      -c * Real.log (B / A) := by
    calc
      _ ≤ ∫ t in Set.Ioc A B, -c * t⁻¹ := by
        apply setIntegral_mono_on (hfTheta.mono_set Set.Ioc_subset_Icc_self)
          (hcInv.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
        intro t ht
        have ht' : t ∈ Set.Icc A B := Set.Ioc_subset_Icc_self ht
        have ht0 := hpos t ht'
        rw [(hf t ht').deriv]
        calc
          _ ≤ -(t^2)⁻¹ * (c * t) := mul_le_mul_of_nonpos_left (hTheta t ht') (neg_nonpos.mpr (by positivity))
          _ = -c * t⁻¹ := by field_simp
      _ = _ := by
        rw [← intervalIntegral.integral_of_le hAB, intervalIntegral.integral_const_mul,
          integral_inv_of_pos hA (hA.trans_le hAB)]
  have hsumBand : ∑ p ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, f p * w p =
      ∑ p ∈ (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime, Real.log p / (p : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    by_cases hp' : p.Prime <;> simp [f, w, hp', div_eq_mul_inv, mul_comm]
  rw [hsumBand] at hAbel
  have htA : A⁻¹ * Chebyshev.theta A ≤ log 4 := by
    calc
      _ ≤ A⁻¹ * (log 4 * A) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x hA.le) (by positivity)
      _ = _ := by field_simp
  have htB : 0 ≤ B⁻¹ * Chebyshev.theta B :=
    mul_nonneg (inv_nonneg.mpr (hA.le.trans hAB)) (Chebyshev.theta_nonneg B)
  dsimp only [f] at hAbel
  linarith

theorem prime_reciprocals_power_band (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c ≤ ∑ p ∈ (Finset.Ioc ⌊x ^ α⌋₊ ⌊x ^ β⌋₊).filter Nat.Prime, (p : ℝ)⁻¹ := by
  let d := log 2 / 2
  let c := d * (β - α) / (2 * β)
  have hβ : 0 < β := hα.trans hαβ
  have hd : 0 < d := by dsimp [d]; positivity
  have hc : 0 < c := div_pos (mul_pos hd (sub_pos.mpr hαβ)) (by positivity)
  refine ⟨c, hc, ?_⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp eventually_linear_theta
  have hL := tendsto_log_atTop.eventually_ge_atTop (2 * log 4 / (d * (β - α)))
  have hPow := (tendsto_rpow_atTop hα).eventually_ge_atTop T
  filter_upwards [hL, hPow, eventually_ge_atTop (2 : ℝ)] with x hxL hxT hx2
  let A := x ^ α
  let B := x ^ β
  let P := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime
  have hx0 : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hA : 0 < A := Real.rpow_pos_of_pos hx0 _
  have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le (by linarith) hαβ.le
  have hlogBA : Real.log (B / A) = (β - α) * Real.log x := by
    rw [← Real.rpow_sub hx0, Real.log_rpow hx0]
  have hw := log_weighted_prime_band A B d hA hAB
    (fun t ht => hT t (hxT.trans ht.1))
  rw [hlogBA] at hw
  have htwice : 2 * log 4 ≤ (d * (β - α)) * log x := by
    have h := (div_le_iff₀ (mul_pos hd (sub_pos.mpr hαβ))).mp hxL
    simpa only [mul_comm] using h
  have hweight :
      (∑ p ∈ P, log p / (p : ℝ)) ≤ β * log x * ∑ p ∈ P, (p : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp' := mem_filter.mp hp
    have hple : (p : ℝ) ≤ B := (Nat.cast_le.mpr (mem_Ioc.mp hp'.1).2).trans
      (Nat.floor_le (hA.le.trans hAB))
    rw [div_eq_mul_inv, ← Real.log_rpow hx0]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (by exact_mod_cast hp'.2.pos) hple) (by positivity)
  apply (mul_le_mul_iff_right₀ (mul_pos hβ hlog)).mp
  calc
    (β * log x) * c = ((d * (β - α)) * log x) / 2 := by
      dsimp [c]
      field_simp
    _ ≤ d * ((β - α) * log x) - log 4 := by linarith
    _ ≤ ∑ p ∈ P, log p / (p : ℝ) := hw
    _ ≤ (β * log x) * (∑ p ∈ P, (p : ℝ)⁻¹) := hweight

end WooleyPrimeBand

open Filter Finset
open scoped Topology

namespace WooleySmoothDensity

private noncomputable def smooth (x η : ℝ) : Finset ℕ :=
  ⌊x⌋₊.smoothNumbersUpTo (⌊x ^ η⌋₊ + 1)

private noncomputable def primeBand (x α β : ℝ) : Finset ℕ :=
  (Ioc ⌊x ^ α⌋₊ ⌊x ^ β⌋₊).filter Nat.Prime

private theorem mem_primeBand {x α β : ℝ} {p : ℕ} :
    p ∈ primeBand x α β ↔ Nat.Prime p ∧ x ^ α < p ∧ (p : ℝ) ≤ x ^ β := by
  constructor
  · intro hp
    obtain ⟨hpI, hpP⟩ := mem_filter.mp hp
    obtain ⟨hl, hu⟩ := mem_Ioc.mp hpI
    exact ⟨hpP, Nat.lt_of_floor_lt hl, (Nat.le_floor_iff' hpP.ne_zero).mp hu⟩
  · rintro ⟨hp, hlo, hhi⟩
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt' hp.ne_zero).mpr hlo,
      (Nat.le_floor_iff' hp.ne_zero).mpr hhi⟩, hp⟩

private theorem mem_smooth {x η : ℝ} {m : ℕ} :
    m ∈ smooth x η ↔ 0 < m ∧ (m : ℝ) ≤ x ∧
      ∀ q : ℕ, q.Prime → q ∣ m → (q : ℝ) ≤ x ^ η := by
  constructor
  · intro hm
    obtain ⟨hle, hsm⟩ := Nat.mem_smoothNumbersUpTo.mp hm
    have hm0 := (Nat.mem_smoothNumbers.mp hsm).1
    refine ⟨Nat.pos_of_ne_zero hm0, (Nat.le_floor_iff' hm0).mp hle, ?_⟩
    intro q hq hd
    exact (Nat.le_floor_iff' hq.ne_zero).mp
      (Nat.le_of_lt_succ ((Nat.mem_smoothNumbers'.mp hsm) q hq hd))
  · rintro ⟨hm, hle, hsm⟩
    refine Nat.mem_smoothNumbersUpTo.mpr ⟨(Nat.le_floor_iff' hm.ne').mpr hle, ?_⟩
    apply Nat.mem_smoothNumbers'.mpr
    intro q hq hd
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff' hq.ne_zero).mpr (hsm q hq hd))

private theorem card_large_prime_divisors {x : ℝ} (hx : 1 < x) {k n : ℕ}
    (hn : 0 < n) (hnx : (n : ℝ) ≤ x) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ∣ n ∧ x ^ (1 / ((k : ℝ) + 1)) ≤ (p : ℝ)) :
    S.card ≤ k + 1 := by
  have hdvdInt : (∏ p ∈ S, (p : ℤ)) ∣ (n : ℤ) := by
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hneq
      have hp' := (hS p hp).1
      have hq' := (hS q hq).1
      exact Nat.isCoprime_iff_coprime.mpr (hp'.coprime_iff_not_dvd.mpr
        (mt (Nat.prime_dvd_prime_iff_eq hp' hq').mp hneq))
    · intro p hp
      exact_mod_cast (hS p hp).2.1
  have hdvd : (∏ p ∈ S, p) ∣ n := by
    rw [← Nat.cast_prod] at hdvdInt
    exact_mod_cast hdvdInt
  have hb : (x ^ (1 / ((k : ℝ) + 1))) ^ S.card ≤ (∏ p ∈ S, p : ℕ) := by
    rw [← Finset.prod_const, Nat.cast_prod]
    exact Finset.prod_le_prod (fun p hp ↦ Real.rpow_nonneg (by linarith) _)
      (fun p hp ↦ (hS p hp).2.2)
  have hbound : (x ^ (1 / ((k : ℝ) + 1))) ^ S.card ≤ x :=
    hb.trans ((by exact_mod_cast Nat.le_of_dvd hn hdvd : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ n).trans hnx)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x)] at hbound
  have hh : x ^ ((1 / ((k : ℝ) + 1)) * (S.card : ℝ)) ≤ x ^ (1 : ℝ) := by
    rwa [Real.rpow_one]
  have h := (Real.rpow_le_rpow_left_iff hx).mp hh
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)] at h
  exact_mod_cast (by simpa using h : (S.card : ℝ) ≤ (k : ℝ) + 1)

private theorem mul_mem_smooth_next {x : ℝ} (hx : 1 < x) {k p m : ℕ} (hk : 2 ≤ k)
    (hp : p ∈ primeBand x (1 / ((k : ℝ) + 1)) (2 / ((k : ℝ) + 1)))
    (hm : m ∈ smooth (x / p) (2 / (k : ℝ))) :
    p * m ∈ smooth x (2 / ((k : ℝ) + 1)) := by
  obtain ⟨hp, hpl, hpu⟩ := mem_primeBand.mp hp
  obtain ⟨hm, hmle, hms⟩ := mem_smooth.mp hm
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hxR : 0 < x := by linarith
  have hmPower : (x / (p : ℝ)) ^ (2 / (k : ℝ)) ≤ x ^ (2 / ((k : ℝ) + 1)) := by
    calc
      _ ≤ (x / x ^ (1 / ((k : ℝ) + 1))) ^ (2 / (k : ℝ)) :=
        Real.rpow_le_rpow (div_nonneg hxR.le hpR.le)
          (div_le_div_of_nonneg_left hxR.le (Real.rpow_pos_of_pos hxR _) hpl.le) (by positivity)
      _ = _ := by
        have hEq : x / x ^ (1 / ((k : ℝ) + 1)) = x ^ (1 - 1 / ((k : ℝ) + 1)) := by
          rw [Real.rpow_sub hxR, Real.rpow_one]
        rw [hEq, ← Real.rpow_mul hxR.le]
        congr 1
        have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
        field_simp
        ring
  refine mem_smooth.mpr ⟨Nat.mul_pos hp.pos hm, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_comm]
    exact (le_div_iff₀ hpR).mp hmle
  · intro q hq hd
    rcases hq.dvd_mul.mp hd with hqp | hqm
    · have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqp
      subst q
      exact hpu
    · exact (hms q hq hqm).trans hmPower

/-- The prime–integer incidence count converts smaller smooth products into the next threshold. -/
theorem smooth_incidence (x : ℝ) (hx : 1 < x) (k : ℕ) (hk : 2 ≤ k) :
    (∑ p ∈ primeBand x (1 / ((k : ℝ) + 1)) (2 / ((k : ℝ) + 1)),
      (smooth (x / p) (2 / (k : ℝ))).card) ≤
      (k + 1) * (smooth x (2 / ((k : ℝ) + 1))).card := by
  let P := primeBand x (1 / ((k : ℝ) + 1)) (2 / ((k : ℝ) + 1))
  let A := P.sigma (fun p => smooth (x / p) (2 / (k : ℝ)))
  let T := smooth x (2 / ((k : ℝ) + 1))
  let f : (Σ _ : ℕ, ℕ) → ℕ := fun a => a.1 * a.2
  change (∑ p ∈ P, (smooth (x / p) (2 / (k : ℝ))).card) ≤ (k + 1) * T.card
  rw [← Finset.card_sigma]
  change A.card ≤ (k + 1) * T.card
  refine Finset.card_le_mul_card_image_of_maps_to (f := f) ?_ (k + 1) ?_
  · intro a ha
    obtain ⟨hp, hm⟩ := Finset.mem_sigma.mp ha
    exact mul_mem_smooth_next hx hk hp hm
  · intro n hn
    let S := P.filter (fun p => p ∣ n)
    have hCard : (A.filter (fun a => f a = n)).card ≤ S.card := by
      apply Finset.card_le_card_of_injOn (f := Sigma.fst)
      · intro a ha
        obtain ⟨ha, hprod⟩ := Finset.mem_filter.mp ha
        exact Finset.mem_filter.mpr ⟨(Finset.mem_sigma.mp ha).1, ⟨a.2, hprod.symm⟩⟩
      · intro a ha b hb he
        obtain ⟨p, m⟩ := a
        obtain ⟨q, l⟩ := b
        change p = q at he
        subst q
        obtain ⟨ha, ham⟩ := Finset.mem_filter.mp ha
        obtain ⟨_, hbm⟩ := Finset.mem_filter.mp hb
        have hp := (mem_primeBand.mp (Finset.mem_sigma.mp ha).1).1
        exact congrArg (Sigma.mk p) (Nat.eq_of_mul_eq_mul_left hp.pos (ham.trans hbm.symm))
    obtain ⟨hn0, hnx, _⟩ := mem_smooth.mp hn
    refine hCard.trans (card_large_prime_divisors hx hn0 hnx S ?_)
    intro p hp
    obtain ⟨hp, hd⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpP, hpl, _⟩ := mem_primeBand.mp hp
    exact ⟨hpP, hd, hpl.le⟩

private theorem smooth_one_card (x : ℝ) : (smooth x 1).card = ⌊x⌋₊ := by
  have hset : smooth x 1 = Icc 1 ⌊x⌋₊ := by
    ext m
    rw [mem_smooth, mem_Icc]
    constructor
    · rintro ⟨hm, hmx, _⟩
      exact ⟨hm, (Nat.le_floor_iff' hm.ne').mpr hmx⟩
    · rintro ⟨hm, hmx⟩
      have hm0 : 0 < m := hm
      have hmx' := (Nat.le_floor_iff' hm0.ne').mp hmx
      refine ⟨hm0, hmx', ?_⟩
      intro q hq hd
      rw [Real.rpow_one]
      exact (Nat.cast_le.mpr (Nat.le_of_dvd hm0 hd)).trans hmx'
  rw [hset, Nat.card_Icc, add_tsub_cancel_right]

/-- If every fixed power band contains a positive reciprocal prime mass, then the
$2/k$-smooth integers have a positive lower density at all large real cutoffs. -/
theorem density_at_two_div
    (hBand : ∀ α β : ℝ, 0 < α → α < β → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℝ in atTop, c ≤ ∑ p ∈ primeBand x α β, (p : ℝ)⁻¹) :
    ∀ k : ℕ, 2 ≤ k → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ x : ℝ in atTop, δ * x ≤ ((smooth x (2 / (k : ℝ))).card : ℝ) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨1 / 2, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    norm_num only [Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)]
    rw [smooth_one_card]
    have hf := Nat.lt_floor_add_one x
    linarith
  | succ k hk ih =>
    have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    let α : ℝ := 1 / ((k : ℝ) + 1)
    let β : ℝ := 2 / ((k : ℝ) + 1)
    have hk1 : 0 < (k : ℝ) + 1 := by linarith
    have hα : 0 < α := by dsimp [α]; positivity
    have hαβ : α < β := (div_lt_div_iff_of_pos_right hk1).mpr (by norm_num)
    have hβ : β < 1 := (div_lt_iff₀ hk1).mpr (by linarith)
    obtain ⟨δ, hδ, hδevent⟩ := ih
    obtain ⟨T, hT⟩ := eventually_atTop.mp hδevent
    obtain ⟨c, hc, hband⟩ := hBand α β hα hαβ
    refine ⟨δ * c / ((k : ℝ) + 1), by positivity, ?_⟩
    have hXp : ∀ᶠ x : ℝ in atTop, T ≤ x ^ (1 - β) :=
      (tendsto_rpow_atTop (sub_pos.mpr hβ)).eventually (eventually_ge_atTop T)
    filter_upwards [eventually_gt_atTop (1 : ℝ), hXp, hband] with x hx hxT hxb
    have hx0 : 0 < x := by linarith
    let P := primeBand x α β
    have hLo (p : ℕ) (hp : p ∈ P) :
        δ * (x / (p : ℝ)) ≤ ((smooth (x / p) (2 / (k : ℝ))).card : ℝ) := by
      obtain ⟨hpP, _, hpu⟩ := mem_primeBand.mp hp
      apply hT
      calc
        T ≤ x ^ (1 - β) := hxT
        _ = x / x ^ β := by rw [Real.rpow_sub hx0, Real.rpow_one]
        _ ≤ _ := div_le_div_of_nonneg_left hx0.le (Nat.cast_pos.mpr hpP.pos) hpu
    have hs (p : ℕ) : δ * (x / (p : ℝ)) = δ * x * (p : ℝ)⁻¹ := by ring
    have hSum := Finset.sum_le_sum (s := P) hLo
    simp_rw [hs] at hSum
    rw [← Finset.mul_sum] at hSum
    have hFin : (∑ p ∈ P, ((smooth (x / p) (2 / (k : ℝ))).card : ℝ)) ≤
        ((k : ℝ) + 1) * ((smooth x β).card : ℝ) := by
      have h : ((∑ p ∈ P, (smooth (x / p) (2 / (k : ℝ))).card : ℕ) : ℝ) ≤
          (((k + 1) * (smooth x β).card : ℕ) : ℝ) :=
        Nat.cast_le.mpr (smooth_incidence x hx k hk)
      simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h
    have hdown : δ * x * c ≤
        ((k : ℝ) + 1) * ((smooth x β).card : ℝ) :=
      ((mul_le_mul_of_nonneg_left hxb (mul_nonneg hδ.le hx0.le)).trans hSum).trans hFin
    rw [Nat.cast_succ]
    change δ * c / ((k : ℝ) + 1) * x ≤ ((smooth x β).card : ℝ)
    have hE : δ * c / ((k : ℝ) + 1) * x = δ * x * c / ((k : ℝ) + 1) := by ring
    rw [hE]
    exact (div_le_iff₀ hk1).mpr (by simpa only [mul_comm ((smooth x β).card : ℝ)] using hdown)

/-- The prime-band estimate implies the exact natural-cutoff smooth-number density. -/
theorem smooth_density_of_prime_band
    (hBand : ∀ α β : ℝ, 0 < α → α < β → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ x : ℝ in atTop, c ≤
        ∑ p ∈ (Ioc ⌊x ^ α⌋₊ ⌊x ^ β⌋₊).filter Nat.Prime, (p : ℝ)⁻¹) :
    ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ P : ℕ in atTop,
        c * P ≤ ((P.smoothNumbersUpTo (⌊(P : ℝ) ^ η⌋₊ + 1)).card : ℝ) := by
  intro η hη
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 (2 / η))
  have hkR : (1 : ℝ) < (k : ℝ) := (le_max_left _ _).trans_lt hk
  have hk2 : 2 ≤ k := by exact_mod_cast hkR
  have hk0 : 0 < (k : ℝ) := by linarith
  have hηk : 2 / (k : ℝ) ≤ η := by
    apply (div_le_iff₀ hk0).mpr
    have h := (le_max_right 1 (2 / η)).trans hk.le
    nlinarith [(div_le_iff₀ hη).mp h]
  obtain ⟨δ, hδ, hevent⟩ := density_at_two_div hBand k hk2
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hevent,
    eventually_ge_atTop (1 : ℕ)] with P hP hP1
  have hsubset : smooth (P : ℝ) (2 / (k : ℝ)) ⊆
      P.smoothNumbersUpTo (⌊(P : ℝ) ^ η⌋₊ + 1) := by
    intro a ha
    have hreal : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP1
    have hpow := Real.rpow_le_rpow_of_exponent_le hreal hηk
    obtain ⟨hbound, hsm⟩ := Nat.mem_smoothNumbersUpTo.mp ha
    rw [Nat.floor_natCast] at hbound
    refine Nat.mem_smoothNumbersUpTo.mpr ⟨hbound, Nat.smoothNumbers_mono ?_ hsm⟩
    exact Nat.add_le_add_right (Nat.floor_le_floor hpow) 1
  exact hP.trans (Nat.cast_le.mpr (Finset.card_le_card hsubset))

end WooleySmoothDensity

theorem OMA.solution : OMA.R_Erdos325_erdos_325_variants_wooley_R1.H1 :=
  WooleySmoothDensity.smooth_density_of_prime_band WooleyPrimeBand.prime_reciprocals_power_band
