import OMAStatements.S_oeis_a099251

-- Problem: A099251: Bisection of Motzkin sums (A005043).
-- Upstream: formal-conjectures statements/oeis-a099251.lean:0 (declaration OMA.S_oeis_a099251.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
--
-- Proof (Grok Bot w3): substitute t = (1 - cos u)/2, so the right side is K(2n)/π with
-- K m = ∫_0^π (1 + cos u)(2 cos u - 1)^m du.  K satisfies (m+3)K(m+2) = 3(m+1)K(m) - 2(m+1)K(m+1)
-- (fundamental theorem of calculus for (2cos u - 1)^(m+1)(1 + cos u) sin u), K(0) = π, K(1) = 0, and
-- K m / π is an integer (binomial expansion and Wallis' integrals), so riordan m * π = (-1)^m K m.

namespace OMA.A099251Proof
open Real intervalIntegral

noncomputable def KK (m : ℕ) : ℝ := ∫ u in (0:ℝ)..π, (1 + cos u) * (2 * cos u - 1) ^ m

lemma key_pt (u : ℝ) (hu : u ∈ Set.Ioc 0 π) :
    Real.sqrt ((1 + cos u) / (1 - cos u)) * sin u = 1 + cos u := by
  obtain ⟨h0, hπ⟩ := hu
  have hs : 0 ≤ sin u := sin_nonneg_of_nonneg_of_le_pi h0.le hπ
  have hc : cos u < 1 := by
    have := cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ h0
    simpa using this
  have hc' : -1 ≤ cos u := neg_one_le_cos u
  have h1 : 0 < 1 - cos u := by linarith
  rw [← Real.sqrt_sq hs, ← Real.sqrt_mul (div_nonneg (by linarith) h1.le), sin_sq]
  have : (1 + cos u) / (1 - cos u) * (1 - cos u ^ 2) = (1 + cos u) ^ 2 := by
    field_simp; ring
  rw [this, Real.sqrt_sq (by linarith)]

lemma subst (n : ℕ) : ∫ t in (0:ℝ)..1, Real.sqrt ((1 - t) / t) * (1 - 8 * t + 16 * t ^ 2) ^ n
    = (1/2) * KK (2*n) := by
  have h := integral_comp_mul_deriv_of_deriv_nonneg (a := 0) (b := π)
    (f := fun u => (1 - cos u)/2) (f' := fun u => sin u / 2)
    (g := fun t => Real.sqrt ((1 - t) / t) * (1 - 8 * t + 16 * t ^ 2) ^ n) ?_ ?_ ?_
  · have e0 : (1 - cos (0:ℝ))/2 = 0 := by simp
    have e1 : (1 - cos π)/2 = 1 := by norm_num
    rw [e0, e1] at h
    rw [← h, KK, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with u hu
    rw [Set.uIoc_of_le pi_pos.le] at hu
    have hk := key_pt u hu
    simp only [Function.comp_apply]
    have e2 : (1 - (1 - cos u) / 2) / ((1 - cos u) / 2) = (1 + cos u) / (1 - cos u) := by
      have : (1 - (1 - cos u) / 2) = (1 + cos u) / 2 := by ring
      rw [this, div_div_div_cancel_right₀ (by norm_num : (2:ℝ) ≠ 0)]
    have e3 : (1 - 8 * ((1 - cos u) / 2) + 16 * ((1 - cos u) / 2) ^ 2) = (2 * cos u - 1) ^ 2 := by
      ring
    rw [e2, e3, pow_mul]
    calc Real.sqrt ((1 + cos u) / (1 - cos u)) * ((2 * cos u - 1) ^ 2) ^ n * (sin u / 2)
        = (Real.sqrt ((1 + cos u) / (1 - cos u)) * sin u) * ((2 * cos u - 1) ^ 2) ^ n / 2 := by ring
      _ = _ := by rw [hk]; ring
  · exact (continuous_const.sub continuous_cos).div_const 2 |>.continuousOn
  · intro x _
    have := ((hasDerivAt_cos x).const_sub 1).div_const 2
    simpa using this
  · intro x hx
    simp only [min_eq_left pi_pos.le, max_eq_right pi_pos.le] at hx
    have := sin_nonneg_of_nonneg_of_le_pi hx.1.le hx.2.le
    positivity

lemma cont_term (j : ℕ) : Continuous fun u : ℝ => (1 + cos u) * (2 * cos u - 1) ^ j := by fun_prop

lemma Krec (m : ℕ) :
    ((m:ℝ) + 3) * KK (m + 2) = 3 * ((m:ℝ) + 1) * KK m - 2 * ((m:ℝ) + 1) * KK (m + 1) := by
  set G : ℝ → ℝ := fun u => (2 * cos u - 1) ^ (m + 1) * (1 + cos u) * sin u
  set G' : ℝ → ℝ := fun u =>
    ((m + 1 : ℕ) * (2 * cos u - 1) ^ m * (2 * -sin u)) * (1 + cos u) * sin u
      + (2 * cos u - 1) ^ (m + 1) * (-sin u) * sin u
      + (2 * cos u - 1) ^ (m + 1) * (1 + cos u) * cos u
  have hd : ∀ u ∈ Set.uIcc 0 π, HasDerivAt G (G' u) u := by
    intro u _
    have h1 : HasDerivAt (fun x => (2 * cos x - 1) ^ (m + 1))
        (((m + 1 : ℕ) : ℝ) * (2 * cos u - 1) ^ m * (2 * -sin u)) u := by
      have := (((hasDerivAt_cos u).const_mul 2).sub_const 1).fun_pow (m + 1)
      simpa using this
    have h2 : HasDerivAt (fun x => 1 + cos x) (-sin u) u := (hasDerivAt_cos u).const_add 1
    have h3 := hasDerivAt_sin u
    have := (h1.fun_mul h2).fun_mul h3
    exact this.congr_deriv (by simp only [G']; ring)
  have hint : IntervalIntegrable G' MeasureTheory.volume 0 π := by
    apply Continuous.intervalIntegrable
    simp only [G']; fun_prop
  have hFTC := integral_eq_sub_of_hasDerivAt hd hint
  have hG : G π - G 0 = 0 := by simp [G]
  rw [hG] at hFTC
  have hpt : ∀ u, G' u = (-(3 * ((m:ℝ) + 1) / 2)) * ((1 + cos u) * (2 * cos u - 1) ^ m)
      + ((m:ℝ) + 1) * ((1 + cos u) * (2 * cos u - 1) ^ (m + 1))
      + (((m:ℝ) + 3) / 2) * ((1 + cos u) * (2 * cos u - 1) ^ (m + 2)) := by
    intro u
    simp only [G']
    have hs : sin u * sin u = 1 - cos u ^ 2 := by rw [← sin_sq]; ring
    push_cast
    have e1 : (2 * cos u - 1) ^ (m + 1) = (2 * cos u - 1) ^ m * (2 * cos u - 1) := pow_succ _ _
    have e2 : (2 * cos u - 1) ^ (m + 2) = (2 * cos u - 1) ^ m * (2 * cos u - 1) ^ 2 := pow_add _ _ _
    rw [e1, e2]
    linear_combination (-(2 * ((m:ℝ) + 1)) * (2 * cos u - 1) ^ m * (1 + cos u)
      - (2 * cos u - 1) ^ m * (2 * cos u - 1)) * hs
  simp_rw [hpt] at hFTC
  rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul] at hFTC
  · simp only [KK]
    linarith
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

noncomputable def WW (j : ℕ) : ℝ := ∫ u in (0:ℝ)..π, cos u ^ j

lemma WW_rec (j : ℕ) : WW (j + 2) = ((j:ℝ) + 1) / ((j:ℝ) + 2) * WW j := by
  simp only [WW]
  rw [integral_cos_pow]
  simp

lemma WW_even (r : ℕ) : WW (2 * r) = π * (r.centralBinom : ℝ) / 4 ^ r := by
  induction r with
  | zero => simp [WW]
  | succ r ih =>
    have h := Nat.succ_mul_centralBinom_succ r
    have h' : ((r:ℝ) + 1) * ((r + 1).centralBinom : ℝ) = 2 * (2 * r + 1) * (r.centralBinom : ℝ) := by
      exact_mod_cast h
    have e : 2 * (r + 1) = 2 * r + 2 := by ring
    rw [e, WW_rec, ih]
    have hr : ((r + 1).centralBinom : ℝ) = 2 * (2 * r + 1) * (r.centralBinom : ℝ) / ((r:ℝ) + 1) := by
      field_simp; linarith
    rw [hr]
    push_cast
    field_simp
    ring

lemma WW_odd (r : ℕ) : WW (2 * r + 1) = 0 := by
  induction r with
  | zero => simp [WW]
  | succ r ih =>
    have e : 2 * (r + 1) + 1 = (2 * r + 1) + 2 := by ring
    rw [e, WW_rec, ih, mul_zero]

lemma A0 (k : ℕ) : ∃ z : ℤ, (2:ℝ) ^ k * WW k = π * z := by
  rcases Nat.even_or_odd' k with ⟨r, rfl | rfl⟩
  · refine ⟨r.centralBinom, ?_⟩
    rw [WW_even, pow_mul]
    norm_num
    field_simp
  · exact ⟨0, by rw [WW_odd]; simp⟩

lemma A1 (k : ℕ) : ∃ z : ℤ, (2:ℝ) ^ k * WW (k + 1) = π * z := by
  rcases Nat.even_or_odd' k with ⟨r, rfl | rfl⟩
  · exact ⟨0, by rw [WW_odd]; simp⟩
  · obtain ⟨q, hq⟩ := Nat.two_dvd_centralBinom_succ r
    refine ⟨q, ?_⟩
    have e : 2 * r + 1 + 1 = 2 * (r + 1) := by ring
    rw [e, WW_even, hq]
    push_cast
    rw [pow_succ, pow_mul, pow_succ]
    norm_num
    field_simp
    ring

lemma KK_int (m : ℕ) : ∃ z : ℤ, KK m = π * z := by
  have hexp : ∀ u : ℝ, (1 + cos u) * (2 * cos u - 1) ^ m =
      ∑ k ∈ Finset.range (m + 1),
        ((-1:ℝ) ^ (m - k) * (m.choose k : ℝ) * 2 ^ k) * (cos u ^ k + cos u ^ (k + 1)) := by
    intro u
    rw [sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [mul_pow]; ring
  have hI : KK m = ∑ k ∈ Finset.range (m + 1),
      ((-1:ℝ) ^ (m - k) * (m.choose k : ℝ)) * ((2:ℝ) ^ k * WW k + (2:ℝ) ^ k * WW (k + 1)) := by
    simp only [KK, hexp]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [integral_const_mul, integral_add, WW, WW]
      · ring
      all_goals (apply Continuous.intervalIntegrable; fun_prop)
    · intro k _
      apply Continuous.intervalIntegrable; fun_prop
  refine ⟨∑ k ∈ Finset.range (m + 1), (-1:ℤ) ^ (m - k) * (m.choose k : ℤ) *
      ((A0 k).choose + (A1 k).choose), ?_⟩
  rw [hI]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h0 := (A0 k).choose_spec
  have h1 := (A1 k).choose_spec
  linear_combination ((-1:ℝ) ^ (m - k) * (m.choose k : ℝ)) * (h0 + h1)

lemma KK0 : KK 0 = π := by
  simp only [KK, pow_zero, mul_one]
  rw [integral_add]
  · simp
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

lemma KK1 : KK 1 = 0 := by
  simp only [KK, pow_one]
  have : ∀ u : ℝ, (1 + cos u) * (2 * cos u - 1) = 2 * cos u ^ 2 + cos u - 1 := fun u => by ring
  simp_rw [this]
  rw [integral_sub, integral_add, integral_const_mul, integral_cos_sq, integral_cos]
  · simp; ring
  all_goals (apply Continuous.intervalIntegrable; fun_prop)

open OMA.S_oeis_a099251 in
lemma main_aux (m : ℕ) : ((riordan m : ℝ) * π = (-1) ^ m * KK m) ∧
    ((riordan (m + 1) : ℝ) * π = (-1) ^ (m + 1) * KK (m + 1)) := by
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [riordan, KK0]
    · simp [riordan, KK1]
  | succ m ih =>
    obtain ⟨P0, P1⟩ := ih
    refine ⟨P1, ?_⟩
    obtain ⟨z, hz⟩ := KK_int (m + 2)
    have hrec := Krec m
    set s : ℝ := (-1) ^ m with hs
    set y : ℤ := (-1) ^ m * z with hy
    have hyR : (y : ℝ) = s * z := by simp [hy, hs]
    have E : ((m:ℝ) + 3) * (y : ℝ) * π
        = ((m:ℝ) + 1) * (2 * (riordan (m + 1) : ℝ) + 3 * (riordan m : ℝ)) * π := by
      rw [hyR]
      have P1' : (riordan (m + 1) : ℝ) * π = -s * KK (m + 1) := by rw [P1, pow_succ]; ring
      linear_combination (-((m:ℝ) + 3) * s) * hz + s * hrec - (3 * ((m:ℝ) + 1)) * P0
        - (2 * ((m:ℝ) + 1)) * P1'
    have E' : ((m:ℝ) + 3) * (y : ℝ) = ((m:ℝ) + 1) * (2 * (riordan (m + 1) : ℝ) + 3 * (riordan m : ℝ)) := by
      have hπ : π ≠ 0 := pi_ne_zero
      exact mul_right_cancel₀ hπ E
    have EZ : ((m:ℤ) + 3) * y = (((m + 1) * (2 * riordan (m + 1) + 3 * riordan m) : ℕ) : ℤ) := by
      have : (((m:ℤ) + 3) * y : ℤ) = ((((m + 1) * (2 * riordan (m + 1) + 3 * riordan m) : ℕ) : ℤ) : ℝ) := by
        push_cast; exact E'
      exact_mod_cast this
    have hy0 : 0 ≤ y := by
      by_contra h
      have h' : y < 0 := not_le.mp h
      have : ((m:ℤ) + 3) * y < 0 := mul_neg_of_pos_of_neg (by positivity) h'
      rw [EZ] at this
      exact absurd this (not_lt.mpr (Int.natCast_nonneg _))
    have hN : (m + 1) * (2 * riordan (m + 1) + 3 * riordan m) = y.toNat * (m + 3) := by
      have h1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
      have : (((m + 1) * (2 * riordan (m + 1) + 3 * riordan m) : ℕ) : ℤ) = ((y.toNat * (m + 3) : ℕ) : ℤ) := by
        rw [← EZ]; push_cast; rw [h1]; ring
      exact_mod_cast this
    have hR : riordan (m + 2) = y.toNat := by
      show (m + 1) * (2 * riordan (m + 1) + 3 * riordan m) / (m + 3) = y.toNat
      exact Nat.div_eq_of_eq_mul_left (by omega) hN
    have hyN : ((y.toNat : ℕ) : ℝ) = (y : ℝ) := by
      have h1 : ((y.toNat : ℕ) : ℤ) = y := Int.toNat_of_nonneg hy0
      exact_mod_cast h1
    show (riordan (m + 2) : ℝ) * π = (-1) ^ (m + 2) * KK (m + 2)
    rw [hR, hyN, hyR, hz, pow_add, ← hs]
    ring


end OMA.A099251Proof

open Real OMA.A099251Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a099251.main := by
  intro n
  rw [subst n]
  have h := (main_aux (2 * n)).1
  rw [pow_mul] at h
  norm_num at h
  have hπ : π ≠ 0 := pi_ne_zero
  field_simp
  linarith [h]
