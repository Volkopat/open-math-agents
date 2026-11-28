import OMAStatements.S_oeis_a069932

/-
For A069932, double count the multiples of each totient in its truncated interval.
The positive limit is Landau’s reciprocal-totient constant (1900).
See Bordellès and Cloitre, J. Integer Seq. 16 (2013), Article 13.6.3, p. 1.
The pinned target requests existence. The summable witness below is its Euler-product expansion.
-/

open Finset Filter Topology
namespace TotientMean

noncomputable def weight (p : ℕ) : ℝ := if p.Prime then 1 / (p-1 : ℕ) else 0
noncomputable def w (s : Finset ℕ) : ℝ := ∏ p ∈ s, weight p
def den (s : Finset ℕ) : ℕ := ∏ p ∈ s, p
noncomputable def coeff (s : Finset ℕ) : ℝ := w s / den s

lemma weight_nn (p : ℕ) : 0 ≤ weight p := by unfold weight; split <;> positivity
lemma w_nn (s : Finset ℕ) : 0 ≤ w s := prod_nonneg fun p _ ↦ weight_nn p
lemma coeff_nn (s : Finset ℕ) : 0 ≤ coeff s := div_nonneg (w_nn s) (Nat.cast_nonneg _)

lemma coeff_sum : Summable coeff := by
  have h : Summable (fun p : ℕ ↦ weight p / p) := by
    apply Summable.of_nonneg_of_le (fun p ↦ div_nonneg (weight_nn p) (Nat.cast_nonneg p))
      (f := fun p : ℕ ↦ 2 * (1 / (p : ℝ)^2))
    · intro p
      unfold weight
      split
      next hp =>
        have hp' : 1 < p := hp.one_lt
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
        rw [Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
        have hpos : (0:ℝ) < p := by positivity
        have hsub : (0:ℝ) < p-1 := by linarith
        field_simp [hpos.ne', hsub.ne']
        nlinarith
      next => simp
    · exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left 2
  apply (summable_finsetProd_of_summable_nonneg (fun p ↦ div_nonneg (weight_nn p) (Nat.cast_nonneg p)) h).congr
  intro s
  simp [coeff,w,den,prod_div_distrib]

lemma ww_zero {s : Finset ℕ} {p : ℕ} (hp : p ∈ s) (hn : ¬p.Prime) : w s = 0 := by
  exact prod_eq_zero hp (by simp [weight,hn])

lemma subset_iff {s : Finset ℕ} {k : ℕ} (hk : 0 < k) (hs : ∀ p ∈ s, Nat.Prime p) :
    s ⊆ k.primeFactors ↔ den s ∣ k := by
  constructor
  · exact fun h ↦ (prod_dvd_prod_of_subset _ _ id h).trans (Nat.prod_primeFactors_dvd k)
  · intro h p hp
    exact Nat.mem_primeFactors.mpr ⟨hs p hp,(dvd_prod_of_mem id hp).trans h,hk.ne'⟩

lemma expand {k : ℕ} (hk : 0 < k) :
    (k : ℝ) / k.totient = ∑ s ∈ k.primeFactors.powerset, w s := by
  have h := Nat.totient_mul_prod_primeFactors k
  have h' : (k.totient : ℝ) * (∏ p ∈ k.primeFactors, (p : ℝ)) =
      k * ∏ p ∈ k.primeFactors, (↑(p-1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_prod] using congrArg (fun x : ℕ ↦ (x : ℝ)) h
  have hpos : 0 < ∏ p ∈ k.primeFactors, (↑(p-1 : ℕ) : ℝ) := by
    apply prod_pos
    intro p hp
    exact_mod_cast Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have ht : (0:ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  unfold w
  rw [← prod_one_add]
  calc
    _ = (∏ p ∈ k.primeFactors, (p : ℝ)) / ∏ p ∈ k.primeFactors, (↑(p-1 : ℕ) : ℝ) :=
      (div_eq_div_iff ht.ne' hpos.ne').mpr (by linarith)
    _ = _ := by
      rw [← prod_div_distrib]
      apply prod_congr rfl
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hp2 := hpr.two_le
      simp only [weight, if_pos hpr, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
      have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have hpN : (p : ℝ)-1 ≠ 0 := by linarith
      field_simp [hpN]
      <;> ring

end TotientMean

open Filter Topology Finset
namespace TotientMean
lemma hratio (d : ℕ) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ (harmonic (n / d) : ℝ) / Real.log n) atTop (𝓝 1) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim (c : ℝ) : Tendsto (fun n : ℕ ↦ c / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ ↦ 1 - Real.log d / Real.log n)
    (h := fun n : ℕ ↦ 1 + 1 / Real.log n)
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub (hlim (Real.log d))
  · simpa using (tendsto_const_nhds (x := (1:ℝ))).add (hlim 1)
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hN := Real.log_pos hnR
    have hnat : n < (n/d+1)*d := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self _)
    have hv : (n:ℝ) ≤ (↑(n/d)+1)*(d:ℝ) := by exact_mod_cast hnat.le
    have hv' := Real.log_le_log (by positivity : (0:ℝ)<n) hv
    rw [Real.log_mul (by positivity) (by exact_mod_cast hd.ne')] at hv'
    have h := log_add_one_le_harmonic (n/d)
    push_cast at h
    apply (le_div_iff₀ hN).mpr
    field_simp [hN.ne']
    <;> linarith
  · filter_upwards [eventually_ge_atTop (max d 2)] with n hn
    have hnR : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hN := Real.log_pos hnR
    have hdn : 0 < n/d := Nat.div_pos (by omega) hd
    have h := harmonic_le_one_add_log (n/d)
    have hh := Real.log_le_log (by exact_mod_cast hdn : (0:ℝ)<(n/d:ℕ))
      (show (↑(n/d) : ℝ) ≤ n by exact_mod_cast Nat.div_le_self n d)
    apply (div_le_iff₀ hN).mpr
    field_simp [hN.ne']
    <;> linarith

lemma harmonic_dom {n d : ℕ} (hn : 1 ≤ Real.log n) :
    (harmonic (n/d) : ℝ)/Real.log n ≤ 2 := by
  have hn0 : 0 < Real.log n := by linarith
  have h := harmonic_le_one_add_log (n/d)
  by_cases hz : n/d=0
  · simp [hz]
  have hl := Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz : (0:ℝ)<(n/d:ℕ))
      (show (↑(n/d) : ℝ) ≤ n by exact_mod_cast Nat.div_le_self n d)
  apply (div_le_iff₀ hn0).mpr
  linarith
end TotientMean

open Finset Filter Topology
namespace TotientMean
lemma expand_all {k : ℕ} (hk : 0 < k) :
    (k:ℝ)/k.totient = ∑' s : Finset ℕ, if den s ∣ k then w s else 0 := by
  rw [expand hk, tsum_eq_sum (s := k.primeFactors.powerset)]
  · apply sum_congr rfl
    intro s hs
    have h := (prod_dvd_prod_of_subset s _ id (mem_powerset.mp hs)).trans (Nat.prod_primeFactors_dvd k)
    exact (if_pos (show den s ∣ k from h)).symm
  · intro s hs
    by_cases h : ∀ p ∈ s, Nat.Prime p
    · have hn : ¬ den s ∣ k := fun hd ↦ hs (mem_powerset.mpr ((subset_iff hk h).mpr hd))
      simp [hn]
    · push Not at h
      obtain ⟨p,hp,hq⟩ := h
      simp [ww_zero hp hq]

lemma supported {k : ℕ} (hk : 0 < k) :
    Summable (fun s : Finset ℕ ↦ if den s ∣ k then w s else 0) := by
  apply summable_of_ne_finset_zero (s := k.primeFactors.powerset)
  intro s hs
  by_cases h : ∀ p ∈ s, Nat.Prime p
  · have hn : ¬ den s ∣ k := fun hd ↦ hs (mem_powerset.mpr ((subset_iff hk h).mpr hd))
    simp [hn]
  · push Not at h
    obtain ⟨p,hp,hq⟩ := h
    simp [ww_zero hp hq]

lemma weighted_multiples (n d : ℕ) :
    (∑ k ∈ Icc 1 n, if d ∣ k then (k:ℝ)⁻¹ else 0) = (harmonic (n/d) : ℝ)/d := by
  by_cases hd : d = 0
  · subst d; simp
  have hd' := Nat.pos_of_ne_zero hd
  rw [← sum_filter, harmonic_eq_sum_Icc]
  push_cast
  rw [sum_div]
  apply sum_bij' (fun k _ ↦ k/d) (fun r _ ↦ r*d)
  · intro k hk
    obtain ⟨hx,hx'⟩ := mem_filter.mp hk
    have hkd : d ≤ k := Nat.le_of_dvd (by have := (mem_Icc.mp hx).1; omega) hx'
    exact mem_Icc.mpr ⟨Nat.div_pos hkd hd',Nat.div_le_div_right (mem_Icc.mp hx).2⟩
  · intro r hr
    obtain ⟨h1,h2⟩ := mem_Icc.mp hr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos h1 hd',(Nat.le_div_iff_mul_le hd').mp h2⟩,
      dvd_mul_left d r⟩
  · intro k hk; exact Nat.div_mul_cancel (mem_filter.mp hk).2
  · intro r hr; simp [hd']
  · intro k hk
    have eqn := Nat.div_mul_cancel (mem_filter.mp hk).2
    have eqR : ((k/d:ℕ):ℝ)*(d:ℝ) = k := by exact_mod_cast eqn
    rw [← eqR]
    simp [div_eq_mul_inv,mul_comm]

lemma raw_multiples (n d : ℕ) :
    (∑ k ∈ Icc 1 n, if d ∣ k then (1:ℝ) else 0) = (n/d : ℕ) := by
  have he : Icc 1 n = Ioc 0 n := by ext; simp; omega
  rw [he, ← Nat.Ioc_filter_dvd_card_eq_div]
  rw [card_filter]
  push_cast
  rfl

lemma recip_expand (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k.totient:ℝ)⁻¹) =
       ∑' s, coeff s * (harmonic (n/den s):ℝ) := by
  calc
    _ = ∑ k ∈ Icc 1 n, (∑' s, if den s ∣ k then w s else 0) * (k:ℝ)⁻¹ := by
      apply sum_congr rfl
      intro k hk
      have hk' : 0 < k := (mem_Icc.mp hk).1
      rw [← expand_all hk']
      field_simp
    _ = ∑' s, ∑ k ∈ Icc 1 n, (if den s ∣ k then w s else 0) * (k:ℝ)⁻¹ := by
      simp_rw [← tsum_mul_right]
      symm
      apply Summable.tsum_finsetSum
      intro k hk
      exact (supported (mem_Icc.mp hk).1).mul_right _
    _ = _ := by
      apply tsum_congr
      intro s
      calc
        _ = w s * ∑ k ∈ Icc 1 n, (if den s ∣ k then (k:ℝ)⁻¹ else 0) := by
          rw [mul_sum]
          apply sum_congr rfl
          intro k hk
          split <;> simp_all
        _ = _ := by rw [weighted_multiples]; unfold coeff; ring

lemma raw_bound (n : ℕ) :
    (∑ k ∈ Icc 1 n, (k:ℝ)/k.totient) ≤ (n:ℝ) * ∑' s, coeff s := by
  calc
    _ = ∑ k ∈ Icc 1 n, ∑' s, (if den s ∣ k then w s else 0) :=
      sum_congr rfl fun k hk ↦ expand_all (mem_Icc.mp hk).1
    _ = ∑' s, ∑ k ∈ Icc 1 n, (if den s ∣ k then w s else 0) := by
      symm; exact Summable.tsum_finsetSum fun k hk ↦ supported (mem_Icc.mp hk).1
    _ = ∑' s, w s * ((n / den s : ℕ) : ℝ) := by
      apply tsum_congr
      intro s
      rw [← raw_multiples,mul_sum]
      apply sum_congr rfl
      intro k hk
      split <;> simp_all
    _ ≤ ∑' s, n * coeff s := by
      apply Summable.tsum_le_tsum
      · intro s
        calc w s * ((n / den s : ℕ) : ℝ) ≤ w s * ((n:ℝ)/den s) := mul_le_mul_of_nonneg_left Nat.cast_div_le (w_nn s)
          _ = _ := by unfold coeff; ring
      · apply Summable.of_nonneg_of_le (fun s ↦ mul_nonneg (w_nn s) (Nat.cast_nonneg _)) (f := fun s ↦ (n:ℝ)*coeff s)
        · intro s
          calc w s * ((n / den s : ℕ) : ℝ) ≤ w s * ((n:ℝ)/den s) := mul_le_mul_of_nonneg_left Nat.cast_div_le (w_nn s)
            _ = _ := by unfold coeff; ring
        · exact coeff_sum.mul_left _
      · exact coeff_sum.mul_left _
    _ = _ := tsum_mul_left

end TotientMean

open Finset Filter Topology
namespace TotientMean

lemma count_nat (n : ℕ) :
    (∑ t ∈ Icc 1 n, OMA.S_oeis_a069932.a t) =
      ∑ k ∈ Icc 1 n, (n/k.totient - (k-1)/k.totient) := by
  classical
  calc
    _ = ∑ t ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if k ≤ t ∧ k.totient ∣ t then 1 else 0) := by
      apply sum_congr rfl
      intro t ht
      unfold OMA.S_oeis_a069932.a
      rw [card_filter]
      have hsub : Icc 1 t ⊆ Icc 1 n := by
        intro k hk; exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans (mem_Icc.mp ht).2⟩
      calc
        _ = ∑ k ∈ Icc 1 t, (if k ≤ t ∧ k.totient ∣ t then 1 else 0) :=
          sum_congr rfl fun k hk ↦ by simp [(mem_Icc.mp hk).2]
        _ = _ := sum_subset hsub fun k hk hkt ↦ by
          have : ¬k ≤ t := fun h ↦ hkt (mem_Icc.mpr ⟨(mem_Icc.mp hk).1,h⟩)
          simp [this]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k hk
      let A := (Ioc 0 n).filter (fun t ↦ k.totient ∣ t)
      let B := (Ioc 0 (k-1)).filter (fun t ↦ k.totient ∣ t)
      have hB : B ⊆ A := by
        intro t ht
        obtain ⟨hx,hd⟩ := mem_filter.mp ht
        have := mem_Ioc.mp hx
        have := mem_Icc.mp hk
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,by omega⟩,hd⟩
      have eqn : (Icc 1 n).filter (fun t ↦ k ≤ t ∧ k.totient ∣ t) = A \ B := by
        apply Finset.ext
        intro t
        simp only [A,B,mem_filter,mem_Icc,mem_Ioc,mem_sdiff]
        have := mem_Icc.mp hk
        by_cases hv : k.totient ∣ t <;> simp [hv] <;> omega
      rw [← card_filter,eqn,card_sdiff_of_subset hB]
      simp [A,B,Nat.Ioc_filter_dvd_card_eq_div]

lemma count_real (n : ℕ) :
    (∑ t ∈ Icc 1 n, (OMA.S_oeis_a069932.a t : ℝ)) =
       ∑ k ∈ Icc 1 n, (((n/k.totient : ℕ):ℝ)-(((k-1)/k.totient:ℕ):ℝ)) := by
  have he:= congrArg (fun a:ℕ ↦ (a:ℝ)) (count_nat n)
  push_cast at he
  rw [he]
  apply sum_congr rfl
  intro k hk
  apply Nat.cast_sub
  exact Nat.div_le_div_right (by have := mem_Icc.mp hk; omega)

lemma count_lower (n : ℕ) :
    (n:ℝ)*(∑ k ∈ Icc 1 n, (k.totient:ℝ)⁻¹) - n - (∑ k ∈ Icc 1 n,(k:ℝ)/k.totient)
      ≤ ∑ t ∈ Icc 1 n, (OMA.S_oeis_a069932.a t:ℝ) := by
  rw [count_real,mul_sum]
  have hcard : (∑ _k ∈ Icc 1 n, (1:ℝ)) = n := by simp
  conv_lhs => lhs; rhs; rw [← hcard]
  rw [← sum_sub_distrib, ← sum_sub_distrib]
  apply sum_le_sum
  intro k hk
  have hk' := (mem_Icc.mp hk).1
  have ht := Nat.totient_pos.mpr hk'
  have hn : n < (n/k.totient+1)*k.totient := (Nat.div_lt_iff_lt_mul ht).mp (Nat.lt_succ_self _)
  have hR : (n:ℝ) ≤ (((n/k.totient:ℕ):ℝ)+1)*k.totient := by exact_mod_cast hn.le
  have htR : 0<(k.totient:ℝ) := by exact_mod_cast ht
  have h1 := (div_le_iff₀ htR).mpr hR
  have h2 : ((((k-1)/k.totient : ℕ):ℝ)) ≤ (k:ℝ)/k.totient :=
    Nat.cast_div_le.trans (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le k 1) htR.le)
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  linarith

lemma count_upper (n : ℕ) :
    (∑ t ∈ Icc 1 n, (OMA.S_oeis_a069932.a t:ℝ)) ≤
      (n:ℝ) * ∑ k ∈ Icc 1 n,(k.totient:ℝ)⁻¹ := by
  rw [count_real,mul_sum]
  apply sum_le_sum
  intro k _
  have h : ((n/k.totient:ℕ):ℝ) ≤ n*(k.totient:ℝ)⁻¹ := Nat.cast_div_le
  exact (sub_le_self _ (Nat.cast_nonneg _)).trans h

end TotientMean

open Filter Topology Finset
namespace TotientMean
lemma reciprocal_limit :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, (k.totient:ℝ)⁻¹)/Real.log n)
      atTop (𝓝 (∑' s, coeff s)) := by
  let f (n : ℕ) (s : Finset ℕ) := coeff s * ((harmonic (n/den s):ℝ)/Real.log n)
  have hf (s : Finset ℕ) : Tendsto (fun n ↦ f n s) atTop (𝓝 (coeff s)) := by
    by_cases hd : den s = 0
    · simp [f,coeff,hd]
    · simpa [f] using (tendsto_const_nhds (x := coeff s)).mul (hratio (den s) (Nat.pos_of_ne_zero hd))
  have hb : ∀ᶠ n : ℕ in atTop, ∀ s, ‖f n s‖ ≤ 2 * coeff s := by
    have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_ge_atTop 1] with n hn
    intro s
    have hh : 0 ≤ (harmonic (n/den s):ℝ) := by
      by_cases hz : n/den s = 0
      · simp [hz]
      · exact_mod_cast (harmonic_pos hz).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coeff_nn s) (div_nonneg hh (by linarith : 0 ≤ Real.log n)))]
    simpa [f,mul_comm] using mul_le_mul_of_nonneg_left (harmonic_dom (d := den s) hn) (coeff_nn s)
  have ht := tendsto_tsum_of_dominated_convergence (coeff_sum.mul_left 2) hf hb
  convert ht using 1
  funext n
  rw [recip_expand, ← tsum_div_const]
  exact tsum_congr fun s ↦ by unfold f; ring

end TotientMean

open Filter Topology Finset
theorem OMA.solution : type_of% @OMA.S_oeis_a069932.main := by
  let C := ∑' s, TotientMean.coeff s
  refine ⟨C, TotientMean.coeff_sum.tsum_pos TotientMean.coeff_nn ∅ (by simp [TotientMean.coeff,TotientMean.w,TotientMean.den]), ?_⟩
  have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ ↦ (1+C)/Real.log n) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  let F (n : ℕ) := (∑ k ∈ Icc 1 n, (k.totient:ℝ)⁻¹) / Real.log n
  have hF : Tendsto F atTop (𝓝 C) := TotientMean.reciprocal_limit
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ ↦ F n - (1+C)/Real.log n) (h := F)
  · simpa using hF.sub hz
  · exact hF
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
    have hL := Real.log_pos hnR
    have hlow := TotientMean.count_lower n
    have hraw : (∑ k ∈ Icc 1 n,(k:ℝ)/k.totient) ≤ n*C := TotientMean.raw_bound n
    have hp : 0 < (n:ℝ)*Real.log n := mul_pos (by linarith) hL
    apply (le_div_iff₀ hp).mpr
    change ((_ / Real.log n - (1+C)/Real.log n) * ((n:ℝ)*Real.log n)) ≤ _
    rw [← sub_div, mul_comm (n:ℝ), ← mul_assoc, div_mul_cancel₀ _ hL.ne']
    linarith only [hlow,hraw]
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (1:ℝ)<n := by exact_mod_cast (by omega : 1<n)
    have hL := Real.log_pos hnR
    apply (div_le_iff₀ (mul_pos (by linarith : (0:ℝ)<n) hL)).mpr
    have hu := TotientMean.count_upper n
    change _ ≤ (_ / Real.log n) * ((n:ℝ)*Real.log n)
    rw [mul_comm (n:ℝ), ← mul_assoc, div_mul_cancel₀ _ hL.ne', mul_comm]
    exact hu
