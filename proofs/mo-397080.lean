import OMAStatements.S_mo_397080

namespace OMA.S_mo_397080

private def scaleNat (j : ℕ) := 2^(j+1)
private noncomputable def mass (j : ℕ) : ℝ := ((scaleNat j : ℝ)⁻¹)^2
private noncomputable def gridWeights (m : ℕ) : Fin (m+1) → ℝ :=
  Fin.cases (1-∑ j : Fin m, mass j.val) (fun j => mass j.val)
private noncomputable def gridValues (m : ℕ) : Fin (m+1) → ℝ :=
  Fin.cases 0 (fun j => (scaleNat j.val : ℝ)/(2:ℝ)^m)

private lemma mass_bound (m : ℕ) : (∑ j : Fin m, mass j.val) ≤ 1/2 - (1/2:ℝ)^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hp : 0 < (1/2:ℝ)^(m+1) := by positivity
    have hle : (1/2:ℝ)^(m+1) ≤ 1/2 := by
      rw [pow_succ]
      have := pow_le_one₀ (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) ≤ 1) (n := m)
      linarith
    have hmass : mass m = ((1/2:ℝ)^(m+1))^2 := by simp [mass,scaleNat,inv_pow]
    simp only [Fin.val_castSucc,Fin.val_last,hmass,pow_succ (1/2:ℝ) (m+1)]
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hle)]

private lemma wfirst (m : ℕ) : 1/2 ≤ gridWeights m 0 := by
  simp only [gridWeights,Fin.cases_zero]
  have := mass_bound m
  have hh : 0 ≤ (1/2:ℝ)^(m+1) := by positivity
  linarith

private lemma weights_pos {m : ℕ} (i : Fin (m+1)) : 0≤gridWeights m i := by
  refine Fin.cases (by linarith [wfirst m]) (fun j => ?_) i
  simp [gridWeights,mass]

private lemma weights_sum (m : ℕ) : (∑ i, gridWeights m i) = 1 := by
  rw [Fin.sum_univ_succ]
  simp [gridWeights]

private lemma values_range {m : ℕ} (i : Fin (m+1)) : gridValues m i ∈ Set.Icc (0:ℝ) 1 := by
  refine Fin.cases (by simp [gridValues]) (fun j => ?_) i
  simp only [gridValues,Fin.cases_succ,Set.mem_Icc,scaleNat,Nat.cast_pow,Nat.cast_ofNat]
  exact ⟨by positivity,(div_le_one (by positivity)).mpr (pow_le_pow_right₀ (by norm_num) j.isLt)⟩

private lemma data_sd (m : ℕ) : sd (gridWeights m) (gridValues m) ≤ Real.sqrt m / 2^m := by
  have hsec : (∑ i, gridWeights m i*(gridValues m i)^2) = (m:ℝ)/(2^m)^2 := by
    rw [Fin.sum_univ_succ]
    simp [gridWeights,gridValues,mass,scaleNat,div_pow,inv_pow,←mul_div_assoc]
    rw [div_eq_mul_inv]
  unfold sd
  rw [hsec]
  calc
    Real.sqrt _ ≤ Real.sqrt ((m:ℝ)/(2^m)^2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (∑ i,gridWeights m i*gridValues m i)])
    _ = _ := by rw [Real.sqrt_div (by positivity),Real.sqrt_sq (by positivity)]

private lemma variance_centered {k : ℕ} (w f : Fin k → ℝ) (hw : ∑ i,w i=1) (a : ℝ)
    (ha : a=∑ i,w i*f i) :
    (∑ i,w i*(f i)^2) - (∑ i,w i*f i)^2 = ∑ i,w i*(f i-a)^2 := by
  have H (i : Fin k) : w i*(f i-a)^2 = w i*(f i)^2-2*a*(w i*f i)+a^2*w i := by ring
  simp_rw [H]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,hw,←ha]
  ring

private lemma band_sd {m : ℕ} (j : Fin m) (f : Fin (m+1) → ℝ) (h0 : f 0=0)
    (h1 : f j.succ=1) : (scaleNat j.val : ℝ)⁻¹/2 ≤ sd (gridWeights m) f := by
  let t := ∑ i, gridWeights m i * f i
  have hrest : gridWeights m j.succ*(f j.succ-t)^2 ≤ ∑ i : Fin m, gridWeights m i.succ*(f i.succ-t)^2 :=
    Finset.single_le_sum (fun (i : Fin m) _ => mul_nonneg (weights_pos i.succ) (sq_nonneg (f i.succ-t))) (Finset.mem_univ j)
  have hj : mass j.val ≤ 1/2 := by
    have h := mass_bound m
    have hj := Finset.single_le_sum (fun (i : Fin m) _ => sq_nonneg ((scaleNat i.val:ℝ)⁻¹)) (Finset.mem_univ j)
    change mass j.val ≤ ∑ i : Fin m, mass i.val at hj
    linarith [show 0 ≤ (1/2:ℝ)^(m+1) by positivity]
  have hsec : mass j.val/4 ≤ ∑ i,gridWeights m i*(f i-t)^2 := by
    rw [Fin.sum_univ_succ,h0,zero_sub,neg_sq]
    rw [h1] at hrest
    change mass j.val*(1-t)^2 ≤ _ at hrest
    have hmul := mul_le_mul_of_nonneg_right (hj.trans (wfirst m)) (sq_nonneg t)
    have hpos : 0 ≤ mass j.val := sq_nonneg _
    nlinarith [mul_nonneg hpos (sq_nonneg (t-1/2))]
  unfold sd
  rw [variance_centered _ _ (weights_sum m) t rfl]
  apply Real.le_sqrt_of_sq_le
  convert hsec using 1
  simp [mass,div_pow]
  ring

private lemma dyadic_sum {m q : ℕ} (f : ℕ → ℝ) (hnonneg : ∀ i,0≤f i)
    (hband : ∀ j : ℕ, j < m → ∀ i : ℕ, i < q*2^(j+1) → q*2^j ≤ i → (scaleNat j : ℝ)⁻¹/2 ≤ f i) :
    (m:ℝ)*q/4 ≤ ∑ i ∈ Finset.range (q*2^m), f i := by
  induction m with
  | zero => simpa using Finset.sum_nonneg (s := Finset.range q) (fun i _ => hnonneg i)
  | succ m ih =>
    have hprev := ih (fun j hj i hi hl => hband j (by omega) i hi hl)
    have hlen : q*2^(m+1) = q*2^m + q*2^m := by rw [pow_succ]; ring
    rw [hlen,Finset.sum_range_add]
    have H : (∑ _i ∈ Finset.range (q*2^m), (scaleNat m:ℝ)⁻¹/2) ≤
        ∑ i ∈ Finset.range (q*2^m), f (q*2^m+i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hu := Finset.mem_range.mp hi
      apply hband m (by omega) _ _ (by omega)
      omega
    have he : (∑ _i ∈ Finset.range (q*2^m), (scaleNat m:ℝ)⁻¹/2) = q/4 := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,scaleNat,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,pow_succ]
      field_simp
      ring
    rw [he] at H
    push_cast
    linarith

private lemma average_lower (m b : ℕ) (hb : 0<b) :
    (m:ℝ)/(4*2^m) ≤ (∑ i : Fin (b*2^m),
      sd (gridWeights m) (fun j => ramp (b*2^m) i.val (gridValues m j)))/(b*2^m:ℕ) := by
  let f (i : ℕ) := sd (gridWeights m) (fun j => ramp (b*2^m) i (gridValues m j))
  have H := dyadic_sum (m := m) (q := b) f (fun i => Real.sqrt_nonneg _) (by
    intro j hj i hi _
    apply band_sd ⟨j,hj⟩
    · simp [gridValues,ramp]
    · simp only [gridValues,Fin.cases_succ,ramp,scaleNat]
      have hcast : (i:ℝ)+1 ≤ (b:ℝ)*2^(j+1) := by exact_mod_cast hi
      have he : ((b*2^m:ℕ):ℝ)*(((2^(j+1):ℕ):ℝ)/(2:ℝ)^m) = (b:ℝ)*2^(j+1) := by
        push_cast
        field_simp
      rw [he,min_eq_left (by linarith : (1:ℝ) ≤ (b:ℝ)*2^(j+1)-i)]
      norm_num)
  rw [Finset.sum_range] at H
  have hn : (0:ℝ) < (b*2^m:ℕ) := by positivity
  apply (le_div_iff₀ hn).mpr
  calc
    (m:ℝ)/(4*2^m)*(b*2^m:ℕ) = m*b/4 := by push_cast;field_simp
    _ ≤ _ := H

lemma scalar_counterexample (C : ℝ) :
    ∃ (k : ℕ) (w a : Fin k → ℝ), 0<k ∧ (∀ i, 0≤w i) ∧ (∑ i,w i)=1 ∧
      (∀ i, a i ∈ Set.Icc (0:ℝ) 1) ∧ ∃ δ>0, ∀ N : ℕ, ∃ n≥N, 0<n ∧
        C*sd w a + δ ≤ (∑ i : Fin n, sd w (fun j => ramp n i.val (a j)))/(n:ℝ) := by
  obtain ⟨L,hL⟩ := exists_nat_gt (4*(|C|+1))
  let m := L^2
  let D : ℝ := 2^m
  have hD : 0<D := by dsimp [D]; positivity
  have hLpos : (0:ℝ)<L := by linarith [abs_nonneg C]
  have hm : (m:ℝ)=(L:ℝ)^2 := by simp [m]
  have hδ : 0 < ((m:ℝ)/4 - |C| * L)/D := by
    rw [hm]
    apply div_pos _ hD
    nlinarith [mul_pos hLpos (show (0:ℝ)<L/4 - |C| by linarith)]
  refine ⟨m+1,gridWeights m,gridValues m,by omega,weights_pos,weights_sum m,values_range,
    ((m:ℝ)/4 - |C| * L)/D,hδ,?_⟩
  intro N
  let b := N+1
  have hb : 0<b := by omega
  refine ⟨b*2^m,le_trans (by dsimp [b]; omega : N≤b) (Nat.le_mul_of_pos_right b (by positivity)),
    Nat.mul_pos hb (by positivity),?_⟩
  apply le_trans _ (average_lower m b hb)
  have hbound := data_sd m
  rw [hm,Real.sqrt_sq (by positivity)] at hbound
  have hc := mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg
    ((∑ i,gridWeights m i*(gridValues m i)^2)-(∑ i,gridWeights m i*gridValues m i)^2))
  change C*sd (gridWeights m) (gridValues m) ≤ |C| * sd (gridWeights m) (gridValues m) at hc
  change sd (gridWeights m) (gridValues m) ≤ L/D at hbound
  have hs := hc.trans (mul_le_mul_of_nonneg_left hbound (abs_nonneg C))
  change C*sd (gridWeights m) (gridValues m)+_ ≤ (m:ℝ)/(4*D)
  calc
    _ ≤ |C| * (L/D)+((m:ℝ)/4 - |C| * L)/D := by linarith
    _ = _ := by ring

end OMA.S_mo_397080

namespace OMA.S_mo_397080
open Matrix
open scoped MatrixOrder ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

private def outer {d : ℕ} (u v : Fin d → ℂ) : Mat d := vecMulVec u (star v)

private lemma outer_mul {d : ℕ} (u v x y : Fin d → ℂ) :
    outer u v * outer x y = (star v ⬝ᵥ x) • outer u y := by
  rw [outer, outer, outer, vecMulVec_mul_vecMulVec, vecMulVec_smul]

private lemma outer_adj {d : ℕ} (u v : Fin d → ℂ) : (outer u v)ᴴ = outer v u := by
  simp [outer, conjTranspose_vecMulVec]

private lemma gram_norm {d : ℕ} (u : Fin d → ℂ) :
    star u ⬝ᵥ u = ((∑ i, ‖u i‖^2 : ℝ) : ℂ) := by
  simp [dotProduct, Complex.conj_mul', RCLike.star_def]

noncomputable def householder {d : ℕ} (v : Fin d → ℂ) : Mat d := 1 - (2:ℂ) • outer v v

private lemma householder_adj {d : ℕ} (v : Fin d → ℂ) : (householder v)ᴴ = householder v := by
  simp [householder, outer_adj]

lemma householder_unitary {d : ℕ} (v : Fin d → ℂ) (hv : ∑ i, ‖v i‖^2 = 1) :
    householder v ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, householder_adj]
  simp only [householder, sub_mul, mul_sub, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
    outer_mul, gram_norm, hv, Complex.ofReal_one, one_smul]
  module

private lemma outer_cross_trace {d : ℕ} (v z : Fin d → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hv : star v ⬝ᵥ v = 1) (hz : star z ⬝ᵥ z = 1) (hx : star v ⬝ᵥ z = 0) :
    traceNorm ((-(2*r) : ℂ) • (outer v z + outer z v)) = 4*r := by
  have hy : star z ⬝ᵥ v = 0 := by rw [star_dotProduct, hx, star_zero]
  let B := ((2*r:ℝ) : ℂ) • (outer v v + outer z z)
  have hB : 0 ≤ B := by
    change 0 ≤ ((2*r:ℝ) : ℂ) • (vecMulVec v (star v) + vecMulVec z (star z))
    apply Matrix.PosSemidef.nonneg
    apply ((posSemidef_vecMulVec_self_star _).add (posSemidef_vecMulVec_self_star _)).smul
    exact_mod_cast (show (0:ℝ) ≤ 2*r by positivity)
  unfold traceNorm
  rw [CFC.sqrt_unique (b := B) _ hB]
  · simp [B, trace_smul, outer, dotProduct_comm v (star v), dotProduct_comm z (star z), hv, hz]
    ring
  · simp only [B, conjTranspose_smul, conjTranspose_add, outer_adj, add_mul, mul_add,
      smul_mul_assoc, mul_smul_comm, outer_mul, hx, hy, hv, hz, zero_smul, one_smul,
      add_zero, zero_add]
    simp only [star_neg, star_mul', star_ofNat, Complex.star_def, Complex.conj_ofReal]
    module

private lemma outer_cross_unscaled {d : ℕ} (v w : Fin d → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hv : star v ⬝ᵥ v = 1) (hw : star w ⬝ᵥ w = (r:ℂ)^2) (hx : star v ⬝ᵥ w = 0) :
    traceNorm ((-2:ℂ) • (outer v w + outer w v)) = 4*r := by
  by_cases he : r = 0
  · subst r
    have hzero : w = 0 := by
      rw [gram_norm] at hw
      norm_num at hw
      have hsum : ∑ i, ‖w i‖^2 = 0 := by exact_mod_cast hw
      have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖w i‖)).mp hsum
      funext i
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hi i (Finset.mem_univ i)))
    simp [hzero, outer, traceNorm]
  let z := (r:ℂ)⁻¹ • w
  have hn : (r:ℂ) ≠ 0 := by exact_mod_cast he
  have hz : star z ⬝ᵥ z = 1 := by
    simp [z, star_smul, smul_dotProduct, dotProduct_smul, hw, hn, smul_eq_mul, sq]
  have hxz : star v ⬝ᵥ z = 0 := by simp [z, dotProduct_smul, hx]
  have hwz : w = (r:ℂ) • z := by simp [z, smul_smul, hn]
  convert outer_cross_trace v z r hr hv hz hxz using 2
  rw [hwz]
  simp only [outer, star_smul, vecMulVec_smul, smul_vecMulVec, Complex.star_def, Complex.conj_ofReal]
  module

lemma householder_trace {d : ℕ} (v : Fin d → ℂ) (a : Fin d → ℝ) (hv : ∑ i, ‖v i‖^2 = 1) :
    traceNorm ((householder v)ᴴ * (Matrix.diagonal (fun i => (a i : ℂ))) * householder v -
      Matrix.diagonal (fun i => (a i : ℂ))) =
      4 * Real.sqrt ((∑ i, ‖v i‖^2 * a i^2) - (∑ i, ‖v i‖^2 * a i)^2) := by
  classical
  let p (i : Fin d) := ‖v i‖^2
  let μ := ∑ i, p i*a i
  let b (i : Fin d) := a i-μ
  let w (i : Fin d) := (b i : ℂ)*v i
  let D := Matrix.diagonal fun i => (a i : ℂ)
  let s := ∑ i, p i*b i^2
  have hp : ∑ i, p i = 1 := hv
  have hb : ∑ i, p i*b i = 0 := by
    simp [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, μ]
  have hs : s = (∑ i, p i*a i^2) - μ^2 := by
    have he (i) : p i*b i^2 = p i*a i^2 - (2*μ)*(p i*a i) + μ^2 * p i := by dsimp [b]; ring
    simp only [s, he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
    change _ - 2*μ*μ + μ^2*1 = _ - μ^2
    ring
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hself : star v ⬝ᵥ v = 1 := by rw [gram_norm, hv, Complex.ofReal_one]
  have cross : star v ⬝ᵥ w = 0 := by
    have he (i) : star (v i)*w i = ((p i*b i:ℝ):ℂ) := by
      rw [Complex.ofReal_mul]; change star (v i)*((b i:ℂ)*v i) = _
      rw [mul_left_comm]
      simp only [p, Complex.ofReal_pow, Complex.star_def, Complex.conj_mul']
      ring
    change (∑ i, star (v i)*w i) = 0
    simp only [he, ← Complex.ofReal_sum, hb, Complex.ofReal_zero]
  have hww : star w ⬝ᵥ w = (Real.sqrt s : ℂ)^2 := by
    have he (i) : star (w i)*w i = ((p i*b i^2:ℝ):ℂ) := by
      simp only [w, star_mul', Complex.star_def, Complex.conj_ofReal, Complex.ofReal_mul,
        Complex.ofReal_pow, p]
      rw [← Complex.conj_mul']; ring
    change (∑ i, star (w i)*w i) = _
    simp only [he, ← Complex.ofReal_sum, ← Complex.ofReal_pow, Real.sq_sqrt hs0, s]
  have hd : D*outer v v = outer w v + (μ:ℂ) • outer v v := by
    unfold outer
    rw [mul_vecMulVec]
    ext i j
    simp [D, mulVec_diagonal, w, b, sub_mul, vecMulVec_apply]
    ring
  have hd' : outer v v*D = outer v w + (μ:ℂ) • outer v v := by
    have he := congrArg Matrix.conjTranspose hd
    have hsD : Dᴴ = D := by
      ext i j
      by_cases h : i = j <;> simp [D, conjTranspose_apply, h, Ne.symm]
    simpa [outer_adj, hsD] using he
  have hdh : outer v v*D*outer v v = (μ:ℂ) • outer v v := by
    have hy : star w ⬝ᵥ v = 0 := by rw [star_dotProduct, cross, star_zero]
    rw [hd', add_mul, smul_mul_assoc, outer_mul, outer_mul, hy, hself, zero_smul, one_smul,
      zero_add]
  have hdelta : (householder v)ᴴ*D*householder v-D = (-2:ℂ) • (outer v w + outer w v) := by
    rw [householder_adj]
    calc
      _ = (-2:ℂ) • (outer v v*D + D*outer v v) + (4:ℂ) • (outer v v*D*outer v v) := by
        simp only [householder, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
        module
      _ = _ := by rw [hdh,hd,hd']; module
  change traceNorm _ = 4*Real.sqrt ((∑ i, p i*a i^2)-μ^2)
  rw [← hs, ← show D=Matrix.diagonal (fun i => (a i:ℂ)) from rfl, hdelta]
  exact outer_cross_unscaled v w _ (Real.sqrt_nonneg _) hself hww cross

end OMA.S_mo_397080

open OMA.S_mo_397080

theorem OMA.solution : type_of% @OMA.S_mo_397080.main := by
  intro C
  obtain ⟨k,w,a,hk,hw,h1,ha,δ,hδ,hn⟩ := scalar_counterexample C
  let v (j : Fin k) : ℂ := (Real.sqrt (w j) : ℝ)
  have hvw (j : Fin k) : ‖v j‖^2 = w j := by simp [v,Real.sq_sqrt (hw j)]
  have hv : ∑ j, ‖v j‖^2 = 1 := by simpa only [hvw] using h1
  let r : ℝ := 4/(k:ℝ)
  have hr : 0<r := by dsimp [r]; positivity
  have he (g : Fin k → ℝ) : gap (householder v) g = r*sd w g := by
    dsimp only [gap]
    rw [householder_trace v g hv]
    simp only [hvw,sd,r]
    ring
  refine ⟨k,a,householder v,hk,ha,householder_unitary v hv,r*δ,mul_pos hr hδ,?_⟩
  intro N
  obtain ⟨n,hnN,hn0,hb⟩ := hn N
  refine ⟨n,hnN,hn0,?_⟩
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ = r*(C*sd w a+δ) := by ring
    _ ≤ r*((∑ i : Fin n, sd w (fun j => ramp n i.val (a j)))/(n:ℝ)) :=
      mul_le_mul_of_nonneg_left hb hr.le
    _ = _ := by ring
