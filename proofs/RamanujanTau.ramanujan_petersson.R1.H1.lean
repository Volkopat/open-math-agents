import OMAReductions.R_RamanujanTau_ramanujan_petersson_R1

namespace OMA.H1Aux
open PowerSeries PowerSeries.WithPiTopology

lemma dvd_prod_sub_one {ι : Type*} {R : Type*} [CommRing R] (a : R) (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, a ∣ f i - 1) : a ∣ (∏ i ∈ s, f i) - 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons]
    have h1 := h i (Finset.mem_cons_self i s)
    have h2 := ih (fun j hj => h j (Finset.mem_cons_of_mem hj))
    have : f i * ∏ j ∈ s, f j - 1 = f i * ((∏ j ∈ s, f j) - 1) + (f i - 1) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right h2 _) h1

noncomputable def fp (N : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range N, (1 - X ^ (i+1)) ^ 24

lemma coeff_tprod_eq (N j : ℕ) (hj : j ≤ N) :
    coeff j (∏' (n : ℕ+), ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24) = coeff j (fp N) := by
  have hP := RamanujanTau.multipliable.hasProd
  have ht : Filter.Tendsto
      (fun s : Finset ℕ+ => coeff j (∏ n ∈ s, ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24))
      Filter.atTop
      (nhds (coeff j (∏' (n : ℕ+), ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24))) :=
    ((continuous_coeff ℤ j).tendsto _).comp hP
  rw [nhds_discrete, Filter.tendsto_pure, Filter.eventually_atTop] at ht
  obtain ⟨s0, hs0⟩ := ht
  let T : Finset ℕ+ := (Finset.range N).map ⟨Nat.succPNat, fun a b h => by simpa using h⟩
  have hT : ∏ n ∈ T, ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24 = fp N := by
    simp only [T, fp, Finset.prod_map]
    rfl
  have hsub : T ⊆ s0 ∪ T := Finset.subset_union_right
  rw [← hs0 (s0 ∪ T) Finset.subset_union_left, ← Finset.prod_sdiff hsub, hT]
  have hd : X ^ (N+1) ∣
      (∏ n ∈ (s0 ∪ T) \ T, ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24) - 1 := by
    apply dvd_prod_sub_one
    intro n hn
    have hnT : n ∉ T := (Finset.mem_sdiff.mp hn).2
    have hnN : N + 1 ≤ (n : ℕ) := by
      by_contra hc
      apply hnT
      simp only [T, Finset.mem_map, Finset.mem_range]
      have hpos := n.pos
      have hlt : (n : ℕ) - 1 < N := by omega
      refine ⟨(n : ℕ) - 1, hlt, ?_⟩
      apply PNat.eq
      show (n : ℕ) - 1 + 1 = n
      omega
    have h1 : ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) - 1 ∣
        ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) ^ 24 - 1 ^ 24 := sub_dvd_pow_sub_pow _ _ _
    rw [one_pow] at h1
    refine dvd_trans ?_ h1
    rw [show ((1 : PowerSeries ℤ) - X ^ (n : ℕ)) - 1 = -X ^ (n:ℕ) by ring, dvd_neg]
    exact pow_dvd_pow _ hnN
  obtain ⟨r, hr⟩ := hd
  rw [sub_eq_iff_eq_add] at hr
  rw [hr, add_mul, one_mul, map_add, mul_assoc, coeff_X_pow_mul', if_neg (by omega), zero_add]

lemma tau_eq (k N : ℕ) (h : k ≤ N) : RamanujanTau.τ k = coeff k (X * fp N) := by
  cases k with
  | zero => simp [RamanujanTau.τ, RamanujanTau.Δ]
  | succ j =>
    simp only [RamanujanTau.τ, RamanujanTau.Δ, coeff_succ_X_mul]
    exact coeff_tprod_eq N j (by omega)

noncomputable def pN (N : ℕ) : Polynomial ℂ :=
  Polynomial.X * (∏ i ∈ Finset.range N, (1 - Polynomial.X ^ (i+1))) ^ 24

lemma pN_coeff (k N : ℕ) (h : k ≤ N) : (pN N).coeff k = (RamanujanTau.τ k : ℂ) := by
  let p : Polynomial ℤ := Polynomial.X * ∏ i ∈ Finset.range N, (1 - Polynomial.X ^ (i+1)) ^ 24
  have h1 : (p : PowerSeries ℤ) = X * fp N := by
    simp only [p, fp, Polynomial.coe_mul, Polynomial.coe_X]
    congr 1
    exact (map_prod (Polynomial.coeToPowerSeries.ringHom (R := ℤ))
      (fun i => (1 - Polynomial.X ^ (i+1)) ^ 24) (Finset.range N)).trans (by simp)
  have h2 : pN N = p.map (Int.castRingHom ℂ) := by
    simp [p, pN, Polynomial.map_prod, Finset.prod_pow]
  rw [tau_eq k N h, ← h1, Polynomial.coeff_coe, h2, Polynomial.coeff_map]
  simp

lemma iter_eval (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) = fun x => (Polynomial.derivative^[k] p).eval x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    rw [Polynomial.deriv, Function.iterate_succ_apply']

lemma iter_eval_zero (p : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) 0 = (k.factorial : ℂ) * p.coeff k := by
  rw [iter_eval]
  show Polynomial.eval 0 _ = _
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

lemma const_tluo {f : ℂ → ℂ} {s : Set ℂ} :
    TendstoLocallyUniformlyOn (fun (_ : ℕ) => f) f Filter.atTop s := by
  intro u hu x _
  exact ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩

noncomputable def G (q : ℂ) : ℂ := ∏' i, (1 - q ^ (i + 1))

noncomputable def F' (q : ℂ) : ℂ := q * G q ^ 24

lemma pN_eval (N : ℕ) (q : ℂ) :
    (pN N).eval q = q * (∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) ^ 24 := by
  simp [pN, Polynomial.eval_prod]

lemma tluo_F : TendstoLocallyUniformlyOn (fun N q => (pN N).eval q) F' Filter.atTop
    (Metric.ball (0 : ℂ) 1) := by
  have hG : ContinuousOn G (Metric.ball (0 : ℂ) 1) :=
    ModularForm.differentiableOn_tprod_one_sub_pow.continuousOn
  have hP : TendstoLocallyUniformlyOn (fun N q => ∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) G
      Filter.atTop (Metric.ball (0 : ℂ) 1) :=
    ModularForm.multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
  have hpow : ∀ m : ℕ, TendstoLocallyUniformlyOn
      (fun N q => (∏ i ∈ Finset.range N, (1 - q ^ (i + 1))) ^ m) (fun q => G q ^ m)
      Filter.atTop (Metric.ball (0 : ℂ) 1) := by
    intro m
    induction m with
    | zero => simpa using (const_tluo (f := fun _ => (1 : ℂ)))
    | succ m ih =>
      have := ih.mul₀ hP (hG.pow m) hG
      convert this using 1
      · ext N q
        simp [pow_succ]
      · ext q
        simp [pow_succ]
  have := (const_tluo (f := fun q : ℂ => q)).mul₀ (hpow 24) continuousOn_id (hG.pow 24)
  convert this using 1
  · ext N q
    simp [pN_eval]
  · ext q
    simp [F']

lemma tluo_iter (k : ℕ) : TendstoLocallyUniformlyOn
    (fun N => iteratedDeriv k (fun q => (pN N).eval q)) (iteratedDeriv k F') Filter.atTop
    (Metric.ball (0 : ℂ) 1) := by
  induction k with
  | zero => simpa using tluo_F
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ih.deriv (Filter.Eventually.of_forall fun N => by
      rw [iter_eval]; exact (Polynomial.differentiable _).differentiableOn) Metric.isOpen_ball

lemma iter_F'_zero (k : ℕ) :
    iteratedDeriv k F' 0 = (k.factorial : ℂ) * (RamanujanTau.τ k : ℂ) := by
  have h := (tluo_iter k).tendsto_at (Metric.mem_ball_self (one_pos : (0 : ℝ) < 1))
  have h2 : ∀ᶠ N in Filter.atTop, iteratedDeriv k (fun q => (pN N).eval q) 0 =
      (k.factorial : ℂ) * (RamanujanTau.τ k : ℂ) := by
    filter_upwards [Filter.eventually_ge_atTop k] with N hN
    rw [iter_eval_zero, pN_coeff k N hN]
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (h2.mono fun N h => h.symm))

lemma cusp_eq : UpperHalfPlane.cuspFunction 1 ModularForm.discriminant =ᶠ[nhds 0] F' := by
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (one_pos : (0 : ℝ) < 1))]
    with q hq
  rw [ModularForm.discriminant_cuspFunction_eqOn hq]
  simp only [F', G]
  rw [(ModularForm.multipliable_one_sub_pow (by simpa using hq)).tprod_pow]

lemma iter_eventually {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) (k : ℕ) :
    iteratedDeriv k f =ᶠ[nhds 0] iteratedDeriv k g := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    simp only [iteratedDeriv_succ]
    exact ih.deriv

end OMA.H1Aux

theorem OMA.solution : OMA.R_RamanujanTau_ramanujan_petersson_R1.H1 := by
  intro n
  rw [UpperHalfPlane.qExpansion_coeff, (OMA.H1Aux.iter_eventually OMA.H1Aux.cusp_eq n).eq_of_nhds,
    OMA.H1Aux.iter_F'_zero, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), one_mul]

