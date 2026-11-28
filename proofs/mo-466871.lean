import OMAStatements.S_mo_466871

/-!
Shortening of @connoranderson’s merged proof #31350, retaining the complete
construction from pin 1c17b9487aac08ad16170d7893aec956668ff755. Standard
tightness, indicator-integrability, and zero-projection lemmas replace three
auxiliary arguments.
Source: Tom, MathOverflow 466871 (CC BY-SA 4.0).
-/

namespace OMA.S_mo_466871

open MeasureTheory

noncomputable def tail {n : ℕ} (μ : Measure (E n)) (t : ℝ) : ℝ :=
  μ.real {x | t < ‖x‖}

noncomputable def ptail {n : ℕ} (μ : Measure (E n)) (S : Submodule ℝ (E n)) (t : ℝ) : ℝ :=
  μ.real {x | t < ‖proj S x‖}

end OMA.S_mo_466871

namespace OMA.S_mo_466871

lemma geometry {n k : ℕ} [Nonempty (Fin k)] (S : Fin k → Submodule ℝ (E n))
    (hirr : ∀ x : E n, (∀ i, x∈S i ∨ x∈(S i)ᗮ) → x=0) :
    ∃ c : ℝ, 0<c ∧ c<1 ∧
      (∀ (x : E n) i, c*‖x‖ ≤ max ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖) ∧
      ∀ x : E n, ∃ i, c*‖x‖ ≤ min ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖ := by
  classical
  let g (i : Fin k) (x : E n) := min ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖
  let G := fun x => Finset.univ.sup' Finset.univ_nonempty (fun i => g i x)
  have gc : Continuous G := Continuous.finset_sup'_apply Finset.univ_nonempty
    fun i _ => ((proj (S i)).continuous.norm.min (proj (S i)ᗮ).continuous.norm)
  have hdecomp (i : Fin k) (x : E n) : proj (S i) x + proj (S i)ᗮ x = x := by
    simp [proj,Submodule.starProjection_orthogonal_val]
  have hpos {x : E n} (hx : x≠0) : 0<G x := by
    by_contra! hz
    apply hx (hirr x ?_)
    intro i
    have hi : g i x ≤ 0 := (Finset.le_sup' (fun i => g i x) (Finset.mem_univ i)).trans hz
    simpa only [g, min_le_iff, norm_le_zero_iff, proj,
      Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal, or_comm] using hi
  let K := Metric.sphere (0:E n) 1
  have hδ : ∃ δ : ℝ, 0<δ ∧ ∀ y ∈ K, δ ≤ G y := by
    by_cases hK : K.Nonempty
    · obtain ⟨z,hz,hm⟩ := (isCompact_sphere (0:E n) 1).exists_isMinOn hK gc.continuousOn
      refine ⟨G z,hpos ?_,hm⟩
      intro h
      simp [h] at hz
    · exact ⟨1,zero_lt_one,fun y hy => (hK ⟨y,hy⟩).elim⟩
  obtain ⟨δ,hδ,hK⟩ := hδ
  let c := min δ (1/2)
  have hhalf : c≤1/2 := min_le_right _ _
  refine ⟨c,lt_min hδ (by norm_num),by linarith,?_,?_⟩
  · intro x i
    have hn := norm_add_le (proj (S i) x) (proj (S i)ᗮ x)
    rw [hdecomp] at hn
    have h1 := le_max_left ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖
    have h2 := le_max_right ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖
    nlinarith [mul_le_mul_of_nonneg_right hhalf (norm_nonneg x)]
  · intro x
    by_cases hx : x=0
    · exact ⟨Classical.arbitrary _,by simp [hx]⟩
    let y := ‖x‖⁻¹ • x
    have hn := norm_pos_iff.mpr hx
    have hy : y∈K := by
      simp [K,y,norm_smul,hn.ne']
    obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => g i y)
    have hl : c≤g i y := (min_le_left _ _).trans ((hK y hy).trans hi.le)
    have he : ‖x‖ • y=x := smul_inv_smul₀ hn.ne' _
    have hg : g i x=‖x‖*g i y := by
      conv_lhs => rw [←he]
      simp [g,map_smul,norm_smul,←mul_min_of_nonneg _ _ hn.le]
    refine ⟨i,?_⟩
    change c*‖x‖≤g i x
    rw [hg,mul_comm]
    exact mul_le_mul_of_nonneg_left hl hn.le

end OMA.S_mo_466871

namespace OMA.S_mo_466871
open MeasureTheory
open scoped ENNReal

private lemma recombine_meas {n : ℕ} (S : Submodule ℝ (E n)) : Measurable (recombine S) :=
  ((proj S).continuous.comp continuous_fst).measurable.add
    (((proj Sᗮ).continuous.comp continuous_snd).measurable)

private lemma proj_le_recombine {n : ℕ} (S : Submodule ℝ (E n)) (x y : E n) :
    ‖proj S x‖ ≤ ‖recombine S (x,y)‖ ∧ ‖proj Sᗮ y‖ ≤ ‖recombine S (x,y)‖ := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (proj S x) (proj Sᗮ y)
    ((S.mem_orthogonal _).mp (Sᗮ.starProjection_apply_mem y) _ (S.starProjection_apply_mem x))
  change ‖proj S x‖ ≤ ‖proj S x + proj Sᗮ y‖ ∧ ‖proj Sᗮ y‖ ≤ ‖proj S x + proj Sᗮ y‖
  constructor <;> nlinarith [norm_nonneg (proj S x + proj Sᗮ y),
    sq_nonneg ‖proj S x‖,sq_nonneg ‖proj Sᗮ y‖]

private lemma one_mixture_lower {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (S : Submodule ℝ (E n)) (t : ℝ) :
    (1-tail μ t)*(ptail μ S t+ptail μ Sᗮ t) ≤
      (μ.prod μ).real ((recombine S) ⁻¹' {x | t < ‖x‖}) := by
  let A (U : Submodule ℝ (E n)) : Set (E n) := {x | t < ‖proj U x‖}
  let Z : Set (E n × E n) := (recombine S) ⁻¹' {x | t < ‖x‖}
  have mA U : MeasurableSet (A U) := measurableSet_lt measurable_const (proj U).continuous.norm.measurable
  have mZ : MeasurableSet Z := (recombine_meas S) (measurableSet_lt measurable_const measurable_norm)
  have hsub : Zᶜ ⊆ (A S)ᶜ ×ˢ (A Sᗮ)ᶜ := by
    intro p hp
    have hz : ‖recombine S p‖ ≤ t := le_of_not_gt hp
    obtain ⟨h₁,h₂⟩ := proj_le_recombine S p.1 p.2
    exact ⟨not_lt.mpr (h₁.trans hz),not_lt.mpr (h₂.trans hz)⟩
  have hu := measureReal_mono (μ := μ.prod μ) hsub
  rw [probReal_compl_eq_one_sub mZ,measureReal_prod_prod,probReal_compl_eq_one_sub (mA S),
    probReal_compl_eq_one_sub (mA Sᗮ)] at hu
  have hle (U : Submodule ℝ (E n)) : μ.real (A U) ≤ tail μ t := by
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    exact lt_of_lt_of_le hx (U.norm_starProjection_apply_le x)
  change (1-tail μ t)*(μ.real (A S)+μ.real (A Sᗮ)) ≤ (μ.prod μ).real Z
  nlinarith [mul_nonneg (sub_nonneg.mpr (hle S)) (measureReal_nonneg (μ := μ) (s := A Sᗮ)),
    mul_nonneg (measureReal_nonneg (μ := μ) (s := A S)) (show 0 ≤ tail μ t from measureReal_nonneg)]

lemma mixture_lower {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (S : Fin k → Submodule ℝ (E n)) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (_hsum : ∑ i, p i = 1) (hmix : μ = mix μ S p) (t : ℝ) (_ht : 0 ≤ t) :
    (1-tail μ t)*(∑ i, p i*(ptail μ (S i) t+ptail μ (S i)ᗮ t)) ≤ tail μ t := by
  let Z : Set (E n) := {x | t < ‖x‖}
  have mZ : MeasurableSet Z := measurableSet_lt measurable_const measurable_norm
  have he : tail μ t = ∑ i, p i * (μ.prod μ).real ((recombine (S i)) ⁻¹' Z) := by
    calc
      _ = (mix μ S p).real Z := congrArg (fun ν : Measure (E n) => ν.real Z) hmix
      _ = _ := by
        unfold mix Measure.real
        rw [Measure.finsetSum_apply,ENNReal.toReal_sum (fun i _ => by
          rw [Measure.smul_apply,Measure.map_apply (recombine_meas _) mZ,smul_eq_mul]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))]
        apply Finset.sum_congr rfl
        intro i _
        rw [Measure.smul_apply,Measure.map_apply (recombine_meas _) mZ]
        simp [ENNReal.toReal_ofReal (hp i).le]
  conv_rhs => rw [he]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := mul_le_mul_of_nonneg_left (one_mixture_lower μ (S i) t) (hp i).le
  dsimp only [Z] at *
  linarith only [h]

end OMA.S_mo_466871

namespace OMA.S_mo_466871

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable def hit (t a : ℝ) : ℝ := if t < a then 1 else 0

lemma hit_nonneg (t a : ℝ) : 0 ≤ hit t a := by
  unfold hit
  split <;> norm_num

lemma hit_integrable {n} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (t : ℝ) (f : E n → ℝ) (hf : Continuous f) :
    Integrable (fun x => hit t (f x)) μ := by
  classical
  convert! (integrable_const (μ := μ) (1 : ℝ)).indicator
    (measurableSet_lt measurable_const hf.measurable) using 1

lemma hit_integral {n} (μ : Measure (E n)) (t : ℝ) (f : E n → ℝ) (hf : Continuous f) :
    (∫ x, hit t (f x) ∂μ) = μ.real {x | t < f x} := by
  classical
  have hm : MeasurableSet {x | t < f x} := measurableSet_lt measurable_const hf.measurable
  simpa [hit, Set.indicator, Pi.one_def] using integral_indicator_one (μ := μ) hm

lemma incidence {n k} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (S : Fin k → Submodule ℝ (E n)) (p : Fin k → ℝ) (hp : ∀ i, 0 < p i)
    (hsum : ∑ i, p i = 1) (c δ : ℝ) (hc : 0 < c) (hδ : ∀ i, δ ≤ p i)
    (hmax : ∀ x i, c * ‖x‖ ≤ max ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖)
    (hmin : ∀ x, ∃ i, c * ‖x‖ ≤ min ‖proj (S i) x‖ ‖proj (S i)ᗮ x‖)
    (t : ℝ) : (1+δ) * tail μ (t/c) ≤
      ∑ i, p i * (ptail μ (S i) t + ptail μ (S i)ᗮ t) := by
  classical
  let a (i : Fin k) (x : E n) := hit t ‖proj (S i) x‖
  let b (i : Fin k) (x : E n) := hit t ‖proj (S i)ᗮ x‖
  have ha i : Integrable (a i) μ := hit_integrable _ _ _ (proj (S i)).continuous.norm
  have hb i : Integrable (b i) μ := hit_integrable _ _ _ (proj (S i)ᗮ).continuous.norm
  have hab i : Integrable (fun x => p i * (a i x + b i x)) μ :=
    ((ha i).add (hb i)).const_mul (p i)
  have hpw (x : E n) : (1+δ) * hit (t/c) ‖x‖ ≤ ∑ i, p i * (a i x + b i x) := by
    by_cases hx : t/c < ‖x‖
    · have htx : t < c * ‖x‖ := by simpa [mul_comm] using (div_lt_iff₀ hc).mp hx
      obtain ⟨j,hj⟩ := hmin x
      have hj' := lt_min_iff.mp (htx.trans_le hj)
      have hj2 : a j x + b j x = 2 := by norm_num [a,b,hit,hj'.1,hj'.2]
      have hbase i : 1 ≤ a i x + b i x := by
        rcases lt_max_iff.mp (htx.trans_le (hmax x i)) with hi | hi
        · simp only [a,hit,if_pos hi]
          linarith [hit_nonneg t ‖proj (S i)ᗮ x‖]
        · simp only [b,hit,if_pos hi]
          linarith [hit_nonneg t ‖proj (S i) x‖]
      have hrest : ∑ i ∈ Finset.univ.erase j, p i ≤
          ∑ i ∈ Finset.univ.erase j, p i * (a i x + b i x) :=
        Finset.sum_le_sum fun i _ => by simpa using
          (mul_le_mul_of_nonneg_left (hbase i) (hp i).le)
      have htotal := Finset.sum_erase_add (s := Finset.univ) p (Finset.mem_univ j)
      rw [hsum] at htotal
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hj2]
      simp only [hit,if_pos hx,mul_one]
      linarith [hδ j]
    · simp only [hit,if_neg hx,mul_zero]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i).le
        (add_nonneg (hit_nonneg ..) (hit_nonneg ..))
  have hi := integral_mono ((hit_integrable μ (t/c) _ continuous_norm).const_mul (1+δ))
    (integrable_finsetSum Finset.univ fun i _ => hab i) hpw
  rw [integral_const_mul,hit_integral μ _ _ continuous_norm,integral_finsetSum] at hi
  · refine hi.trans_eq (Finset.sum_congr rfl ?_)
    intro i _
    rw [integral_const_mul,integral_add (ha i) (hb i)]
    simp only [a,b,hit_integral μ t _ (proj (S i)).continuous.norm,
      hit_integral μ t _ (proj (S i)ᗮ).continuous.norm,ptail]
  · exact fun i _ => hab i

lemma small_tail {n} (μ : Measure (E n)) [IsProbabilityMeasure μ] (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 0 < T ∧ ∀ t ≥ T, tail μ t ≤ ε := by
  have hlim : Tendsto (fun t : ℝ => μ {x | t < ‖x‖}) atTop (𝓝 0) := by
    simpa using tendsto_measure_norm_gt_of_isTightMeasureSet
      (isTightMeasureSet_singleton (μ := μ))
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hlim
  obtain ⟨T, hT, ht⟩ := ((hreal.eventually (gt_mem_nhds hε)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  refine ⟨T, ht, fun t htt => ?_⟩
  exact (measureReal_mono (fun x hx => lt_of_le_of_lt htt hx)).trans hT.le

end OMA.S_mo_466871

namespace OMA.S_mo_466871

open MeasureTheory Set Real

lemma log_integrable_of_tail {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (C h T : ℝ) (hC : 1 < C) (hh0 : 0 ≤ h) (hh1 : h < 1) (hT : 0 < T)
    (hrec : ∀ t ≥ T, tail μ (C*t) ≤ h*tail μ t) :
    Integrable (fun x : E n => Real.log (1+‖x‖)) μ := by
  classical
  let R := fun k : ℕ => T*C^k
  let S := fun k : ℕ => {x : E n | R k < ‖x‖ ∧ ‖x‖ ≤ R (k+1)}
  let g := fun x : E n => Real.log (1+‖x‖)
  let B := fun k : ℕ => log (1+T)+(k+1:ℝ)*log C
  have hcp : 0 < C := zero_lt_one.trans hC
  have hR (k : ℕ) : T ≤ R k := by
    exact le_mul_of_one_le_right hT.le (one_le_pow₀ hC.le)
  have htail (k : ℕ) : tail μ (R k) ≤ h^k*tail μ T := by
    induction k with
    | zero => simp [R]
    | succ k ih =>
      have hr : R (k+1)=C*R k := by dsimp [R]; rw [pow_succ]; ring
      rw [hr,pow_succ]
      exact (hrec (R k) (hR k)).trans (by
        simpa [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left ih hh0)
  have hg : Continuous g := (continuous_const.add continuous_norm).log (by
    intro x; change 1+‖x‖ ≠ 0; positivity)
  have hgi (r : ℝ) : IntegrableOn g (Metric.closedBall 0 r) μ :=
    hg.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hs (k : ℕ) : MeasurableSet (S k) :=
    (measurableSet_lt measurable_const continuous_norm.measurable).inter
      (measurableSet_le continuous_norm.measurable measurable_const)
  have hi (k : ℕ) : IntegrableOn g (S k) μ :=
    (hgi (R (k+1))).mono_set (fun x hx => by simpa [Metric.mem_closedBall] using hx.2)
  have hB (k : ℕ) : 0 ≤ B k := add_nonneg (log_nonneg (by linarith))
    (mul_nonneg (by positivity) (log_nonneg hC.le))
  have hb (k : ℕ) (x : E n) (hx : x ∈ S k) : ‖g x‖ ≤ B k := by
    rw [Real.norm_eq_abs,abs_of_nonneg (log_nonneg (by linarith [norm_nonneg x]) : 0 ≤ g x)]
    calc
      g x ≤ log ((1+T)*C^(k+1)) := by
        apply Real.log_le_log (by positivity)
        have e : ‖x‖ ≤ T*C^(k+1) := hx.2
        nlinarith [one_le_pow₀ (n := k+1) hC.le]
      _ = B k := by simp [B,log_mul (by positivity : (1+T:ℝ) ≠ 0) (pow_ne_zero _ hcp.ne'),log_pow]
  have hI (k : ℕ) : (∫ x in S k, ‖g x‖ ∂μ) ≤ B k*(h^k*tail μ T) := by
    calc
      _ ≤ ∫ _ in S k, B k ∂μ := integral_mono_ae (hi k).norm (integrable_const _)
        ((ae_restrict_iff' (hs k)).mpr (Filter.Eventually.of_forall (hb k)))
      _ = B k*μ.real (S k) := by simp [mul_comm]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (hB k)
        exact (measureReal_mono (fun x hx => hx.1 : S k ⊆ {x | R k < ‖x‖})).trans (htail k)
  have hgeom := summable_geometric_of_lt_one hh0 hh1
  have hlin : Summable (fun k : ℕ => (k:ℝ)*h^k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa [Real.norm_eq_abs,abs_of_nonneg hh0] using hh1 : ‖h‖ < 1)
  have hsum : Summable (fun k => B k*(h^k*tail μ T)) := by
    apply (((hgeom.mul_left (log (1+T)+log C)).add (hlin.mul_left (log C))).mul_right (tail μ T)).congr
    intro k
    dsimp [B]; ring
  have hu := integrableOn_iUnion_of_summable_integral_norm hi
    (hsum.of_nonneg_of_le (fun k => integral_nonneg (fun x => norm_nonneg _)) hI)
  have cover : univ ⊆ Metric.closedBall (0:E n) T ∪ ⋃ k, S k := by
    intro x _
    by_cases h : ‖x‖ ≤ T
    · exact Or.inl (by simpa [Metric.mem_closedBall] using h)
    apply Or.inr
    obtain ⟨k,hk⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hC).eventually_gt_atTop (‖x‖/T)).exists
    have ex : ∃ k, ‖x‖ ≤ R k := ⟨k,by
      simpa [R,mul_comm] using ((div_lt_iff₀ hT).mp hk).le⟩
    obtain ⟨k,ek⟩ : ∃ k, Nat.find ex = k+1 := by
      have hz : Nat.find ex ≠ 0 := by
        intro e
        have he := Nat.find_spec ex
        rw [e] at he
        exact h (by simpa [R] using he)
      exact Nat.exists_eq_succ_of_ne_zero hz
    refine Set.mem_iUnion.mpr ⟨k,?_,?_⟩
    · exact lt_of_not_ge (fun hk => (Nat.find_min ex (by omega : k < Nat.find ex)) hk)
    · simpa [← ek] using Nat.find_spec ex
  exact integrableOn_univ.mp (((hgi T).union hu).mono_set cover)

end OMA.S_mo_466871

open MeasureTheory OMA.S_mo_466871

theorem OMA.solution : type_of% @OMA.S_mo_466871.main := by
  classical
  intro n k μ hμ S p hp hsum hirr hmix
  have : Nonempty (Fin k) := by
    by_contra! hempty
    have : IsEmpty (Fin k) := hempty
    simp at hsum
  obtain ⟨j,_,hj⟩ := Finset.exists_min_image Finset.univ p Finset.univ_nonempty
  let δ := p j
  have hδ : 0 < δ := hp j
  obtain ⟨c,hc,hc1,hmax,hmin⟩ := geometry S hirr
  obtain ⟨T,hT,hsmall⟩ := small_tail μ (δ / (2*(1+δ))) (by positivity)
  have hcoef : 0 < 1+δ/2 := by linarith
  apply log_integrable_of_tail μ (1/c) (1/(1+δ/2)) T
    ((lt_div_iff₀ hc).mpr (by linarith)) (by positivity)
    ((div_lt_iff₀ hcoef).mpr (by linarith)) hT
  intro t ht
  have hsm := (le_div_iff₀ (by positivity : 0<2*(1+δ))).mp (hsmall t ht)
  have ha : 1+δ/2 ≤ (1-tail μ t)*(1+δ) := by nlinarith
  have htail : 0 ≤ tail μ (t/c) := measureReal_nonneg
  have hn : 0 ≤ 1-tail μ t := by
    by_contra! hneg
    have := mul_neg_of_neg_of_pos hneg (by linarith : 0<1+δ)
    linarith
  have hi := incidence μ S p hp hsum c δ hc (fun i => hj i (Finset.mem_univ i)) hmax hmin t
  have hl := mixture_lower μ S p hp hsum hmix t (hT.le.trans ht)
  have h1 := (mul_le_mul_of_nonneg_right ha htail).trans
    ((le_of_eq (mul_assoc _ _ _)).trans ((mul_le_mul_of_nonneg_left hi hn).trans hl))
  rw [show 1 / c * t = t/c by ring, show 1/(1+δ/2)*tail μ t = tail μ t/(1+δ/2) by ring]
  exact (le_div_iff₀ hcoef).mpr (by linarith)
