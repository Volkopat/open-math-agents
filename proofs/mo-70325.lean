import OMAStatements.S_mo_70325

namespace OMA.S_mo_70325
open MeasureTheory Set
open scoped ENNReal
lemma edges_box (n : ℕ) : parallelepiped (edges n) = Set.Icc 0 (fun _ => (n:ℝ)⁻¹) := by
  change parallelepiped (fun i : Fin n => Pi.single i ((n:ℝ)⁻¹)) = _
  rw [parallelepiped_single (fun _ : Fin n => (n:ℝ)⁻¹),Set.uIcc_of_le]
  exact fun i => inv_nonneg.mpr (Nat.cast_nonneg n)
lemma edges_subset {n : ℕ} (hn : 0<n) : parallelepiped (edges n) ⊆ cone n := by
  rw [edges_box]
  intro x hx
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have h0 : ∀ i,0≤x i := hx.1
  refine ⟨Finset.sum_nonneg (fun i _ => h0 i),?_,Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => h0 i)⟩
  calc height x ≤ ∑ _ : Fin n,(n:ℝ)⁻¹ := Finset.sum_le_sum (fun i _ => hx.2 i)
       _ = 1 := by simp [hn'.ne']
lemma edges_volume (n : ℕ) : volume (parallelepiped (edges n)) = ENNReal.ofReal ((n:ℝ)⁻¹ ^ n) := by
  rw [edges_box,Real.volume_Icc_pi,ENNReal.ofReal_pow (inv_nonneg.mpr (Nat.cast_nonneg n))]
  simp
lemma gen_data {n : ℕ} (v : Fin n → X n) (hp : parallelepiped v ⊆ cone n) :
    (∀ i, v i ∈ cone n) ∧ ∑ i,height (v i) ≤ 1 := by
  constructor
  · intro i
    apply hp
    refine (mem_parallelepiped_iff v _).2 ⟨Pi.single i (1:ℝ),⟨?_,?_⟩,?_⟩
    · intro j
      by_cases h:j=i <;> simp [h]
    · intro j
      by_cases h:j=i <;> simp [h]
    · simp [Pi.single_apply,ite_smul]
  · have h : ∑ i,v i ∈ parallelepiped v := by
      refine (mem_parallelepiped_iff v _).2 ⟨1,⟨zero_le_one,le_rfl⟩,?_⟩
      simp
    have hh := (hp h).2.1
    change (∑ j, (∑ i,v i) j) ≤ 1 at hh
    simp only [Finset.sum_apply] at hh
    unfold height
    rw [Finset.sum_comm]
    exact hh
lemma para_volume {n : ℕ} (v : Fin n → X n) :
    volume (parallelepiped v) = ENNReal.ofReal |(Matrix.of v).det| := by
  rw [← addHaarMeasure_eq_volume_pi,← Module.Basis.parallelepiped_basisFun,← Module.Basis.addHaar_def,
    Measure.addHaar_parallelepiped,Pi.basisFun_det_apply]
end OMA.S_mo_70325

namespace OMA.S_mo_70325
open MeasureTheory
open scoped ENNReal
lemma ballVolume_pos (n : ℕ) : 0 < ballVolume n := by
  apply div_pos
  · apply pow_pos
    exact mul_pos two_pos (Real.Gamma_pos_of_pos (by norm_num))
  · exact Real.Gamma_pos_of_pos (by positivity)
lemma cone_volume_le_ball {n : ℕ} (hn : 0<n) : volume (cone n) ≤ ENNReal.ofReal (ballVolume n) := by
  let _ : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let B := {x : X n | (∑ i, |x i| ^ (2:ℝ)) ^ (1/2:ℝ) ≤ 1}
  have hsub : cone n ⊆ B := by
    intro x hx
    change (∑ i, |x i| ^ (2:ℝ)) ^ (1/2:ℝ) ≤ 1
    simp only [Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_sqrt hx.2.2).trans ((Real.sqrt_sq hx.1).le.trans hx.2.1)
  apply (measure_mono hsub).trans
  have h := MeasureTheory.volume_sum_rpow_le (ι:=Fin n) (p:=2) (by norm_num) 1
  simpa [B,ballVolume] using h.le
lemma bound_from_ball {n : ℕ} (hn : 0<n) :
    ENNReal.ofReal (((n:ℝ)⁻¹^n)/ballVolume n) * volume (cone n) ≤ volume (parallelepiped (edges n)) := by
  calc _ ≤ ENNReal.ofReal (((n:ℝ)⁻¹^n)/ballVolume n) * ENNReal.ofReal (ballVolume n) :=
          mul_le_mul le_rfl (cone_volume_le_ball hn) zero_le zero_le
       _ = _ := by
         rw [← ENNReal.ofReal_mul' (ballVolume_pos n).le,div_mul_cancel₀ _ (ballVolume_pos n).ne',edges_volume]
end OMA.S_mo_70325

namespace OMA.S_mo_70325
open Matrix Finset

lemma abs_det_le_prod_height {n : ℕ} (v : Fin n → X n) (hv : ∀ i,v i ∈ cone n) :
    |(Matrix.of v).det| ≤ ∏ i,height (v i) := by
  let E := EuclideanSpace ℝ (Fin n)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let w (i : Fin n) : E := WithLp.toLp 2 (v i)
  let _ : Fact (Module.finrank ℝ E = n) := ⟨finrank_euclideanSpace_fin⟩
  have h := b.toBasis.orientation.abs_volumeForm_apply_le w
  rw [b.toBasis.orientation.volumeForm_robust b rfl,Module.Basis.det_apply] at h
  have he : b.toBasis.toMatrix w=(Matrix.of v)ᵀ := by ext; rfl
  rw [he,Matrix.det_transpose] at h
  apply h.trans
  apply Finset.prod_le_prod (fun i _ => norm_nonneg (w i))
  intro i _
  apply le_of_sq_le_sq _ (hv i).1
  rw [EuclideanSpace.real_norm_sq_eq (w i)]
  exact (hv i).2.2

lemma det_upper {n : ℕ} (hn : 0 < n) (v : Fin n → X n) (hv : ∀ i,v i ∈ cone n)
    (hs : ∑ i,height (v i) ≤ 1) : |(Matrix.of v).det| ≤ (n:ℝ)⁻¹^n := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean (univ : Finset (Fin n)) (fun _ => 1)
    (fun i => height (v i)) (by simp) (by simpa using hn') (fun i _ => (hv i).1)
  simp only [Real.rpow_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
    one_mul] at h
  have hprod : 0 ≤ ∏ i,height (v i) := Finset.prod_nonneg fun i _ => (hv i).1
  have hp := pow_le_pow_left₀ (Real.rpow_nonneg hprod _) h n
  rw [←Real.rpow_natCast,←Real.rpow_mul hprod,inv_mul_cancel₀ hn'.ne',Real.rpow_one] at hp
  apply (abs_det_le_prod_height v hv).trans (hp.trans _)
  apply pow_le_pow_left₀
  · exact div_nonneg (Finset.sum_nonneg fun i _ => (hv i).1) hn'.le
  · simpa only [one_div] using div_le_div_of_nonneg_right hs hn'.le
end OMA.S_mo_70325

namespace OMA.S_mo_70325
open MeasureTheory
open scoped ENNReal
lemma affine_bounds {n : ℕ} (hn : 0<n) (L : X n ≃ₗ[ℝ] X n)
    (hu : ∀ v : Fin n → X n, parallelepiped v ⊆ cone n →
      volume (parallelepiped v) ≤ volume (parallelepiped (edges n))) :
    parallelepiped (L ∘ edges n) ⊆ L '' cone n ∧
    (∀ v : Fin n → X n, parallelepiped v ⊆ L '' cone n →
      volume (parallelepiped v) ≤ volume (parallelepiped (L ∘ edges n))) ∧
    ENNReal.ofReal (((n:ℝ)⁻¹^n)/ballVolume n) * volume (L '' cone n) ≤
      volume (parallelepiped (L ∘ edges n)) := by
  have image_eq (e : X n ≃ₗ[ℝ] X n) (v : Fin n → X n) : e '' parallelepiped v = parallelepiped (e ∘ v) :=
    image_parallelepiped e.toLinearMap v
  have him (v : Fin n → X n) : volume (parallelepiped (L ∘ v)) =
      ENNReal.ofReal |LinearMap.det L.toLinearMap| * volume (parallelepiped v) := by
    rw [← image_eq L v]
    exact Measure.addHaar_image_linearMap volume L.toLinearMap _
  have hc : volume (L '' cone n) =
      ENNReal.ofReal |LinearMap.det L.toLinearMap| * volume (cone n) :=
    Measure.addHaar_image_linearMap volume L.toLinearMap _
  constructor
  · rw [← image_eq L (edges n)]
    exact Set.image_mono (edges_subset hn)
  constructor
  · intro v hv
    let u := L.symm ∘ v
    have he : L ∘ u=v := by funext i; exact L.apply_symm_apply _
    have hs : parallelepiped u ⊆ cone n := by
      change parallelepiped (L.symm ∘ v) ⊆ cone n
      rw [← image_eq]
      rintro _ ⟨x,hx,rfl⟩
      obtain ⟨z,hz,rfl⟩ := hv hx
      simpa using hz
    have hm := mul_le_mul (le_refl (ENNReal.ofReal |LinearMap.det L.toLinearMap|)) (hu u hs) zero_le zero_le
    rwa [← him u,he,← him] at hm
  · rw [hc,him,mul_left_comm]
    exact mul_le_mul le_rfl (bound_from_ball hn) zero_le zero_le
end OMA.S_mo_70325

namespace OMA.S_mo_70325
open MeasureTheory Matrix Set Finset
open scoped InnerProductSpace
private abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)
private def sliceCone (d : ℕ) : Set (ℝ × Euc d) :=
  {p | (0 ≤ p.1 ∧ p.1 ≤ (Real.sqrt (d+1))⁻¹) ∧ ‖p.2‖ ≤ Real.sqrt d*p.1}
private lemma measSlice (d : ℕ) : MeasurableSet (sliceCone d) := by
  have he : sliceCone d = (Prod.fst ⁻¹' Icc 0 (Real.sqrt (d+1))⁻¹) ∩
      {p : ℝ × Euc d | ‖p.2‖ ≤ Real.sqrt d*p.1} := rfl
  rw [he]
  exact (measurable_fst measurableSet_Icc).inter (measurableSet_le (by fun_prop) (by fun_prop))
private lemma chart_volume (d : ℕ) : volume (cone (d+1)) = volume (sliceCone d) := by
  let N : ℝ := d+1
  let r := Real.sqrt N
  have hN : 0<N := by dsimp [N]; positivity
  have hr : 0<r := Real.sqrt_pos.mpr hN
  have hrs : r^2=N := Real.sq_sqrt hN.le
  let u : Euc (d+1) := WithLp.toLp 2 (fun _ => 1)
  let w : Euc (d+1) := EuclideanSpace.single 0 r
  have hu : ‖u‖ = ‖w‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖u‖^2 = ‖(PiLp.single 2 0 r : Euc (d+1))‖^2
    rw [EuclideanSpace.real_norm_sq_eq,PiLp.norm_single]
    simpa [u,Real.norm_eq_abs,abs_of_pos hr,N] using hrs.symm
  let R := (ℝ ∙ (u-w))ᗮ.reflection
  have hR : R u=w := Submodule.reflection_sub hu
  let rot (x : X (d+1)) : X (d+1) := WithLp.ofLp (R (WithLp.toLp 2 x))
  have rot_volume : MeasurePreserving rot := (PiLp.volume_preserving_ofLp _).comp
    (R.measurePreserving.comp (PiLp.volume_preserving_toLp _))
  have rh (x : X (d+1)) : height x = r*(rot x 0) := by
    let v : Euc (d+1) := WithLp.toLp 2 x
    have he := R.inner_map_map u v
    rw [hR] at he
    change height x = r*(R v 0)
    calc height x = inner ℝ u v := by simp [u,v,height,PiLp.inner_apply]
         _ = inner ℝ w (R v) := he.symm
         _ = _ := by simp [w,PiLp.inner_apply,mul_comm]
  have rn (x : X (d+1)) :
      (∑ j,(x j)^2) = (rot x 0)^2+‖WithLp.toLp 2 (fun i : Fin d => rot x i.succ)‖^2 := by
    have h := congrArg (fun t : ℝ => t^2) (R.norm_map (WithLp.toLp 2 x))
    simp only [EuclideanSpace.real_norm_sq_eq] at h ⊢
    rw [←h,Fin.sum_univ_succ]
  let split (y : X (d+1)) : ℝ × Euc d := (y 0,WithLp.toLp 2 (fun i : Fin d => y i.succ))
  have hs : MeasurePreserving split := by
    have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin d))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0)
    convert h using 1 <;> rfl
  have he : cone (d+1) = (split ∘ rot) ⁻¹' (sliceCone d) := by
    ext x
    let s := rot x 0
    let y : Euc d := WithLp.toLp 2 (fun i : Fin d => rot x i.succ)
    change (0 ≤ height x ∧ height x ≤ 1 ∧ (∑ i,(x i)^2) ≤ (height x)^2) ↔
      ((0 ≤ s ∧ s ≤ r⁻¹) ∧ ‖y‖ ≤ Real.sqrt d*s)
    rw [rh,rn]
    change (0 ≤ r*s ∧ r*s ≤ 1 ∧ s^2+‖y‖^2 ≤ (r*s)^2) ↔ _
    rw [mul_nonneg_iff_of_pos_left hr,←le_div_iff₀' hr,one_div]
    have hsq := Real.sq_sqrt (Nat.cast_nonneg d : (0:ℝ) ≤ d)
    constructor
    · rintro ⟨h0,h1,hy⟩
      refine ⟨⟨h0,h1⟩, (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0)).mp ?_⟩
      rw [mul_pow,hrs] at hy
      rw [mul_pow,hsq]
      dsimp [N] at hy
      linarith
    · rintro ⟨⟨h0,h1⟩,hy⟩
      refine ⟨h0,h1,?_⟩
      have he := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0)).mpr hy
      rw [mul_pow,hsq] at he
      rw [mul_pow,hrs]
      dsimp [N]
      linarith
  rw [he,(hs.comp rot_volume).measure_preimage (measSlice _).nullMeasurableSet]
end OMA.S_mo_70325
namespace OMA.S_mo_70325
open MeasureTheory Set Metric
private lemma slice_volume (d : ℕ) :
    volume.real (sliceCone d) =
    (volume : Measure (Euc d)).real (ball 0 1) *
      (Real.sqrt ((d:ℝ)/(d+1)))^d / (((d:ℝ)+1)*Real.sqrt (d+1)) := by
  let r : ℝ := (Real.sqrt (d+1))⁻¹
  let κ := volume (ball (0:Euc d) 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hsec (s : ℝ) : volume ((Prod.mk s) ⁻¹' sliceCone d) =
      κ * (Icc (0:ℝ) r).indicator (fun t : ℝ => ENNReal.ofReal ((Real.sqrt d*t)^d)) s := by
    by_cases hs : s ∈ Icc (0:ℝ) r
    · have he : (Prod.mk s) ⁻¹' sliceCone d = closedBall (0:Euc d) (Real.sqrt d*s) := by
        ext y
        change ((0 ≤ s ∧ s ≤ r) ∧ ‖y‖ ≤ Real.sqrt d*s) ↔ _
        simp [hs.1,hs.2,Metric.mem_closedBall]
      rw [he,Measure.addHaar_closedBall volume _ (mul_nonneg (Real.sqrt_nonneg _) hs.1),
          indicator_of_mem hs]
      simp [κ,mul_comm,finrank_euclideanSpace]
    · have he : (Prod.mk s) ⁻¹' sliceCone d = ∅ := by
        ext y
        change (s ∈ Icc (0:ℝ) r ∧ _) ↔ False
        simp [hs]
      simp [he,hs]
  have hI : ∫ s in Icc (0:ℝ) r, (Real.sqrt d*s)^d =
      (Real.sqrt d)^d * (r^(d+1)/((d:ℝ)+1)) := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hr.le]
    simp_rw [mul_pow]
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp
  have hnn : 0 ≤ (Real.sqrt d)^d * (r^(d+1)/((d:ℝ)+1)) := by positivity
  have hmeasure : volume (sliceCone d) =
      κ * ENNReal.ofReal ((Real.sqrt d)^d * (r^(d+1)/((d:ℝ)+1))) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply (measSlice _)]
    simp_rw [hsec]
    rw [lintegral_const_mul _ ((by fun_prop : Measurable (fun t : ℝ =>
      ENNReal.ofReal ((Real.sqrt d*t)^d))).indicator measurableSet_Icc),
      lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal, hI]
    · exact (by fun_prop : Continuous (fun s : ℝ => (Real.sqrt d*s)^d)).continuousOn.integrableOn_Icc
    · filter_upwards [ae_restrict_mem (μ := (volume:Measure ℝ)) measurableSet_Icc] with s hs
      exact pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hs.1) _
  rw [measureReal_def,hmeasure,ENNReal.toReal_mul,ENNReal.toReal_ofReal hnn]
  change κ.toReal * _ = κ.toReal * _ / _
  rw [Real.sqrt_div (Nat.cast_nonneg d),div_pow]
  dsimp [r]
  rw [pow_succ,inv_pow]
  have hp : 0 < Real.sqrt ((d:ℝ)+1) := by positivity
  field_simp
lemma cone_volume {n : ℕ} (hn : 2 ≤ n) :
    volume.real (cone n) = (volume : Measure (EuclideanSpace ℝ (Fin (n-1)))).real
      (Metric.ball 0 1) * (Real.sqrt (((n-1 : ℕ) : ℝ)/(n:ℝ)))^(n-1) /
        ((n:ℝ)*Real.sqrt n) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [measureReal_def,chart_volume]
  simpa [measureReal_def] using slice_volume d
end OMA.S_mo_70325

open OMA.S_mo_70325
theorem OMA.solution : type_of% @OMA.S_mo_70325.main := by
  refine ⟨fun _ hn => cone_volume hn,edges_volume,fun _ hn L => affine_bounds hn L ?_⟩
  intro v hv
  obtain ⟨h1,h2⟩ := gen_data v hv
  rw [para_volume,edges_volume]
  exact ENNReal.ofReal_le_ofReal (det_upper hn v h1 h2)
