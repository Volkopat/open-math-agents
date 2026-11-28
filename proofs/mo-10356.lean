import OMAStatements.S_mo_10356

/-!
# The modulus map on the dual of finitely supported sequences

Bill Johnson answered the question negatively for a Banach predual using the
Mazur map (https://mathoverflow.net/questions/10356/topological-interpolation).
Here we give another counterexample for the stated class of normed spaces.
Take the finitely supported real sequences with the sum norm. On their dual,
coordinatewise absolute value is Lipschitz, and finite support makes every
weak-star evaluation of its output continuous. The weighted mean of that
output is positive on every nonzero input. This rules out weak continuity,
since every basic weak neighborhood of zero contains an entire nonzero line.
-/

noncomputable section

namespace Mo10356Proof

open Filter Set Topology

/-- A finite family of weak coordinates cannot bound a positive homogeneous
    gauge if its common kernel always contains a nonzero vector. -/
lemma no_weak_gauge {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (q : V → ℝ) (hz : q 0 = 0) (hpos : ∀ x ≠ 0, 0 < q x)
    (hscale : ∀ (c : ℝ), 0 < c → ∀ x, q (c • x) = c * q x)
    (hker : ∀ s : Finset (V →L[ℝ] ℝ), ∃ x : V, x ≠ 0 ∧ ∀ f ∈ s, f x = 0) :
    ¬ @Continuous V ℝ (TopologicalSpace.induced (fun x : V => fun f : V →L[ℝ] ℝ => f x)
      inferInstance) inferInstance q := by
  intro hc
  let ev (x : V) (f : V →L[ℝ] ℝ) := f x
  have hq : q ⁻¹' Iio 1 ∈ comap ev (𝓝 (ev 0)) := by
    rw [← nhds_induced]
    have ht := @Continuous.tendsto V ℝ (TopologicalSpace.induced ev inferInstance) _ q hc 0
    exact ht (Iio_mem_nhds (by rw [hz]; norm_num))
  obtain ⟨w, hw, hwq⟩ := Filter.mem_comap.mp hq
  rw [nhds_pi, Filter.mem_pi'] at hw
  obtain ⟨s, U, hU, hUw⟩ := hw
  obtain ⟨x, hx, hzero⟩ := hker s
  have hp := hpos x hx
  let c := (q x)⁻¹
  have hcpos : 0 < c := inv_pos.mpr hp
  have hmem : ev (c • x) ∈ Set.pi (↑s) U := by
    intro f hf
    change f (c • x) ∈ U f
    have h0 : 0 ∈ U f := by simpa [ev] using mem_of_mem_nhds (hU f)
    simpa [map_smul, hzero f hf] using h0
  have hlt : q (c • x) < 1 := hwq (hUw hmem)
  rw [hscale c hcpos x, inv_mul_cancel₀ hp.ne'] at hlt
  exact lt_irrefl _ hlt

/-- The predual consists of finitely supported real sequences. -/
abbrev E := ℕ →₀ ℝ

def embed : E →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 1 where
  toFun x := ⟨fun i => x i, memℓp_gen_iff (by norm_num) |>.2 (by
    simpa using (summable_of_ne_finset_zero (s := x.support)
      (f := fun i => ‖x i‖) (fun i hi => by simp [Finsupp.notMem_support_iff.mp hi])))⟩
  map_add' _ _ := lp.ext rfl
  map_smul' _ _ := lp.ext rfl

scoped instance : NormedAddCommGroup E := NormedAddCommGroup.induced _ _ embed
  (fun _ _ h => Finsupp.ext (fun i => congrArg (fun v : lp (fun _ : ℕ => ℝ) 1 => v i) h))

scoped instance : NormedSpace ℝ E := NormedSpace.induced _ _ _ embed

lemma norm_eq (x : E) : ‖x‖ = ∑ i ∈ x.support, ‖x i‖ := by
  change ‖embed x‖ = _
  rw [lp.norm_eq_tsum_rpow (by norm_num)]
  simp only [ENNReal.toReal_one, Real.rpow_one, one_div, inv_one]
  apply tsum_eq_sum
  intro i hi
  change ‖x i‖ = 0
  simp [Finsupp.notMem_support_iff.mp hi]

def e (i : ℕ) : E := Finsupp.single i 1

@[simp] lemma norm_e (i : ℕ) : ‖e i‖ = 1 := by
  simp [norm_eq, e]

def pairing (a : ℕ → ℝ) (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) : E →L[ℝ] ℝ :=
  (Finsupp.linearCombination ℝ a).mkContinuous C (by
    intro x
    rw [Finsupp.linearCombination_apply, Finsupp.sum, norm_eq, Finset.mul_sum]
    refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => ?_))
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (ha i) (norm_nonneg _))

lemma pairing_apply (a : ℕ → ℝ) (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) (x : E) :
    pairing a C ha x = ∑ i ∈ x.support, x i * a i := rfl

@[simp] lemma pairing_e (a : ℕ → ℝ) (C : ℝ) (ha : ∀ i, ‖a i‖ ≤ C) (i : ℕ) :
    pairing a C ha (e i) = a i := by
  simp [pairing_apply, e]

abbrev V := E →L[ℝ] ℝ

lemma coeff_bound (φ : V) (i : ℕ) : ‖φ (e i)‖ ≤ ‖φ‖ := by
  simpa using φ.le_opNorm (e i)

def modulus (φ : V) : V :=
  pairing (fun i => |φ (e i)|) ‖φ‖ (fun i => by simpa [Real.norm_eq_abs] using coeff_bound φ i)

@[simp] lemma modulus_e (φ : V) (i : ℕ) : modulus φ (e i) = |φ (e i)| := by
  simp [modulus]

lemma modulus_apply (φ : V) (x : E) :
    modulus φ x = ∑ i ∈ x.support, x i * |φ (e i)| := rfl

lemma modulus_norm_continuous : Continuous modulus := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro φ ψ
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [sub_apply, modulus_apply, modulus_apply, ← Finset.sum_sub_distrib,
    norm_eq, Finset.mul_sum]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [← mul_sub, norm_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc ‖|φ (e i)| - |ψ (e i)|‖ ≤ ‖φ (e i) - ψ (e i)‖ := abs_abs_sub_abs_le _ _
       _ ≤ ‖φ - ψ‖ := coeff_bound (φ - ψ) i

abbrev starTopology : TopologicalSpace V :=
  TopologicalSpace.induced (fun φ : V => fun x : E => φ x) inferInstance

lemma modulus_star_continuous : @Continuous _ _ starTopology starTopology modulus := by
  let _ := starTopology
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  change Continuous (fun φ => modulus φ x)
  simp_rw [modulus_apply]
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (((continuous_apply (e i)).comp continuous_induced_dom).abs)

def weight (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i

lemma weight_pos (i : ℕ) : 0 < weight i := by unfold weight; positivity

lemma series_bound (φ : V) (i : ℕ) : ‖weight i * φ (e i)‖ ≤ weight i * ‖φ‖ := by
  rw [norm_mul, Real.norm_of_nonneg (weight_pos i).le]
  exact mul_le_mul_of_nonneg_left (coeff_bound φ i) (weight_pos i).le

lemma weights_summable : Summable weight := summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma series_summable (φ : V) : Summable (fun i => weight i * φ (e i)) :=
  (weights_summable.mul_right ‖φ‖).of_norm_bounded (series_bound φ)

lemma series_norm_summable (φ : V) : Summable (fun i => ‖weight i * φ (e i)‖) :=
  (weights_summable.mul_right ‖φ‖).of_nonneg_of_le (fun _ => norm_nonneg _) (series_bound φ)

/-- A bidual functional with a strictly positive weight on every coordinate. -/
def mean : V →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun φ : V => ∑' i, weight i * φ (e i)
      map_add' := by
        intro φ ψ
        simp only [add_apply, mul_add]
        exact (series_summable φ).tsum_add (series_summable ψ)
      map_smul' := by
        intro c φ
        simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (weight _) c]
        exact tsum_mul_left } (∑' i, weight i) (by
      intro φ
      refine (norm_tsum_le_tsum_norm ?_).trans ?_
      · exact series_norm_summable φ
      · rw [← tsum_mul_right]
        exact Summable.tsum_le_tsum (series_bound φ) (series_norm_summable φ)
          (weights_summable.mul_right ‖φ‖))

lemma mean_apply (φ : V) : mean φ = ∑' i, weight i * φ (e i) := rfl

lemma ext_e {φ ψ : V} (h : ∀ i, φ (e i) = ψ (e i)) : φ = ψ := by
  have hh : φ.toLinearMap = ψ.toLinearMap := Finsupp.basisSingleOne.ext h
  exact DFunLike.ext _ _ (LinearMap.congr_fun hh)

lemma gauge_zero : mean (modulus 0) = 0 := by simp [mean_apply]

lemma gauge_pos (φ : V) (hφ : φ ≠ 0) : 0 < mean (modulus φ) := by
  obtain ⟨i, hi⟩ : ∃ i, φ (e i) ≠ 0 := by
    by_contra! hall
    exact hφ (ext_e (by simpa using hall))
  exact (series_summable (modulus φ)).tsum_pos
    (fun j => by simpa using mul_nonneg (weight_pos j).le (abs_nonneg (φ (e j)))) i
    (by simpa using mul_pos (weight_pos i) (abs_pos.mpr hi))

lemma gauge_scale (c : ℝ) (hc : 0 < c) (φ : V) :
    mean (modulus (c • φ)) = c * mean (modulus φ) := by
  have h : modulus (c • φ) = c • modulus φ := by
    apply ext_e
    intro i
    simp [abs_mul, abs_of_pos hc]
  rw [h, map_smul, smul_eq_mul]

def finiteEval (x : E) : V :=
  pairing (fun i => x i) ‖x‖ (lp.norm_apply_le_norm (by norm_num) (embed x))

@[simp] lemma finiteEval_e (x : E) (i : ℕ) : finiteEval x (e i) = x i :=
  pairing_e _ _ _ _

def intoDual : E →ₗ[ℝ] V where
  toFun := finiteEval
  map_add' x y := ext_e fun i => by simp
  map_smul' c x := ext_e fun i => by simp

lemma intoDual_injective : Function.Injective intoDual := by
  intro x y h
  ext i
  simpa [intoDual] using congrArg (fun φ : V => φ (e i)) h

/-- Otherwise the weak coordinates would embed all finitely supported sequences
into a finite-dimensional space. -/
lemma common_kernel (s : Finset (V →L[ℝ] ℝ)) :
    ∃ x : V, x ≠ 0 ∧ ∀ f ∈ s, f x = 0 := by
  classical
  let T : V →ₗ[ℝ] (s → ℝ) := LinearMap.pi (fun f : s => f.1.toLinearMap)
  by_contra! hall
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    by_contra! hne
    obtain ⟨f, hf, hfx⟩ := hall x hne
    exact hfx (congrFun (LinearMap.mem_ker.mp hx) ⟨f, hf⟩)
  have := Module.Finite.of_injective (T.comp intoDual) (hinj.comp intoDual_injective)
  have : Finite ℕ := (Finsupp.basisSingleOne (ι := ℕ) (R := ℝ)).linearIndependent.finite
  exact not_finite ℕ

end Mo10356Proof

open Mo10356Proof OMA.S_mo_10356

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_10356.main) := by
  intro hall
  have hweak := hall E modulus modulus_norm_continuous modulus_star_continuous
  apply no_weak_gauge (fun φ => mean (modulus φ)) gauge_zero gauge_pos gauge_scale common_kernel
  let J (φ : V) (f : V →L[ℝ] ℝ) := f φ
  have hJ : @Continuous V _ (weak E) _ J := continuous_induced_dom
  have hm := @Continuous.comp V _ ℝ (weak E) _ _ J _ (continuous_apply mean) hJ
  exact @Continuous.comp V V ℝ (weak E) (weak E) _ modulus _ hm hweak
