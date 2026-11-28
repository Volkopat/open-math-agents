import OMAReductions.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Proof of Step `LonelyRunnerConjecture.lonely_runner_conjecture.R1.H1`:
Real-to-integer velocity reduction for the Lonely Runner Conjecture
(Bienia-Goddyn-Gvozdjak-Sebo-Tarsi 1998; Bohman-Holzman-Kleitman 2001).
Credit: @paynebrowning
-/

noncomputable section

open scoped ComplexConjugate
open Set Submodule MeasureTheory UnitAddTorus

private lemma exists_finset_of_mem_span_mFourier {d : ℕ}
    {P : C(UnitAddTorus (Fin d), ℂ)}
    (hP : P ∈ span ℂ (range (mFourier (d := Fin d)))) :
    ∃ (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ∈ F ∧ ∀ x : UnitAddTorus (Fin d), P x = ∑ n ∈ F, c n * mFourier n x := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hP
  · rintro _ ⟨n₀, rfl⟩
    refine ⟨insert 0 {n₀}, fun n => if n = n₀ then 1 else 0, Finset.mem_insert_self 0 {n₀}, fun x => ?_⟩
    rcases eq_or_ne n₀ 0 with rfl | hn0
    · simp
    · rw [Finset.sum_insert (Finset.notMem_singleton.mpr hn0.symm), Finset.sum_singleton]
      simp [hn0.symm]
  · refine ⟨{0}, fun _ => 0, Finset.mem_singleton_self 0, fun x => ?_⟩
    simp
  · rintro P₁ P₂ _ _ ⟨F₁, c₁, h0₁, h₁⟩ ⟨F₂, c₂, _, h₂⟩
    refine ⟨F₁ ∪ F₂, fun n => (if n ∈ F₁ then c₁ n else 0) + (if n ∈ F₂ then c₂ n else 0),
      Finset.mem_union_left F₂ h0₁, fun x => ?_⟩
    change P₁ x + P₂ x = _
    rw [h₁ x, h₂ x]
    simp_rw [add_mul, Finset.sum_add_distrib]
    congr 1
    · have heq1 : (∑ n ∈ F₁, c₁ n * mFourier n x) =
          ∑ n ∈ F₁, (if n ∈ F₁ then c₁ n else 0) * mFourier n x := by
        refine Finset.sum_congr rfl fun n hn => by simp [hn]
      rw [heq1]
      exact Finset.sum_subset (Finset.subset_union_left : F₁ ⊆ F₁ ∪ F₂) fun n _ hn1 => by simp [hn1]
    · have heq2 : (∑ n ∈ F₂, c₂ n * mFourier n x) =
          ∑ n ∈ F₂, (if n ∈ F₂ then c₂ n else 0) * mFourier n x := by
        refine Finset.sum_congr rfl fun n hn => by simp [hn]
      rw [heq2]
      exact Finset.sum_subset (Finset.subset_union_right : F₂ ⊆ F₁ ∪ F₂) fun n _ hn2 => by simp [hn2]
  · rintro a P₁ _ ⟨F₁, c₁, h0₁, h₁⟩
    refine ⟨F₁, fun n => a * c₁ n, h0₁, fun x => ?_⟩
    change a * P₁ x = _
    rw [h₁ x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => by ring

private lemma exists_mFourier_approx {d : ℕ} (fC : C(UnitAddTorus (Fin d), ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : C(UnitAddTorus (Fin d), ℂ)) (F : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
      0 ∈ F ∧ ‖P - fC‖ < δ ∧
      ∀ x : UnitAddTorus (Fin d), P x = ∑ n ∈ F, c n * mFourier n x := by
  have h_top : (span ℂ (range (mFourier (d := Fin d)))).topologicalClosure = ⊤ :=
    UnitAddTorus.span_mFourier_closure_eq_top
  have hfC_mem : fC ∈ (span ℂ (range (mFourier (d := Fin d)))).topologicalClosure := by
    rw [h_top]; trivial
  have hfC_cl : (fC : C(UnitAddTorus (Fin d), ℂ)) ∈
      closure ((span ℂ (range (mFourier (d := Fin d)))) : Set C(UnitAddTorus (Fin d), ℂ)) := by
    rwa [← Submodule.topologicalClosure_coe]
  rw [Metric.mem_closure_iff] at hfC_cl
  obtain ⟨P, hP_mem, hP_dist⟩ := hfC_cl δ hδ
  have hP_norm : ‖P - fC‖ < δ := by rwa [dist_comm, dist_eq_norm] at hP_dist
  obtain ⟨F, c, h0F, hP_eval⟩ := exists_finset_of_mem_span_mFourier hP_mem
  exact ⟨P, F, c, h0F, hP_norm, hP_eval⟩

private lemma mFourier_eval_add {d : ℕ} (n : Fin d → ℤ) (x y : UnitAddTorus (Fin d)) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

private lemma mFourier_eval_nsmul {d : ℕ} (n : Fin d → ℤ) (m : ℕ) (x : UnitAddTorus (Fin d)) :
    mFourier n (m • x) = (mFourier n x) ^ m := by
  induction m with
  | zero =>
    simp [mFourier]
  | succ m ih =>
    rw [succ_nsmul, mFourier_eval_add, ih, pow_succ]

private lemma mFourier_ray_ne_one {d : ℕ} (e : Fin d → ℝ) (n : Fin d → ℤ)
    (tau : ℝ) (hpos : 0 < |tau * ∑ j : Fin d, (n j : ℝ) * e j|)
    (hlt : |tau * ∑ j : Fin d, (n j : ℝ) * e j| < 1 / 2) :
    mFourier n (fun j : Fin d => ((tau * e j : ℝ) : UnitAddCircle)) ≠ 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  set u : ℝ := tau * ∑ j : Fin d, (n j : ℝ) * e j
  have hsum : (∑ j : Fin d, 2 * ↑Real.pi * Complex.I * ↑(n j) * ↑(tau * e j)) =
      ↑u * (2 * ↑Real.pi * Complex.I) := by
    simp only [u, Complex.ofReal_mul, Complex.ofReal_sum, Complex.ofReal_intCast]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsum]
  intro heq
  rw [Complex.exp_eq_one_iff] at heq
  obtain ⟨m, hm⟩ := heq
  have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hu_eq : (u : ℂ) = (m : ℂ) := mul_right_cancel₀ hpi hm
  have hu_real : u = (m : ℝ) := by exact_mod_cast hu_eq
  rw [hu_real] at hpos hlt
  rcases eq_or_ne m 0 with rfl | hm0
  · simp at hpos
  · have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      exact_mod_cast Int.one_le_abs hm0
    linarith

section HaarTorus

private lemma integral_mFourier_eq_zero {d : ℕ} {n : Fin d → ℤ} (hn : n ≠ 0) :
    (∫ x : UnitAddTorus (Fin d), mFourier n x) = 0 := by
  have hj : ∃ j : Fin d, n j ≠ 0 := by
    by_contra h
    exact hn (funext fun j => Decidable.byContradiction fun hnj => h ⟨j, hnj⟩)
  obtain ⟨j₀, hj₀⟩ := hj
  let a : UnitAddCircle := ↑((1 : ℝ) / 2 / (n j₀ : ℝ))
  let δ : UnitAddTorus (Fin d) := Function.update 0 j₀ a
  have hshift : ∀ x : UnitAddTorus (Fin d), mFourier n (x + δ) = -mFourier n x := by
    intro x
    simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply]
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀),
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ j₀)]
    have hrest : ∏ i ∈ Finset.univ.erase j₀, fourier (n i) (x i + δ i) =
        ∏ i ∈ Finset.univ.erase j₀, fourier (n i) (x i) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      have hij : i ≠ j₀ := Finset.ne_of_mem_erase hi
      simp [δ, Function.update_of_ne hij]
    have hmain : fourier (n j₀) (x j₀ + δ j₀) = -fourier (n j₀) (x j₀) := by
      simp only [δ, Function.update_self, a]
      exact fourier_add_half_inv_index hj₀ zero_lt_one (x j₀)
    rw [hrest, hmain, mul_neg]
  have hint : (∫ x : UnitAddTorus (Fin d), mFourier n (x + δ)) =
      ∫ x : UnitAddTorus (Fin d), mFourier n x :=
    integral_add_right_eq_self (fun x => mFourier n x) δ
  simp_rw [hshift, integral_neg] at hint
  have h2 : (2 : ℂ) * (∫ x : UnitAddTorus (Fin d), mFourier n x) = 0 := by
    linear_combination -hint
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero

private lemma kronecker_pos {d : ℕ} (e : Fin d → ℝ) (he : LinearIndependent ℚ e)
    (θ : Fin d → UnitAddCircle) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ ∀ j : Fin d, dist ((t * e j : ℝ) : UnitAddCircle) (θ j) < ε := by
  by_contra h_no
  have h_far : ∀ t : ℝ, 0 ≤ t →
      ε ≤ dist (fun j : Fin d => ((t * e j : ℝ) : UnitAddCircle)) θ := by
    intro t ht
    by_contra hlt
    have hlt' := lt_of_not_ge hlt
    rw [dist_pi_lt_iff hε] at hlt'
    exact h_no ⟨t, ht, hlt'⟩
  let f_real : UnitAddTorus (Fin d) → ℝ := fun x => max 0 (ε - dist x θ)
  have hf_cont : Continuous f_real :=
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  have hf_int : Integrable f_real volume :=
    hf_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f_real)
  have hf_nonneg : 0 ≤ f_real := fun _ => le_max_left 0 _
  have hf_theta : f_real θ ≠ 0 := by
    simp only [f_real, dist_self, sub_zero, max_eq_right hε.le]
    exact ne_of_gt hε
  let I : ℝ := ∫ x : UnitAddTorus (Fin d), f_real x
  have hI : 0 < I :=
    integral_pos_of_integrable_nonneg_nonzero hf_cont hf_int hf_nonneg hf_theta
  let V : ℝ := (volume : Measure (UnitAddTorus (Fin d))).real univ
  have hV_pos : 0 < V := by
    dsimp [V, Measure.real]
    exact ENNReal.toReal_pos
      (IsOpen.measure_ne_zero volume isOpen_univ ⟨0, trivial⟩)
      (measure_ne_top volume univ)
  let δ : ℝ := I / (3 * V)
  have hδ_pos : 0 < δ := div_pos hI (by positivity)
  let fC : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (f_real x : ℂ), Complex.continuous_ofReal.comp hf_cont⟩
  obtain ⟨P, F, c, h0F, hP_norm, hP_eval⟩ := exists_mFourier_approx fC hδ_pos
  let S : Finset (Fin d → ℤ) := F.erase 0
  have hint_P : (∫ x : UnitAddTorus (Fin d), P x) = (V : ℂ) * c 0 := by
    have h_eq_fn : (fun x : UnitAddTorus (Fin d) => P x) =
        fun x => ∑ n ∈ F, c n * mFourier n x := funext hP_eval
    rw [h_eq_fn]
    rw [integral_finsetSum F (fun n _ => ((mFourier n).continuous.const_mul (c n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    rw [← Finset.add_sum_erase F _ h0F]
    have h0 : (∫ x : UnitAddTorus (Fin d), c 0 * mFourier 0 x) = (V : ℂ) * c 0 := by
      have hm0 : (fun x : UnitAddTorus (Fin d) => c 0 * mFourier 0 x) = fun _ => c 0 := by
        ext x; simp [mFourier_zero]
      rw [hm0, integral_const]
      simp [V, Complex.real_smul]
    have hS : ∑ n ∈ S, (∫ x : UnitAddTorus (Fin d), c n * mFourier n x) = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [integral_const_mul, integral_mFourier_eq_zero (Finset.ne_of_mem_erase hn), mul_zero]
    rw [h0, hS, add_zero]
  have hint_fC : (∫ x : UnitAddTorus (Fin d), fC x) = (I : ℂ) := integral_ofReal
  have hc0_diff : ‖(V : ℂ) * c 0 - (I : ℂ)‖ ≤ V * ‖P - fC‖ := by
    rw [← hint_P, ← hint_fC, ← integral_sub
      (P.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fC.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    calc ‖∫ x : UnitAddTorus (Fin d), (P x - fC x)‖
        ≤ ∫ x : UnitAddTorus (Fin d), ‖P x - fC x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : UnitAddTorus (Fin d), ‖P - fC‖ := by
          refine integral_mono
            (((P - fC).continuous.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            (integrable_const _) (fun x => ContinuousMap.norm_coe_le_norm (P - fC) x)
      _ = V * ‖P - fC‖ := by
          rw [integral_const, smul_eq_mul]
  have hc0_gt : 2 * δ < ‖c 0‖ := by
    have hI_norm : ‖(I : ℂ)‖ = I := Complex.norm_of_nonneg hI.le
    have hVc_norm : ‖(V : ℂ) * c 0‖ = V * ‖c 0‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hV_pos.le]
    have htri : ‖(I : ℂ)‖ - ‖(V : ℂ) * c 0‖ ≤ ‖(V : ℂ) * c 0 - (I : ℂ)‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le (I : ℂ) ((V : ℂ) * c 0)
    have hVP : V * ‖P - fC‖ < I / 3 := by
      have := mul_lt_mul_of_pos_left hP_norm hV_pos
      have hVδ : V * δ = I / 3 := by dsimp [δ]; field_simp [ne_of_gt hV_pos]
      linarith
    have hVc_gt : 2 * I / 3 < V * ‖c 0‖ := by linarith
    have h2δ : 2 * δ = (2 * I / 3) / V := by dsimp [δ]; ring
    rw [h2δ, div_lt_iff₀ hV_pos]
    linarith
  let ω : (Fin d → ℤ) → ℝ := fun n => ∑ j : Fin d, (n j : ℝ) * e j
  have hω_pos : ∀ n ∈ S, 0 < |ω n| := by
    intro n hn
    have hn_ne : n ≠ 0 := Finset.ne_of_mem_erase hn
    rw [abs_pos]
    intro h0
    have hlin : ∑ j : Fin d, (n j : ℚ) • e j = 0 := by
      simpa [ω, Rat.smul_def] using h0
    have hall := Fintype.linearIndependent_iff.mp he (fun j => (n j : ℚ)) hlin
    apply hn_ne
    ext j
    exact_mod_cast hall j
  let Mω : ℝ := (∑ n ∈ S, |ω n|) + 1
  have hMω_pos : 0 < Mω := by
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun _ _ => abs_nonneg _) zero_lt_one
  let tau : ℝ := 1 / (2 * Mω)
  have htau_pos : 0 < tau := by positivity
  let γ₁ : UnitAddTorus (Fin d) := fun j => ((tau * e j : ℝ) : UnitAddCircle)
  let z : (Fin d → ℤ) → ℂ := fun n => mFourier n γ₁
  have hz_ne : ∀ n ∈ S, z n ≠ 1 := by
    intro n hn
    apply mFourier_ray_ne_one e n tau
    · rw [abs_mul, abs_of_pos htau_pos]
      exact mul_pos htau_pos (hω_pos n hn)
    · rw [abs_mul, abs_of_pos htau_pos]
      have hle : |ω n| ≤ ∑ m ∈ S, |ω m| :=
        Finset.single_le_sum (f := fun m : Fin d → ℤ => |ω m|) (fun _ _ => abs_nonneg _) hn
      have hltM : |ω n| < Mω := by dsimp [Mω]; linarith
      dsimp [tau]
      rw [one_div_mul_eq_div, div_lt_div_iff₀ (by positivity) (by positivity)]
      linarith
  have hz_norm : ∀ n : Fin d → ℤ, ‖z n‖ = 1 := by
    intro n
    simp only [z, mFourier, ContinuousMap.coe_mk, fourier_apply, norm_prod, Circle.norm_coe,
      Finset.prod_const_one]
  let B : ℝ := ∑ n ∈ S, ‖c n‖ * (2 / ‖z n - 1‖)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (B / δ)
  let N : ℕ := N₀ + 1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hBN : B / (N : ℝ) < δ := by
    rw [div_lt_iff₀ hN_pos]
    have hlt' := (div_lt_iff₀ hδ_pos).mp hN₀
    have hN_ge : (N₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.le_succ N₀
    nlinarith
  let A : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) * ∑ m ∈ Finset.range N, P (m • γ₁)
  have hγ_eq : ∀ m : ℕ, (m • γ₁ : UnitAddTorus (Fin d)) =
      fun j => ((((m : ℝ) * tau) * e j : ℝ) : UnitAddCircle) := by
    intro m
    ext j
    simp only [Pi.smul_apply, γ₁, mul_assoc, ← QuotientAddGroup.mk_nsmul, nsmul_eq_mul]
  have hA_lt : ‖A‖ < δ := by
    dsimp [A]
    rw [norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    calc (1 / (N : ℝ)) * ‖∑ m ∈ Finset.range N, P (m • γ₁)‖
        ≤ (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, ‖P (m • γ₁)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ ≤ (1 / (N : ℝ)) * ∑ _ ∈ Finset.range N, ‖P - fC‖ := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => ?_) (by positivity)
          have hf0 : fC (m • γ₁) = 0 := by
            simp only [fC, ContinuousMap.coe_mk, Complex.ofReal_eq_zero, f_real, max_eq_left_iff,
              sub_nonpos, hγ_eq m]
            exact h_far ((m : ℝ) * tau) (by positivity)
          have hsub : P (m • γ₁) = (P - fC) (m • γ₁) := by simp [hf0]
          rw [hsub]
          exact ContinuousMap.norm_coe_le_norm (P - fC) (m • γ₁)
      _ = ‖P - fC‖ := by
          simp [Finset.sum_const, Finset.card_range, ne_of_gt hN_pos]
      _ < δ := hP_norm
  have hA_decomp : A - c 0 = ((1 / (N : ℝ) : ℝ) : ℂ) *
      ∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m := by
    dsimp [A]
    have hsum1 : (∑ m ∈ Finset.range N, P (m • γ₁)) =
        (N : ℂ) * c 0 + ∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m := by
      simp_rw [hP_eval]
      rw [Finset.sum_comm]
      rw [← Finset.add_sum_erase _ _ h0F]
      congr 1
      · simp [mFourier_zero, Finset.sum_const, Finset.card_range]
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        exact mFourier_eval_nsmul n m γ₁
    rw [hsum1, mul_add]
    have hN_inv : ((1 / (N : ℝ) : ℝ) : ℂ) * (N : ℂ) = 1 := by
      exact_mod_cast one_div_mul_cancel (ne_of_gt hN_pos)
    linear_combination c 0 * hN_inv
  have hA_tail : ‖A - c 0‖ ≤ B / (N : ℝ) := by
    rw [hA_decomp, norm_mul, Complex.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)),
      one_div_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ hN_pos.le
    calc ‖∑ n ∈ S, c n * ∑ m ∈ Finset.range N, (z n) ^ m‖
        ≤ ∑ n ∈ S, ‖c n * ∑ m ∈ Finset.range N, (z n) ^ m‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ‖c n‖ * (2 / ‖z n - 1‖) := by
          refine Finset.sum_le_sum fun n hn => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [geom_sum_eq (hz_ne n hn), norm_div]
          refine div_le_div_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖(z n) ^ N - 1‖ ≤ ‖(z n) ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, hz_norm n, one_pow, norm_one]; norm_num
  have hA_ge : ‖c 0‖ - ‖A‖ ≤ ‖A - c 0‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le (c 0) A
  linarith

end HaarTorus

private lemma exists_rat_li_span : ∀ (m : ℕ) (u : Fin m → ℝ),
    ∃ (d : ℕ) (b : Fin d → ℝ) (q : Fin m → Fin d → ℚ),
      LinearIndependent ℚ b ∧ ∀ i : Fin m, u i = ∑ j : Fin d, (q i j : ℝ) * b j
  | 0, u =>
    ⟨0, Fin.elim0, fun i => Fin.elim0 i, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | m + 1, u => by
    obtain ⟨d, b, q, hb_li, hq⟩ := exists_rat_li_span m (Fin.init u)
    by_cases h_mem : ∃ r : Fin d → ℚ, u (Fin.last m) = ∑ j : Fin d, (r j : ℝ) * b j
    · obtain ⟨r, hr⟩ := h_mem
      refine ⟨d, b, Fin.snoc q r, hb_li, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · simpa [Fin.snoc_last] using hr
      · simpa [Fin.snoc_castSucc, Fin.init] using hq i₀
    · let b' : Fin (d + 1) → ℝ := Fin.snoc b (u (Fin.last m))
      have hb'_li : LinearIndependent ℚ b' := by
        rw [Fintype.linearIndependent_iff]
        intro g hg
        rw [Fin.sum_univ_castSucc] at hg
        simp only [b', Fin.snoc_castSucc, Fin.snoc_last] at hg
        have hlast : g (Fin.last d) = 0 := by
          by_contra hne
          apply h_mem
          refine ⟨fun j => -g j.castSucc / g (Fin.last d), ?_⟩
          have hne_r : (g (Fin.last d) : ℝ) ≠ 0 := by exact_mod_cast hne
          have hsum_r : (∑ j : Fin d, (g j.castSucc : ℝ) * b j) +
              (g (Fin.last d) : ℝ) * u (Fin.last m) = 0 := by
            simpa [Rat.smul_def] using hg
          have hu_eq : u (Fin.last m) = -(∑ j : Fin d, (g j.castSucc : ℝ) * b j) / (g (Fin.last d) : ℝ) := by
            field_simp [hne_r]
            linarith
          rw [hu_eq, neg_div, Finset.sum_div]
          simp only [← Finset.sum_neg_distrib, Rat.cast_div, Rat.cast_neg]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
        have hg_init : ∑ j : Fin d, g j.castSucc • b j = 0 := by
          rw [hlast, zero_smul, add_zero] at hg
          exact hg
        have hinit := Fintype.linearIndependent_iff.mp hb_li (fun j => g j.castSucc) hg_init
        intro j
        refine Fin.lastCases hlast hinit j
      let q' : Fin (m + 1) → Fin (d + 1) → ℚ :=
        Fin.snoc (fun i₀ => Fin.snoc (q i₀) 0) (Fin.snoc (fun _ => 0) 1)
      refine ⟨d + 1, b', q', hb'_li, fun i => ?_⟩
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · rw [Fin.sum_univ_castSucc]
        simp [q', b', Fin.snoc_last, Fin.snoc_castSucc]
      · rw [Fin.sum_univ_castSucc]
        simpa [q', b', Fin.snoc_last, Fin.snoc_castSucc, Fin.init] using hq i₀

private lemma exists_int_coords_over_rat_li {k : ℕ} (v : Fin k → ℝ) :
    ∃ (d : ℕ) (e : Fin d → ℝ) (c : Fin k → Fin d → ℤ),
      LinearIndependent ℚ e ∧ ∀ i : Fin k, v i = ∑ j : Fin d, (c i j : ℝ) * e j := by
  obtain ⟨d, b, q, hb_li, hq⟩ := exists_rat_li_span k v
  let D : ℕ := ∏ i : Fin k, ∏ j : Fin d, (q i j).den
  have hD_pos : 0 < D :=
    Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => (q i j).pos
  have hD_ne_q : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
  have hD_ne_r : (D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hD_pos)
  let e : Fin d → ℝ := fun j => b j / (D : ℝ)
  have he_li : LinearIndependent ℚ e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : ∑ j : Fin d, (g j / (D : ℚ)) • b j = 0 := by
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [e, Rat.smul_def, Rat.cast_div, Rat.cast_natCast]
      ring
    have hall := Fintype.linearIndependent_iff.mp hb_li (fun j => g j / (D : ℚ)) hg'
    intro j
    exact (div_eq_zero_iff.mp (hall j)).resolve_right hD_ne_q
  let q_div : Fin k → Fin d → ℕ := fun i j => D / (q i j).den
  let c : Fin k → Fin d → ℤ := fun i j => (q i j).num * (q_div i j : ℤ)
  have hc_eq : ∀ (i : Fin k) (j : Fin d), (c i j : ℚ) = (D : ℚ) * q i j := by
    intro i j
    have hdvd1 : (q i j).den ∣ ∏ j' : Fin d, (q i j').den :=
      Finset.dvd_prod_of_mem (fun j' : Fin d => (q i j').den) (Finset.mem_univ j)
    have hdvd2 : (∏ j' : Fin d, (q i j').den) ∣ D :=
      Finset.dvd_prod_of_mem (fun i' : Fin k => ∏ j' : Fin d, (q i' j').den) (Finset.mem_univ i)
    have hdvd : (q i j).den ∣ D := dvd_trans hdvd1 hdvd2
    have hmul : (q_div i j : ℚ) * ((q i j).den : ℚ) = (D : ℚ) := by
      dsimp [q_div]
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((q i j).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (q i j).pos)
    apply mul_right_cancel₀ hden_ne
    have hnum : q i j * ((q i j).den : ℚ) = ((q i j).num : ℚ) := Rat.mul_den_eq_num (q i j)
    calc (c i j : ℚ) * ((q i j).den : ℚ)
        = ((q i j).num : ℚ) * ((q_div i j : ℚ) * ((q i j).den : ℚ)) := by
          dsimp only [c]; rw [Int.cast_mul, Int.cast_natCast, mul_assoc]
      _ = ((q i j).num : ℚ) * (D : ℚ) := by rw [hmul]
      _ = (D : ℚ) * (q i j * ((q i j).den : ℚ)) := by rw [hnum, mul_comm]
      _ = ((D : ℚ) * q i j) * ((q i j).den : ℚ) := by ring
  refine ⟨d, e, c, he_li, fun i => ?_⟩
  rw [hq i]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcj_r : (c i j : ℝ) = (D : ℝ) * (q i j : ℝ) := by exact_mod_cast hc_eq i j
  rw [hcj_r]
  dsimp [e]
  field_simp [hD_ne_r]

private lemma unitAddCircle_dist_neg_zero (x : ℝ) :
    dist ((-x : ℝ) : UnitAddCircle) 0 = dist (x : UnitAddCircle) 0 := by
  rw [dist_zero_right, dist_zero_right, QuotientAddGroup.mk_neg, norm_neg]

private lemma unitAddCircle_dist_abs_mul (t x : ℝ) :
    dist ((t * |x| : ℝ) : UnitAddCircle) 0 = dist ((t * x : ℝ) : UnitAddCircle) 0 := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, mul_neg, unitAddCircle_dist_neg_zero]

private lemma dist_zsmul_unitAddCircle_le (n : ℤ) (x y : UnitAddCircle) :
    dist (n • x) (n • y) ≤ |(n : ℝ)| * dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← zsmul_sub]
  have hnat : ∀ (m : ℕ) (z : UnitAddCircle), ‖m • z‖ ≤ (m : ℝ) * ‖z‖ := fun _ _ => norm_nsmul_le
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simpa [abs_of_nonneg hm0] using hnat m (x - y)
  · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [neg_zsmul, norm_neg, Int.cast_neg, Int.cast_natCast, abs_neg, abs_of_nonneg hm0]
    exact hnat m (x - y)

private lemma dist_sum_zsmul_le {d : ℕ} (c : Fin d → ℤ) (x y : Fin d → UnitAddCircle) :
    dist (∑ j : Fin d, c j • x j) (∑ j : Fin d, c j • y j) ≤
      ∑ j : Fin d, |(c j : ℝ)| * dist (x j) (y j) := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc ‖∑ j : Fin d, (c j • x j - c j • y j)‖
      ≤ ∑ j : Fin d, ‖c j • x j - c j • y j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin d, |(c j : ℝ)| * dist (x j) (y j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← dist_eq_norm]
        exact dist_zsmul_unitAddCircle_le (c j) (x j) (y j)

private lemma mk_sum_int_mul {d : ℕ} (c : Fin d → ℤ) (x : Fin d → ℝ) :
    ((∑ j : Fin d, (c j : ℝ) * x j : ℝ) : UnitAddCircle) =
      ∑ j : Fin d, c j • ((x j : ℝ) : UnitAddCircle) := by
  rw [QuotientAddGroup.mk_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← QuotientAddGroup.mk_zsmul, zsmul_eq_mul]

private lemma clear_pos_rat_denoms {m : ℕ} (r : Fin m → ℚ) (hr_pos : ∀ i : Fin m, 0 < r i) :
    ∃ (M : ℕ) (a : Fin m → ℕ), 0 < M ∧ (∀ i : Fin m, 0 < a i) ∧
      ∀ i : Fin m, (a i : ℚ) = (M : ℚ) * r i := by
  let M : ℕ := ∏ i : Fin m, (r i).den
  have hM_pos : 0 < M := Finset.prod_pos fun i _ => (r i).pos
  let m_div : Fin m → ℕ := fun i => M / (r i).den
  let z : Fin m → ℤ := fun i => (r i).num * (m_div i : ℤ)
  have hz_eq : ∀ i : Fin m, (z i : ℚ) = (M : ℚ) * r i := by
    intro i
    have hdvd : (r i).den ∣ M :=
      Finset.dvd_prod_of_mem (fun i' : Fin m => (r i').den) (Finset.mem_univ i)
    have hmul : (m_div i : ℚ) * ((r i).den : ℚ) = (M : ℚ) := by
      dsimp [m_div]
      exact_mod_cast Nat.div_mul_cancel hdvd
    have hden_ne : ((r i).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt (r i).pos)
    apply mul_right_cancel₀ hden_ne
    have hnum : r i * ((r i).den : ℚ) = ((r i).num : ℚ) := Rat.mul_den_eq_num (r i)
    calc (z i : ℚ) * ((r i).den : ℚ)
        = ((r i).num : ℚ) * ((m_div i : ℚ) * ((r i).den : ℚ)) := by
          dsimp only [z]; rw [Int.cast_mul, Int.cast_natCast, mul_assoc]
      _ = ((r i).num : ℚ) * (M : ℚ) := by rw [hmul]
      _ = (M : ℚ) * (r i * ((r i).den : ℚ)) := by rw [hnum, mul_comm]
      _ = ((M : ℚ) * r i) * ((r i).den : ℚ) := by ring
  have hz_pos : ∀ i : Fin m, 0 < z i := by
    intro i
    have hpos_q : (0 : ℚ) < (z i : ℚ) := by
      rw [hz_eq i]
      exact mul_pos (Nat.cast_pos.mpr hM_pos) (hr_pos i)
    exact Int.cast_pos.mp hpos_q
  refine ⟨M, fun i => (z i).toNat, hM_pos, fun i => ?_, fun i => ?_⟩
  · exact Int.pos_iff_toNat_pos.mp (hz_pos i)
  · have htonat : ((z i).toNat : ℤ) = z i := Int.toNat_of_nonneg (hz_pos i).le
    calc (((z i).toNat : ℕ) : ℚ) = ((z i : ℤ) : ℚ) := by exact_mod_cast htonat
      _ = (M : ℚ) * r i := hz_eq i

private theorem real_to_nat_lrc (k : ℕ) (hk : 2 ≤ k) (v : Fin k → ℝ)
    (hv_pos : ∀ i : Fin k, 0 < v i) (hv_mono : StrictMono v)
    (h_int : ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (w : Fin m → ℕ),
      (∀ i : Fin m, 0 < w i) → StrictMono w →
      ∃ t : ℝ, t ≥ 0 ∧
        ∀ i : Fin m, dist ((t * (w i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / ((m + 1 : ℕ) : ℝ)) :
    ∃ t : ℝ, t ≥ 0 ∧
      ∀ i : Fin k, dist ((t * v i : ℝ) : UnitAddCircle) 0 ≥ 1 / ((k + 1 : ℕ) : ℝ) := by
  let i₀ : Fin k := ⟨0, by omega⟩
  have hv0 : 0 < v i₀ := hv_pos i₀
  by_cases h_prop : ∀ i : Fin k, ∃ r : ℚ, v i = (r : ℝ) * v i₀
  · choose r hr using h_prop
    have hr_pos : ∀ i : Fin k, 0 < r i := by
      intro i
      have hpos_r : (0 : ℝ) < (r i : ℝ) := by
        have := hv_pos i
        rw [hr i] at this
        exact pos_of_mul_pos_left this hv0.le
      exact Rat.cast_pos.mp hpos_r
    obtain ⟨M, w, hM_pos, hw_pos, hw_eq⟩ := clear_pos_rat_denoms r hr_pos
    have hw_real : ∀ i : Fin k, (w i : ℝ) * v i₀ = (M : ℝ) * v i := by
      intro i
      have hw_r : (w i : ℝ) = (M : ℝ) * (r i : ℝ) := by exact_mod_cast hw_eq i
      rw [hw_r, hr i, mul_assoc]
    have hw_mono : StrictMono w := by
      intro i j hij
      have hlt_v : (M : ℝ) * v i < (M : ℝ) * v j :=
        mul_lt_mul_of_pos_left (hv_mono hij) (Nat.cast_pos.mpr hM_pos)
      rw [← hw_real i, ← hw_real j] at hlt_v
      have hlt_w : (w i : ℝ) < (w j : ℝ) := lt_of_mul_lt_mul_right hlt_v hv0.le
      exact Nat.cast_lt.mp hlt_w
    obtain ⟨t', ht'0, ht'⟩ := h_int k (by omega) le_rfl w hw_pos hw_mono
    refine ⟨t' * (M : ℝ) / v i₀, by positivity, fun i => ?_⟩
    have hmul : t' * (M : ℝ) / v i₀ * v i = t' * (w i : ℝ) := by
      have h1 : (M : ℝ) * v i = (w i : ℝ) * v i₀ := (hw_real i).symm
      calc t' * (M : ℝ) / v i₀ * v i = t' * ((M : ℝ) * v i) / v i₀ := by ring
        _ = t' * ((w i : ℝ) * v i₀) / v i₀ := by rw [h1]
        _ = t' * (w i : ℝ) := by field_simp [ne_of_gt hv0]
    rw [hmul]
    exact ht' i
  · obtain ⟨d, e, c, he_li, hve⟩ := exists_int_coords_over_rat_li v
    let Csum : ℝ := (∑ i : Fin k, ∑ j : Fin d, |(c i j : ℝ)|) + 1
    have hCsum_pos : 0 < Csum := by
      refine add_pos_of_nonneg_of_pos ?_ zero_lt_one
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * Csum / v i₀)
    let N : ℕ := N₀ + 1
    have hN_pos_r : (0 : ℝ) < (N : ℝ) := by positivity
    let r : Fin d → ℚ := fun j => (⌊(N : ℝ) * e j⌋ : ℚ) / (N : ℚ)
    have hr_approx : ∀ j : Fin d, |(r j : ℝ) - e j| ≤ 1 / (N : ℝ) := by
      intro j
      have hfl1 : (⌊(N : ℝ) * e j⌋ : ℝ) ≤ (N : ℝ) * e j := Int.floor_le _
      have hfl2 : (N : ℝ) * e j < (⌊(N : ℝ) * e j⌋ : ℝ) + 1 := Int.lt_floor_add_one _
      have hr_cast : (r j : ℝ) = (⌊(N : ℝ) * e j⌋ : ℝ) / (N : ℝ) := by
        dsimp [r]; push_cast; rfl
      have heq : (r j : ℝ) - e j = ((⌊(N : ℝ) * e j⌋ : ℝ) - (N : ℝ) * e j) / (N : ℝ) := by
        rw [hr_cast]; field_simp [ne_of_gt hN_pos_r]
      rw [heq, abs_div, abs_of_pos hN_pos_r]
      refine div_le_div_of_nonneg_right ?_ hN_pos_r.le
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    let rStar : Fin k → ℚ := fun i => ∑ j : Fin d, (c i j : ℚ) * r j
    have hrStar_pos : ∀ i : Fin k, 0 < rStar i := by
      intro i
      have hvi_ge : v i₀ ≤ v i := by
        rcases eq_or_lt_of_le (Nat.zero_le i.val) with h0 | hpos
        · have hi_eq : i = i₀ := Fin.ext h0.symm
          rw [hi_eq]
        · exact (hv_mono (by rw [Fin.lt_def]; exact hpos)).le
      have hdiff : |(rStar i : ℝ) - v i| ≤ Csum / (N : ℝ) := by
        have hcast : (rStar i : ℝ) - v i = ∑ j : Fin d, (c i j : ℝ) * ((r j : ℝ) - e j) := by
          rw [hve i]
          dsimp [rStar]
          push_cast
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => by ring
        rw [hcast]
        calc |∑ j : Fin d, (c i j : ℝ) * ((r j : ℝ) - e j)|
            ≤ ∑ j : Fin d, |(c i j : ℝ) * ((r j : ℝ) - e j)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j : Fin d, |(c i j : ℝ)| * |(r j : ℝ) - e j| := by
              refine Finset.sum_congr rfl fun j _ => abs_mul _ _
          _ ≤ ∑ j : Fin d, |(c i j : ℝ)| * (1 / (N : ℝ)) := by
              refine Finset.sum_le_sum fun j _ =>
                mul_le_mul_of_nonneg_left (hr_approx j) (abs_nonneg _)
          _ = (∑ j : Fin d, |(c i j : ℝ)|) / (N : ℝ) := by
              rw [← Finset.sum_mul, mul_one_div]
          _ ≤ Csum / (N : ℝ) := by
              refine div_le_div_of_nonneg_right ?_ hN_pos_r.le
              have hle_i : (∑ j : Fin d, |(c i j : ℝ)|) ≤ ∑ i' : Fin k, ∑ j : Fin d, |(c i' j : ℝ)| :=
                Finset.single_le_sum (f := fun i' : Fin k => ∑ j : Fin d, |(c i' j : ℝ)|)
                  (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
              dsimp [Csum]; linarith
      have hCN : Csum / (N : ℝ) < v i₀ / 2 := by
        rw [div_lt_div_iff₀ hN_pos_r zero_lt_two]
        have h1 := (div_lt_iff₀ hv0).mp hN₀
        have h2 : (N₀ : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_succ_self N₀
        nlinarith
      have hpos_r : (0 : ℝ) < (rStar i : ℝ) := by
        have := (abs_le.mp hdiff).1
        linarith
      exact Rat.cast_pos.mp hpos_r
    have hex_col : ∃ (j₀ : Fin d) (i : Fin k),
        (c i j₀ : ℚ) / rStar i ≠ (c i₀ j₀ : ℚ) / rStar i₀ := by
      by_contra h_all
      apply h_prop
      intro i
      refine ⟨rStar i / rStar i₀, ?_⟩
      have hr0_ne : (rStar i₀ : ℝ) ≠ 0 := ne_of_gt (Rat.cast_pos.mpr (hrStar_pos i₀))
      have h_col_eq : ∀ j : Fin d, (c i j : ℝ) * (rStar i₀ : ℝ) = (c i₀ j : ℝ) * (rStar i : ℝ) := by
        intro j
        have h_eq_q : (c i j : ℚ) / rStar i = (c i₀ j : ℚ) / rStar i₀ :=
          Decidable.byContradiction fun hne => h_all ⟨j, i, hne⟩
        have h_mul_q : (c i j : ℚ) * rStar i₀ = (c i₀ j : ℚ) * rStar i := by
          have hr_i_ne : rStar i ≠ 0 := ne_of_gt (hrStar_pos i)
          have hr_0_ne : rStar i₀ ≠ 0 := ne_of_gt (hrStar_pos i₀)
          exact (div_eq_div_iff hr_i_ne hr_0_ne).mp h_eq_q
        exact_mod_cast h_mul_q
      have hsum_eq : v i * (rStar i₀ : ℝ) = (rStar i : ℝ) * v i₀ := by
        rw [hve i, hve i₀, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        calc ((c i j : ℝ) * e j) * (rStar i₀ : ℝ)
            = ((c i j : ℝ) * (rStar i₀ : ℝ)) * e j := by ring
          _ = ((c i₀ j : ℝ) * (rStar i : ℝ)) * e j := by rw [h_col_eq j]
          _ = (rStar i : ℝ) * ((c i₀ j : ℝ) * e j) := by ring
      push_cast
      field_simp [hr0_ne]
      linarith
    obtain ⟨j₀, i_neq, hi_neq⟩ := hex_col
    let f : Fin k → ℚ := fun i => (c i j₀ : ℚ) / rStar i
    let Sf : Finset ℚ := Finset.univ.image f
    have hSf_ne : Sf.Nonempty := ⟨f i₀, Finset.mem_image_of_mem f (Finset.mem_univ i₀)⟩
    let q1 : ℚ := Sf.min' hSf_ne
    have hq1_mem : q1 ∈ Sf := Finset.min'_mem Sf hSf_ne
    obtain ⟨i₁, _, hi₁_eq⟩ := Finset.mem_image.mp hq1_mem
    have hex_gt : ∃ x ∈ Sf, q1 < x := by
      have hf0_mem : f i₀ ∈ Sf := Finset.mem_image_of_mem f (Finset.mem_univ i₀)
      have hfi_mem : f i_neq ∈ Sf := Finset.mem_image_of_mem f (Finset.mem_univ i_neq)
      have hle0 : q1 ≤ f i₀ := Finset.min'_le Sf (f i₀) hf0_mem
      have hlei : q1 ≤ f i_neq := Finset.min'_le Sf (f i_neq) hfi_mem
      rcases lt_or_eq_of_le hle0 with hlt0 | heq0
      · exact ⟨f i₀, hf0_mem, hlt0⟩
      · refine ⟨f i_neq, hfi_mem, lt_of_le_of_ne hlei ?_⟩
        intro heqi
        exact hi_neq (heqi.symm.trans heq0)
    let Sf_gt : Finset ℚ := Sf.filter (fun x => q1 < x)
    have hSf_gt_ne : Sf_gt.Nonempty := by
      obtain ⟨x, hx, hlt⟩ := hex_gt
      exact ⟨x, Finset.mem_filter.mpr ⟨hx, hlt⟩⟩
    let q2 : ℚ := Sf_gt.min' hSf_gt_ne
    have hq2_mem : q2 ∈ Sf_gt := Finset.min'_mem Sf_gt hSf_gt_ne
    obtain ⟨hq2_Sf, hq1_lt_q2⟩ := Finset.mem_filter.mp hq2_mem
    obtain ⟨i₂, _, hi₂_eq⟩ := Finset.mem_image.mp hq2_Sf
    have hi₁_ne_i₂ : i₁ ≠ i₂ := by
      intro heq
      rw [heq, hi₂_eq] at hi₁_eq
      exact (lt_irrefl q2) (hi₁_eq ▸ hq1_lt_q2)
    have hf_gap : ∀ i : Fin k, f i ≤ f i₁ ∨ f i₂ ≤ f i := by
      intro i
      rw [hi₁_eq, hi₂_eq]
      rcases le_or_gt (f i) q1 with hle | hgt
      · exact Or.inl hle
      · refine Or.inr (Finset.min'_le Sf_gt (f i) ?_)
        exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem f (Finset.mem_univ i), hgt⟩
    let η : Fin d → ℚ := fun j =>
      (if j = j₀ then rStar i₁ + rStar i₂ else 0) - ((c i₁ j₀ : ℚ) + (c i₂ j₀ : ℚ)) * r j
    let wStar : Fin k → ℚ := fun i => ∑ j : Fin d, (c i j : ℚ) * η j
    have hwStar_formula : ∀ i : Fin k,
        wStar i = (rStar i₁ + rStar i₂) * (c i j₀ : ℚ) -
          ((c i₁ j₀ : ℚ) + (c i₂ j₀ : ℚ)) * rStar i := by
      intro i
      dsimp [wStar, η, rStar]
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp [mul_comm]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
    have hwStar_collide : |wStar i₁| = |wStar i₂| := by
      have hsum0 : wStar i₁ + wStar i₂ = 0 := by
        rw [hwStar_formula i₁, hwStar_formula i₂]
        ring
      have hneg : wStar i₁ = -wStar i₂ := eq_neg_of_add_eq_zero_left hsum0
      rw [hneg, abs_neg]
    have hwStar_abs_pos : ∀ i : Fin k, 0 < |wStar i| := by
      intro i
      rw [abs_pos]
      intro hw0
      rw [hwStar_formula i] at hw0
      have hr1 := hrStar_pos i₁
      have hr2 := hrStar_pos i₂
      have hri := hrStar_pos i
      have hf12 : f i₁ < f i₂ := by rwa [hi₁_eq, hi₂_eq]
      have hlt12 : (c i₁ j₀ : ℚ) * rStar i₂ < (c i₂ j₀ : ℚ) * rStar i₁ := by
        dsimp [f] at hf12
        rwa [div_lt_div_iff₀ hr1 hr2] at hf12
      rcases hf_gap i with hle1 | hge2
      · dsimp [f] at hle1
        have h1 : (c i j₀ : ℚ) * rStar i₁ ≤ (c i₁ j₀ : ℚ) * rStar i :=
          (div_le_div_iff₀ hri hr1).mp hle1
        nlinarith
      · dsimp [f] at hge2
        have h2 : (c i₂ j₀ : ℚ) * rStar i ≤ (c i j₀ : ℚ) * rStar i₂ :=
          (div_le_div_iff₀ hr2 hri).mp hge2
        nlinarith
    obtain ⟨Mw, a, hMw_pos, ha_pos, ha_eq⟩ :=
      clear_pos_rat_denoms (fun i => |wStar i|) hwStar_abs_pos
    have ha_collide : a i₁ = a i₂ := by
      have hq : (a i₁ : ℚ) = (a i₂ : ℚ) := by
        rw [ha_eq i₁, ha_eq i₂, hwStar_collide]
      exact Nat.cast_injective hq
    let Aset : Finset ℕ := Finset.univ.image a
    have hA_sub : Aset ⊆ (Finset.univ.erase i₂).image a := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rcases eq_or_ne i i₂ with rfl | hne
      · rw [← ha_collide]
        exact Finset.mem_image.mpr ⟨i₁, Finset.mem_erase.mpr ⟨hi₁_ne_i₂, Finset.mem_univ i₁⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ i⟩, rfl⟩
    let m : ℕ := Aset.card
    have hm_pos : 1 ≤ m := by
      have hne : Aset.Nonempty := ⟨a i₀, Finset.mem_image_of_mem a (Finset.mem_univ i₀)⟩
      exact Finset.card_pos.mpr hne
    have hm_lt : m < k := by
      have h1 : Aset.card ≤ ((Finset.univ.erase i₂).image a).card := Finset.card_le_card hA_sub
      have h2 : ((Finset.univ.erase i₂).image a).card ≤ (Finset.univ.erase i₂).card :=
        Finset.card_image_le
      have h3 : (Finset.univ.erase i₂).card = k - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i₂), Finset.card_fin]
      omega
    let emb := Aset.orderEmbOfFin rfl
    let w_int : Fin m → ℕ := fun l => emb l
    have hw_int_pos : ∀ l : Fin m, 0 < w_int l := by
      intro l
      have hmem : w_int l ∈ Aset := Finset.orderEmbOfFin_mem Aset rfl l
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      rw [← hi]
      exact ha_pos i
    have hw_int_mono : StrictMono w_int := emb.strictMono
    obtain ⟨t₀, ht₀_nonneg, ht₀_lonely⟩ := h_int m hm_pos hm_lt.le w_int hw_int_pos hw_int_mono
    have ha_lonely : ∀ i : Fin k,
        dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 ≥ 1 / (k : ℝ) := by
      intro i
      have hmem : a i ∈ (Aset : Set ℕ) :=
        Finset.mem_coe.mpr (Finset.mem_image_of_mem a (Finset.mem_univ i))
      have hrange : Set.range w_int = (Aset : Set ℕ) := Finset.range_orderEmbOfFin Aset rfl
      obtain ⟨l, hl⟩ : ∃ l : Fin m, w_int l = a i := by rwa [← hrange] at hmem
      have hstep := ht₀_lonely l
      rw [hl] at hstep
      have ha_r : (a i : ℝ) = (Mw : ℝ) * |(wStar i : ℝ)| := by
        have := ha_eq i
        exact_mod_cast this
      have hdist_eq : dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 =
          dist ((t₀ * (a i : ℝ) : ℝ) : UnitAddCircle) 0 := by
        rw [ha_r, ← mul_assoc, unitAddCircle_dist_abs_mul]
      rw [hdist_eq]
      have hmk_le : m + 1 ≤ k := by omega
      have hfrac : 1 / (k : ℝ) ≤ 1 / ((m + 1 : ℕ) : ℝ) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hmk_le)
      exact le_trans hfrac hstep
    let θ : Fin d → UnitAddCircle := fun j => ((t₀ * (Mw : ℝ) * (η j : ℝ) : ℝ) : UnitAddCircle)
    have hθ_sum : ∀ i : Fin k,
        ∑ j : Fin d, c i j • θ j = ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) := by
      intro i
      dsimp [θ]
      rw [← mk_sum_int_mul]
      congr 1
      dsimp [wStar]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => by ring
    let gap : ℝ := 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)
    have hgap_pos : 0 < gap := by
      dsimp [gap]
      refine sub_pos.mpr ?_
      exact one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.lt_succ_self k)
    let ε : ℝ := gap / (2 * Csum)
    have hε_pos : 0 < ε := div_pos hgap_pos (by positivity)
    obtain ⟨t, ht_nonneg, ht_approx⟩ := kronecker_pos e he_li θ hε_pos
    refine ⟨t, ht_nonneg, fun i => ?_⟩
    have htv_sum : ((t * v i : ℝ) : UnitAddCircle) =
        ∑ j : Fin d, c i j • ((t * e j : ℝ) : UnitAddCircle) := by
      rw [← mk_sum_int_mul, hve i, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    have hclose : dist ((t * v i : ℝ) : UnitAddCircle)
        ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) ≤ gap / 2 := by
      rw [htv_sum, ← hθ_sum i]
      calc dist (∑ j : Fin d, c i j • ((t * e j : ℝ) : UnitAddCircle)) (∑ j : Fin d, c i j • θ j)
          ≤ ∑ j : Fin d, |(c i j : ℝ)| * dist ((t * e j : ℝ) : UnitAddCircle) (θ j) :=
            dist_sum_zsmul_le (c i) _ θ
        _ ≤ ∑ j : Fin d, |(c i j : ℝ)| * ε := by
            refine Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_left (ht_approx j).le (abs_nonneg _)
        _ = (∑ j : Fin d, |(c i j : ℝ)|) * ε := (Finset.sum_mul _ _ _).symm
        _ ≤ Csum * ε := by
            refine mul_le_mul_of_nonneg_right ?_ hε_pos.le
            have hle_i : (∑ j : Fin d, |(c i j : ℝ)|) ≤ ∑ i' : Fin k, ∑ j : Fin d, |(c i' j : ℝ)| :=
              Finset.single_le_sum (f := fun i' : Fin k => ∑ j : Fin d, |(c i' j : ℝ)|)
                (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            dsimp [Csum]; linarith
        _ = gap / 2 := by
            dsimp [ε]
            field_simp [ne_of_gt hCsum_pos]
    have hbase := ha_lonely i
    have htri : dist ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) 0 ≤
        dist ((t * v i : ℝ) : UnitAddCircle)
          ((t₀ * (Mw : ℝ) * (wStar i : ℝ) : ℝ) : UnitAddCircle) +
        dist ((t * v i : ℝ) : UnitAddCircle) 0 := by
      rw [dist_comm ((t * v i : ℝ) : UnitAddCircle)]
      exact dist_triangle _ _ _
    have hfin : 1 / ((k + 1 : ℕ) : ℝ) ≤ dist ((t * v i : ℝ) : UnitAddCircle) 0 := by
      dsimp [gap] at hclose hgap_pos
      linarith
    exact hfin

end

theorem OMA.solution : OMA.R_LonelyRunnerConjecture_lonely_runner_conjecture_R1.H1 := by
  intro k hk3 v hv_pos hv_mono _ h_int
  exact real_to_nat_lrc k (by omega) v hv_pos hv_mono h_int
