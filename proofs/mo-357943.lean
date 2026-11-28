import OMAStatements.S_mo_357943

namespace OMA.S_mo_357943_Proof

open OMA.S_mo_357943 Matrix Finset MeasureTheory ProbabilityTheory
open scoped NNReal

private lemma norm_direction_le_one {d : ℕ} (x : E d) : ‖direction x‖ ≤ 1 := by
  by_cases hx : x = 0
  · simp [direction, hx]
  · have hpos : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    simp [direction, norm_smul, hpos]

private lemma norm_direction_sq_le_one {d : ℕ} (x : E d) : ‖direction x‖ ^ 2 ≤ 1 := by
  nlinarith [norm_direction_le_one x, norm_nonneg (direction x)]

private lemma abs_direction_apply_le_one {d : ℕ} (x : E d) (i : Fin d) : |direction x i| ≤ 1 := by
  have h1 : ‖direction x i‖ ≤ ‖direction x‖ := PiLp.norm_apply_le (direction x) i
  rw [Real.norm_eq_abs] at h1
  exact h1.trans (norm_direction_le_one x)

private lemma measurable_direction {d : ℕ} : Measurable (@direction d) :=
  measurable_norm.inv.smul measurable_id

private lemma measurable_direction_apply {d : ℕ} (i : Fin d) :
    Measurable (fun x : E d => direction x i) :=
  ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable).comp measurable_direction

private lemma integrable_direction_mul {d : ℕ} (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (i j : Fin d) : Integrable (fun x => direction x i * direction x j) μ := by
  refine Integrable.of_bound
    (((measurable_direction_apply i).mul (measurable_direction_apply j)).aestronglyMeasurable)
    1 (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hi := abs_direction_apply_le_one x i
  have hj := abs_direction_apply_le_one x j
  have hi0 := abs_nonneg (direction x i)
  have hj0 := abs_nonneg (direction x j)
  nlinarith

private lemma part1 (d : ℕ) (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    (angular μ).PosSemidef ∧ (angular μ).trace ≤ 1 := by
  constructor
  · refine ⟨?_, ?_⟩
    · ext i j
      simp [Matrix.conjTranspose_apply, angular, mul_comm]
    · intro x
      have hrewrite :
          (x.sum fun i xi => x.sum fun j xj => star xi * angular μ i j * xj) =
            ∫ y, (x.sum fun i xi => xi * direction y i) ^ 2 ∂μ := by
        simp only [Finsupp.sum, star_trivial, angular]
        have hterm : ∀ i j : Fin d,
            x i * (∫ y, direction y i * direction y j ∂μ) * x j =
              ∫ y, (x i * direction y i) * (x j * direction y j) ∂μ := by
          intro i j
          have h1 : ∀ y, (x i * direction y i) * (x j * direction y j) =
              (x i * x j) * (direction y i * direction y j) := fun y => by ring
          simp_rw [h1, integral_const_mul]
          ring
        simp_rw [hterm]
        have hint : ∀ i j : Fin d,
            Integrable (fun y => (x i * direction y i) * (x j * direction y j)) μ := by
          intro i j
          have h1 : (fun y => (x i * direction y i) * (x j * direction y j)) =
              (fun y => (x i * x j) * (direction y i * direction y j)) := by
            ext y; ring
          rw [h1]
          exact (integrable_direction_mul μ i j).const_mul (x i * x j)
        have hinner : ∀ i ∈ x.support,
            (∑ j ∈ x.support, ∫ y, (x i * direction y i) * (x j * direction y j) ∂μ) =
              ∫ y, ∑ j ∈ x.support, (x i * direction y i) * (x j * direction y j) ∂μ := by
          intro i _
          exact (integral_finsetSum x.support (fun j _ => hint i j)).symm
        rw [Finset.sum_congr rfl hinner]
        rw [← integral_finsetSum x.support
          (fun i _ => integrable_finsetSum x.support (fun j _ => hint i j))]
        congr 1
        ext y
        rw [sq, Finset.sum_mul_sum]
      rw [hrewrite]
      exact integral_nonneg fun y => sq_nonneg _
  · rw [Matrix.trace]
    simp only [Matrix.diag_apply, angular]
    rw [← integral_finsetSum Finset.univ (fun i _ => integrable_direction_mul μ i i)]
    calc
      (∫ x, ∑ i : Fin d, direction x i * direction x i ∂μ)
          ≤ ∫ _ : E d, (1 : ℝ) ∂μ := by
        refine integral_mono
          (integrable_finsetSum Finset.univ (fun i _ => integrable_direction_mul μ i i))
          (integrable_const 1) (fun x => ?_)
        have hsq : ∑ i : Fin d, direction x i * direction x i = ‖direction x‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          congr 1
          ext i
          rw [Real.norm_eq_abs, sq_abs, sq]
        rw [hsq]
        exact norm_direction_sq_le_one x
      _ = 1 := by simp

private lemma spectral_entry {d : ℕ} {M : Mat d} (hH : M.IsHermitian) (i j : Fin d) :
    M i j = ∑ k : Fin d, hH.eigenvalues k * (hH.eigenvectorBasis k i * hH.eigenvectorBasis k j) := by
  have hspec := congr_fun (congr_fun hH.spectral_theorem i) j
  rw [Unitary.conjStarAlgAut_apply] at hspec
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Function.comp_apply, RCLike.ofReal_real_eq_id,
    id_eq, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Matrix.star_apply, star_trivial, Matrix.IsHermitian.eigenvectorUnitary_apply] at hspec
  rw [hspec]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma part2 (d : ℕ) (M : Mat d) (hM : M.PosSemidef) (hTr : M.trace ≤ 1)
    (σ : ℝ≥0) (hσ : 0 < σ) :
    ∃ μ : Measure (E d), IsProbabilityMeasure μ ∧
      subgaussian μ σ ∧ angular μ = M ∧
      ∃ S : Finset (E d), S.card ≤ 2 * d + 1 ∧ μ (S : Set (E d))ᶜ = 0 := by
  let hH : M.IsHermitian := hM.1
  let lam : Fin d → ℝ := hH.eigenvalues
  let b : OrthonormalBasis (Fin d) ℝ (E d) := hH.eigenvectorBasis
  let r : ℝ := (σ : ℝ)
  have hr : 0 < r := by exact_mod_cast hσ
  have hlam : ∀ k : Fin d, 0 ≤ lam k := fun k => hM.eigenvalues_nonneg k
  have hsum_lam : ∑ k : Fin d, lam k = M.trace := by
    simpa [lam] using hH.trace_eq_sum_eigenvalues.symm
  let p0 : ℝ := 1 - ∑ k : Fin d, lam k
  have hp0 : 0 ≤ p0 := sub_nonneg.mpr (hsum_lam ▸ hTr)
  let μk : Fin d → Measure (E d) := fun k =>
    ENNReal.ofReal (lam k / 2) • Measure.dirac (r • b k) +
      ENNReal.ofReal (lam k / 2) • Measure.dirac (-(r • b k))
  let μ : Measure (E d) := ENNReal.ofReal p0 • Measure.dirac 0 + ∑ k : Fin d, μk k
  have hμ_univ : μ Set.univ = 1 := by
    simp only [μ, μk, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
      mul_one]
    have hsum_k : ∀ k : Fin d,
        ENNReal.ofReal (lam k / 2) + ENNReal.ofReal (lam k / 2) = ENNReal.ofReal (lam k) := by
      intro k
      rw [← ENNReal.ofReal_add (by linarith [hlam k]) (by linarith [hlam k])]
      ring_nf
    simp_rw [hsum_k]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => hlam k)]
    rw [← ENNReal.ofReal_add hp0 (Finset.sum_nonneg fun k _ => hlam k)]
    have h1 : p0 + ∑ k : Fin d, lam k = 1 := by dsimp [p0]; ring
    rw [h1, ENNReal.ofReal_one]
  have hProb : IsProbabilityMeasure μ := ⟨hμ_univ⟩
  have hdir_int : ∀ (f : E d → ℝ) (c : ℝ) (a : E d),
      Integrable f (ENNReal.ofReal c • Measure.dirac a) := fun f c a =>
    (integrable_dirac (f := f) (a := a) enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hint_μ : ∀ f : E d → ℝ, Integrable f μ := by
    intro f
    refine Integrable.add_measure (hdir_int f p0 0) ?_
    refine integrable_finsetSum_measure.mpr fun k _ => ?_
    exact Integrable.add_measure (hdir_int f (lam k / 2) (r • b k))
      (hdir_int f (lam k / 2) (-(r • b k)))
  have hintegral_μ : ∀ f : E d → ℝ,
      ∫ x, f x ∂μ =
        p0 * f 0 + ∑ k : Fin d, ((lam k / 2) * f (r • b k) + (lam k / 2) * f (-(r • b k))) := by
    intro f
    have h0 : Integrable f (ENNReal.ofReal p0 • Measure.dirac (0 : E d)) := hdir_int f p0 0
    have hk : ∀ k : Fin d, Integrable f (μk k) := fun k =>
      Integrable.add_measure (hdir_int f (lam k / 2) (r • b k))
        (hdir_int f (lam k / 2) (-(r • b k)))
    have hsum_int : Integrable f (∑ k : Fin d, μk k) :=
      integrable_finsetSum_measure.mpr fun k _ => hk k
    dsimp only [μ]
    rw [integral_add_measure h0 hsum_int]
    rw [integral_smul_measure, ENNReal.toReal_ofReal hp0, integral_dirac, smul_eq_mul]
    rw [integral_finsetSum_measure fun k _ => hk k]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    dsimp only [μk]
    rw [integral_add_measure (hdir_int f (lam k / 2) (r • b k))
      (hdir_int f (lam k / 2) (-(r • b k)))]
    rw [integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (by linarith [hlam k]), integral_dirac, integral_dirac,
      smul_eq_mul, smul_eq_mul]
  have hnorm_b : ∀ k : Fin d, ‖b k‖ = 1 := fun k => b.orthonormal.1 k
  have hsubg : subgaussian μ σ := by
    intro v hv
    refine ⟨fun t => hint_μ _, fun t => ?_⟩
    rw [mgf, hintegral_μ]
    have hexp_pos : 0 ≤ ((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 := by positivity
    have h0_le : p0 * Real.exp (t * inner ℝ v 0) ≤
        p0 * Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
      rw [inner_zero_right, mul_zero, Real.exp_zero]
      exact mul_le_mul_of_nonneg_left (Real.one_le_exp hexp_pos) hp0
    have hk_le : ∀ k : Fin d,
        (lam k / 2) * Real.exp (t * inner ℝ v (r • b k)) +
          (lam k / 2) * Real.exp (t * inner ℝ v (-(r • b k))) ≤
          lam k * Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
      intro k
      set u : ℝ := t * inner ℝ v (r • b k)
      have hneg : t * inner ℝ v (-(r • b k)) = -u := by
        rw [inner_neg_right, mul_neg]
      rw [hneg]
      have hcosh :
          (lam k / 2) * Real.exp u + (lam k / 2) * Real.exp (-u) = lam k * Real.cosh u := by
        rw [Real.cosh_eq]
        ring
      rw [hcosh]
      refine mul_le_mul_of_nonneg_left ?_ (hlam k)
      refine (Real.cosh_le_exp_half_sq u).trans ?_
      refine Real.exp_le_exp.mpr ?_
      have habs : |inner ℝ v (r • b k)| ≤ r := by
        calc
          |inner ℝ v (r • b k)| ≤ ‖v‖ * ‖r • b k‖ := abs_real_inner_le_norm v (r • b k)
          _ = 1 * (|r| * ‖b k‖) := by rw [hv, norm_smul, Real.norm_eq_abs]
          _ = r := by rw [abs_of_pos hr, hnorm_b k]; ring
      have hsq : u ^ 2 ≤ ((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 := by
        have h1 : (inner ℝ v (r • b k)) ^ 2 ≤ r ^ 2 := by
          rw [← sq_abs]
          exact sq_le_sq' (by linarith [abs_nonneg (inner ℝ v (r • b k))]) habs
        have hr_eq : r ^ 2 = ((σ ^ 2 : ℝ≥0) : ℝ) := by simp [r]
        rw [← hr_eq]
        dsimp [u]
        nlinarith [sq_nonneg t]
      linarith
    calc
      p0 * Real.exp (t * inner ℝ v 0) +
          ∑ k : Fin d,
            ((lam k / 2) * Real.exp (t * inner ℝ v (r • b k)) +
              (lam k / 2) * Real.exp (t * inner ℝ v (-(r • b k))))
          ≤ p0 * Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) +
              ∑ k : Fin d, lam k * Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) :=
        add_le_add h0_le (Finset.sum_le_sum fun k _ => hk_le k)
      _ = (p0 + ∑ k : Fin d, lam k) * Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
        rw [← Finset.sum_mul, ← add_mul]
      _ = Real.exp (((σ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
        have h1 : p0 + ∑ k : Fin d, lam k = 1 := by dsimp [p0]; ring
        rw [h1, one_mul]
  have hang : angular μ = M := by
    ext i j
    change ∫ x, direction x i * direction x j ∂μ = M i j
    rw [hintegral_μ]
    have hdir0 : direction (0 : E d) = 0 := by simp [direction]
    have hdir_pos : ∀ k : Fin d, direction (r • b k) = b k := by
      intro k
      have hn : ‖r • b k‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm_b k, mul_one]
      rw [direction, hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    have hdir_neg : ∀ k : Fin d, direction (-(r • b k)) = -(b k) := by
      intro k
      have hn : ‖-(r • b k)‖ = r := by
        rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hnorm_b k, mul_one]
      rw [direction, hn, smul_neg, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    simp only [hdir0, PiLp.zero_apply, mul_zero, zero_add, hdir_pos, hdir_neg, PiLp.neg_apply,
      neg_mul, mul_neg, neg_neg]
    rw [spectral_entry hH i j]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  let S : Finset (E d) :=
    insert 0
      ((Finset.univ.image (fun k : Fin d => r • b k)) ∪
        (Finset.univ.image (fun k : Fin d => -(r • b k))))
  have hScard : S.card ≤ 2 * d + 1 := by
    have h1 : S.card ≤ ((Finset.univ.image (fun k : Fin d => r • b k)) ∪
        (Finset.univ.image (fun k : Fin d => -(r • b k)))).card + 1 :=
      Finset.card_insert_le _ _
    have h2 : ((Finset.univ.image (fun k : Fin d => r • b k)) ∪
        (Finset.univ.image (fun k : Fin d => -(r • b k)))).card ≤
        (Finset.univ.image (fun k : Fin d => r • b k)).card +
        (Finset.univ.image (fun k : Fin d => -(r • b k))).card :=
      Finset.card_union_le _ _
    have h3 : (Finset.univ.image (fun k : Fin d => r • b k)).card ≤ d := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
        (f := fun k => r • b k)
    have h4 : (Finset.univ.image (fun k : Fin d => -(r • b k))).card ≤ d := by
      simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin d)))
        (f := fun k => -(r • b k))
    omega
  have hSsupp : μ (S : Set (E d))ᶜ = 0 := by
    have h0S : (0 : E d) ∈ S := by simp [S]
    have hposS : ∀ k : Fin d, r • b k ∈ S := by
      intro k
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact Or.inr (Or.inl ⟨k, rfl⟩)
    have hnegS : ∀ k : Fin d, -(r • b k) ∈ S := by
      intro k
      simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact Or.inr (Or.inr ⟨k, rfl⟩)
    have hmeas : MeasurableSet ((S : Set (E d))ᶜ) := S.finite_toSet.measurableSet.compl
    simp only [μ, μk, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hmeas]
    simp [h0S, hposS, hnegS]
  exact ⟨μ, hProb, hsubg, hang, S, hScard, hSsupp⟩

private noncomputable def flipCoord {d : ℕ} (i : Fin d) : E d ≃ₗᵢ[ℝ] E d :=
  { toFun := fun x => WithLp.toLp 2 (fun k => if k = i then -x k else x k)
    invFun := fun x => WithLp.toLp 2 (fun k => if k = i then -x k else x k)
    map_add' := fun x y => by
      ext k
      by_cases hk : k = i
      · simp [hk]
        ring
      · simp [hk]
    map_smul' := fun c x => by
      ext k
      by_cases hk : k = i <;> simp [hk]
    left_inv := fun x => by
      ext k
      by_cases hk : k = i <;> simp [hk]
    right_inv := fun x => by
      ext k
      by_cases hk : k = i <;> simp [hk]
    norm_map' := fun x => by
      have hsq : ‖WithLp.toLp 2 (fun k : Fin d => if k = i then -x k else x k)‖ ^ 2 = ‖x‖ ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = i <;> simp [hk]
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq }

private noncomputable def swapCoord {d : ℕ} (i k : Fin d) : E d ≃ₗᵢ[ℝ] E d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i k)

private noncomputable def sphereActionME {d : ℕ} (U : E d ≃ₗᵢ[ℝ] E d) :
    Sphere d ≃ᵐ Sphere d where
  toFun := sphereAction U
  invFun := sphereAction U.symm
  left_inv := fun v => Subtype.ext (U.symm_apply_apply v.val)
  right_inv := fun v => Subtype.ext (U.apply_symm_apply v.val)
  measurable_toFun :=
    (U.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable
  measurable_invFun :=
    (U.symm.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

private lemma integrable_sphere_mul {d : ℕ} (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (i j : Fin d) : Integrable (fun v : Sphere d => v.val i * v.val j) ν := by
  have hcont : Continuous (fun v : Sphere d => v.val i * v.val j) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j).comp continuous_subtype_val)
  refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun v => ?_)
  have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  have hi : |v.val i| ≤ 1 := by
    have h1 : ‖v.val i‖ ≤ ‖v.val‖ := PiLp.norm_apply_le v.val i
    rwa [Real.norm_eq_abs, hv] at h1
  have hj : |v.val j| ≤ 1 := by
    have h1 : ‖v.val j‖ ≤ ‖v.val‖ := PiLp.norm_apply_le v.val j
    rwa [Real.norm_eq_abs, hv] at h1
  rw [Real.norm_eq_abs, abs_mul]
  have hi0 := abs_nonneg (v.val i)
  have hj0 := abs_nonneg (v.val j)
  nlinarith

private lemma part3 (d : ℕ) (hd : 0 < d) (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hν : orthInvariant ν) (i j : Fin d) :
    (∫ v : Sphere d, v.val i * v.val j ∂ν) = if i = j then 1 / (d : ℝ) else 0 := by
  by_cases hij : i = j
  · subst hij
    have heq : ∀ k : Fin d,
        (∫ v : Sphere d, v.val k * v.val k ∂ν) = ∫ v : Sphere d, v.val i * v.val i ∂ν := by
      intro k
      let U := swapCoord i k
      have hmp : MeasurePreserving (sphereActionME U) ν ν := hν U
      have hcomp := hmp.integral_comp (sphereActionME U).measurableEmbedding
        (fun v : Sphere d => v.val i * v.val i)
      rw [← hcomp]
      congr 1
      ext v
      have hval : (sphereActionME U v).val i = v.val k := by
        change (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i k) v.val) i = v.val k
        rw [LinearIsometryEquiv.piLpCongrLeft_apply]
        simp [Equiv.piCongrLeft']
      rw [hval]
    have hsum : ∑ k : Fin d, (∫ v : Sphere d, v.val k * v.val k ∂ν) = 1 := by
      rw [← integral_finsetSum Finset.univ (fun k _ => integrable_sphere_mul ν k k)]
      have hconst : (fun v : Sphere d => ∑ k : Fin d, v.val k * v.val k) = fun _ => (1 : ℝ) := by
        ext v
        have hv : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
        have hsq : ∑ k : Fin d, v.val k * v.val k = ‖v.val‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          congr 1
          ext k
          rw [Real.norm_eq_abs, sq_abs, sq]
        rw [hsq, hv, one_pow]
      rw [hconst]
      simp
    have hsum2 : ∑ k : Fin d, (∫ v : Sphere d, v.val k * v.val k ∂ν) =
        (d : ℝ) * (∫ v : Sphere d, v.val i * v.val i ∂ν) := by
      simp_rw [heq]
      simp [Finset.sum_const, nsmul_eq_mul]
    have hd_ne : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [↓reduceIte]
    rw [eq_div_iff hd_ne, mul_comm]
    linarith
  · simp only [hij, ↓reduceIte]
    let U := flipCoord i
    have hmp : MeasurePreserving (sphereActionME U) ν ν := hν U
    have hcomp := hmp.integral_comp (sphereActionME U).measurableEmbedding
      (fun v : Sphere d => v.val i * v.val j)
    have hneg :
        (∫ v : Sphere d, (sphereActionME U v).val i * (sphereActionME U v).val j ∂ν) =
          -(∫ v : Sphere d, v.val i * v.val j ∂ν) := by
      rw [← integral_neg]
      congr 1
      ext v
      have hi : (sphereActionME U v).val i = -(v.val i) := by
        change (flipCoord i v.val) i = -(v.val i)
        simp [flipCoord]
      have hj : (sphereActionME U v).val j = v.val j := by
        change (flipCoord i v.val) j = v.val j
        simp [flipCoord, Ne.symm hij]
      rw [hi, hj, neg_mul]
    linarith

end OMA.S_mo_357943_Proof

theorem OMA.solution : type_of% @OMA.S_mo_357943.main :=
  ⟨OMA.S_mo_357943_Proof.part1, OMA.S_mo_357943_Proof.part2, OMA.S_mo_357943_Proof.part3⟩
