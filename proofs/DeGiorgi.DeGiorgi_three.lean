import FormalConjectures.Paper.DeGiorgi

/-! # Proof of De Giorgi's Conjecture in Dimension 3 (Ambrosio–Cabré) -/

namespace OMA.R_DeGiorgi_DeGiorgi_three_R1

open EuclideanGeometry InnerProductSpace MeasureTheory Set

private theorem hyperplanes_of_constant_quotient (u : ℝ^3 → ℝ)
    (hu : Differentiable ℝ u)
    (hv : ∀ x, 0 < fderiv ℝ u x (EuclideanSpace.single 0 1))
    (c1 c2 : ℝ)
    (hw1 : ∀ x, fderiv ℝ u x (EuclideanSpace.single 1 1) =
      c1 * fderiv ℝ u x (EuclideanSpace.single 0 1))
    (hw2 : ∀ x, fderiv ℝ u x (EuclideanSpace.single 2 1) =
      c2 * fderiv ℝ u x (EuclideanSpace.single 0 1)) :
    DeGiorgi.HasHyperplaneLevelSets u := by
  let e0 : ℝ^3 := EuclideanSpace.single 0 1
  let e1 : ℝ^3 := EuclideanSpace.single 1 1
  let e2 : ℝ^3 := EuclideanSpace.single 2 1
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let L : ℝ^3 →ₗ[ℝ] ℝ := b.coord 0 + c1 • b.coord 1 + c2 • b.coord 2
  have hL (d : ℝ^3) : L d = d 0 + c1 * d 1 + c2 * d 2 := by
    simp [L, b, Module.Basis.coord_apply, EuclideanSpace.basisFun_repr]
  have hL0 : L e0 = 1 := by simp [hL, e0]
  have hbasis (d : ℝ^3) : d = d 0 • e0 + d 1 • e1 + d 2 • e2 := by
    ext i
    fin_cases i <;> simp [e0, e1, e2]
  have hgradient (x d : ℝ^3) :
      fderiv ℝ u x d = fderiv ℝ u x e0 * L d := by
    conv_lhs => rw [hbasis d]
    rw [map_add, map_add, map_smul, map_smul, map_smul, hL]
    change d 0 * fderiv ℝ u x e0 + d 1 * fderiv ℝ u x e1 + d 2 * fderiv ℝ u x e2 =
      fderiv ℝ u x e0 * (d 0 + c1 * d 1 + c2 * d 2)
    rw [show fderiv ℝ u x e1 = c1 * fderiv ℝ u x e0 from hw1 x,
        show fderiv ℝ u x e2 = c2 * fderiv ℝ u x e0 from hw2 x]
    ring
  have hline (x d : ℝ^3) (t : ℝ) :
      HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t := by
    exact (hu _).hasFDerivAt.comp_hasDerivAt t
      (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))
  have hsame (x z : ℝ^3) (h : L x = L z) : u x = u z := by
    have hd : L (z - x) = 0 := by rw [map_sub, h, sub_self]
    have hconst (t : ℝ) : deriv (fun s : ℝ => u (x + s • (z - x))) t = 0 := by
      rw [(hline x (z - x) t).deriv, hgradient, hd, mul_zero]
    have h01 := is_const_of_deriv_eq_zero
      (fun t => (hline x (z - x) t).differentiableAt) hconst 0 1
    simpa [add_comm] using h01
  have hdifferent (x z : ℝ^3) (h : u x = u z) : L x = L z := by
    let t := L x - L z
    have hLz : L (z + t • e0) = L x := by
      rw [map_add, map_smul, hL0]
      simp [t]
    have hu0 : u (z + t • e0) = u z := (hsame _ _ hLz).trans h
    have hinj : Function.Injective (fun s : ℝ => u (z + s • e0)) := by
      apply StrictMono.injective
      apply strictMono_of_deriv_pos
      intro s
      rw [(hline z e0 s).deriv]
      exact hv _
    have ht : t = 0 := hinj (by simpa using hu0)
    exact sub_eq_zero.mp ht
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  refine ⟨AffineSubspace.mk' x L.ker, ?_, ?_⟩
  · ext z
    change u z = u x ↔ z ∈ AffineSubspace.mk' x L.ker
    rw [AffineSubspace.mem_mk', vsub_eq_sub, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact ⟨hdifferent z x, hsame z x⟩
  · have hsurj : Function.Surjective L := fun r => ⟨r • e0, by simp [hL0]⟩
    have hdim := L.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_euclideanSpace_fin] at hdim
    simp only [Module.finrank_self] at hdim
    rw [AffineSubspace.direction_mk']
    omega

/-- Quadratic energy growth bound on balls of radius R for partial derivatives
of monotone bounded solutions in dimension 3. -/
def H1 : Prop :=
  ∀ (u : ℝ^3 → ℝ) (i : Fin 3),
    DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤ C * R ^ 2

/-- The weak divergence-form equation for each derivative quotient, tested against
compactly supported functions. -/
def H2 : Prop :=
  ∀ (u : ℝ^3 → ℝ) (i : Fin 3),
    DeGiorgi.IsBoundedSolution u → DeGiorgi.HasPositiveDeriv u →
    let v := fun x => fderiv ℝ u x (EuclideanSpace.single 0 1)
    let w := fun x => fderiv ℝ u x (EuclideanSpace.single i 1)
    let q := fun x => w x / v x
    ∀ η : ℝ^3 → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0

/-- The 3D weighted Liouville theorem of Ambrosio and Cabré: if v > 0 and v * q
has O(R^2) L^2-energy growth on balls of radius R, any weak solution to
div(v^2 grad q) = 0 on R^3 is constant. -/
def H3 : Prop :=
  ∀ (v q : ℝ^3 → ℝ),
    ContDiff ℝ 1 v → ContDiff ℝ 1 q → (∀ x, 0 < v x) →
    (∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q x) ^ 2) ≤ C * R ^ 2) →
    (∀ η : ℝ^3 → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (gradient q x) (gradient η x)) = 0) →
    ∃ c : ℝ, ∀ x, q x = c

theorem main : H1 → H2 → H3 → DeGiorgi.DeGiorgi_conclusion 3 := by
  intro hbound hequation hliouville u ⟨hu, hup⟩
  let v := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 0 1)
  let w1 := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 1 1)
  let w2 := fun x : ℝ^3 => fderiv ℝ u x (EuclideanSpace.single 2 1)
  let q1 := fun x : ℝ^3 => w1 x / v x
  let q2 := fun x : ℝ^3 => w2 x / v x
  have hud : Differentiable ℝ u := hu.regular.differentiable (by norm_num)
  have hv : ∀ x, 0 < v x := by
    intro x
    simpa only [(hud x).lineDeriv_eq_fderiv] using hup x
  have hder : ContDiff ℝ 1 (fderiv ℝ u) := hu.regular.fderiv_right (by norm_num)
  have hvC : ContDiff ℝ 1 v := hder.clm_apply contDiff_const
  have hw1C : ContDiff ℝ 1 w1 := hder.clm_apply contDiff_const
  have hw2C : ContDiff ℝ 1 w2 := hder.clm_apply contDiff_const
  have hq1C : ContDiff ℝ 1 q1 := hw1C.div hvC fun x => (hv x).ne'
  have hq2C : ContDiff ℝ 1 q2 := hw2C.div hvC fun x => (hv x).ne'
  have hmul1 (x : ℝ^3) : v x * q1 x = w1 x := by
    dsimp [q1]
    field_simp [(hv x).ne']
  have hmul2 (x : ℝ^3) : v x * q2 x = w2 x := by
    dsimp [q2]
    field_simp [(hv x).ne']
  obtain ⟨C1, hC1⟩ := hbound u 1 hu hup
  obtain ⟨C2, hC2⟩ := hbound u 2 hu hup
  have hbounded1 : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q1 x) ^ 2) ≤ C * R ^ 2 := by
    refine ⟨C1, fun R hR => ?_⟩
    simp only [hmul1]
    exact hC1 R hR
  have hbounded2 : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : ℝ^3) R, (v x * q2 x) ^ 2) ≤ C * R ^ 2 := by
    refine ⟨C2, fun R hR => ?_⟩
    simp only [hmul2]
    exact hC2 R hR
  obtain ⟨c1, hc1⟩ := hliouville v q1 hvC hq1C hv hbounded1 (hequation u 1 hu hup)
  obtain ⟨c2, hc2⟩ := hliouville v q2 hvC hq2C hv hbounded2 (hequation u 2 hu hup)
  refine hyperplanes_of_constant_quotient u hud hv c1 c2
    (fun x => (div_eq_iff (hv x).ne').mp (hc1 x))
    (fun x => (div_eq_iff (hv x).ne').mp (hc2 x))

end OMA.R_DeGiorgi_DeGiorgi_three_R1

namespace OMA.DeGiorgiWeak3

open EuclideanGeometry InnerProductSpace MeasureTheory Filter Set Finset
open scoped Gradient Laplacian Topology

abbrev Plane := ℝ^3

noncomputable def partialDerivative (u : Plane → ℝ) (e : Plane) (x : Plane) : ℝ :=
  fderiv ℝ u x e

private theorem partial_continuous {u : Plane → ℝ} (h : ContDiff ℝ 1 u) (e : Plane) :
    Continuous (partialDerivative u e) :=
  (h.continuous_fderiv one_ne_zero).clm_apply continuous_const

private theorem partial_contDiff {u : Plane → ℝ} (h : ContDiff ℝ 2 u) (e : Plane) :
    ContDiff ℝ 1 (partialDerivative u e) :=
  (h.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem partial_compact {u : Plane → ℝ} (h : HasCompactSupport u) (e : Plane) :
    HasCompactSupport (partialDerivative u e) :=
  h.fderiv_apply ℝ e

private theorem integrate_compact_mul {a b : Plane → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hs : HasCompactSupport a) :
    Integrable (fun x => a x * b x) :=
  (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_right (f' := b))

private theorem translated_deriv {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (x e : Plane) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x + s • e)) (partialDerivative f e (x + t • e)) t := by
  exact (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const e).const_add x))

private theorem shifted_integral_deriv {a f : Plane → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : ContDiff ℝ 1 f) (e : Plane) :
    HasDerivAt (fun t : ℝ => ∫ x, a x * f (x + t • e))
      (∫ x, a x * partialDerivative f e x) 0 := by
  let F := fun (t : ℝ) (x : Plane) => a x * f (x + t • e)
  let D := fun (t : ℝ) (x : Plane) => a x * partialDerivative f e (x + t • e)
  let S := tsupport a
  let T : Set ℝ := Set.Icc (-1) 1
  have hT : T ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  have hS : MeasurableSet S := (isClosed_tsupport a).measurableSet
  have hjoint : Continuous (fun p : ℝ × Plane => D p.1 p.2) :=
    (ha.comp continuous_snd).mul
      ((partial_continuous hf e).comp (continuous_snd.add (continuous_fst.smul continuous_const)))
  have hTC : IsCompact T := isCompact_Icc
  obtain ⟨M, hM⟩ := (hTC.prod hc).exists_bound_of_continuousOn hjoint.continuousOn
  let bound := S.indicator fun _ => M
  have hBound : Integrable bound :=
    (integrableOn_const (μ := volume) (C := M)
      (hs := hc.measure_lt_top.ne)).integrable_indicator hS
  have hDom : ∀ᵐ x : Plane ∂volume, ∀ t ∈ T, ‖D t x‖ ≤ bound x := by
    refine ae_of_all _ fun x t ht => ?_
    by_cases hx : x ∈ S
    · rw [show bound x = M from indicator_of_mem hx _]
      exact hM (t, x) ⟨ht, hx⟩
    · have he : a x = 0 := by
        by_contra h
        exact hx (subset_closure h)
      rw [show bound x = 0 from indicator_of_notMem hx _]
      simp [D, he]
  have hF (t : ℝ) : Continuous (F t) :=
    ha.mul (hf.continuous.comp (continuous_id.add continuous_const))
  have hD (t : ℝ) : Continuous (D t) :=
    ha.mul ((partial_continuous hf e).comp (continuous_id.add continuous_const))
  have hFint : Integrable (F 0) := integrate_compact_mul ha
    (hf.continuous.comp (continuous_id.add continuous_const)) hc
  have hd (x : Plane) (t : ℝ) : HasDerivAt (F · x) (D t x) t :=
    (translated_deriv hf x e t).const_mul _
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hT
    (Eventually.of_forall fun t => (hF t).aestronglyMeasurable) hFint
    (hD 0).aestronglyMeasurable hDom hBound
    (ae_of_all _ fun x t _ => hd x t)).2
  simpa only [F, D, zero_smul, add_zero] using h

private theorem derivative_of_partial {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e d x : Plane) :
    partialDerivative (partialDerivative u e) d x =
      (fderiv ℝ (fderiv ℝ u) x d) e := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  unfold partialDerivative
  rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const e)]
  simp

private theorem partial_comm {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (x e d : Plane) :
    partialDerivative (partialDerivative u e) d x =
      partialDerivative (partialDerivative u d) e x := by
  rw [derivative_of_partial hu, derivative_of_partial hu]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) d e

private theorem laplacian_as_partials {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (b : OrthonormalBasis (Fin 3) ℝ Plane) (x : Plane) :
    (Δ u) x = ∑ i, partialDerivative (partialDerivative u (b i)) (b i) x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  exact sum_congr rfl fun i _ => by
    rw [iteratedFDeriv_two_apply, derivative_of_partial hu]
    simp

private theorem inner_gradient_as_partials (u v : Plane → ℝ)
    (b : OrthonormalBasis (Fin 3) ℝ Plane) (x : Plane) :
    inner ℝ (∇ u x) (∇ v x) =
      ∑ i, partialDerivative u (b i) x * partialDerivative v (b i) x := by
  rw [← b.sum_inner_mul_inner]
  apply sum_congr rfl
  intro i _
  have h (f : Plane → ℝ) : inner ℝ (∇ f x) (b i) = partialDerivative f (b i) x := by
    rw [← toDual_apply_apply, toDual_gradient]
    rfl
  rw [h u, real_inner_comm (∇ v x) (b i), h v]

private theorem shifted_partial {g : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (s d x : Plane) :
    partialDerivative (fun y => g (y + s)) d x = partialDerivative g d (x + s) := by
  have hh := ((hg.differentiable one_ne_zero (x + s)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).add_const s)).fderiv
  change fderiv ℝ (fun y : Plane => g (y + s)) x =
    (fderiv ℝ g (x + s)).comp (ContinuousLinearMap.id ℝ Plane) at hh
  rw [ContinuousLinearMap.comp_id] at hh
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L d) hh

private theorem integrate_shifted_by_parts {g η : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (s e : Plane) :
    (∫ x, partialDerivative η e x * g (x + s)) =
      -∫ x, η x * partialDerivative g e (x + s) := by
  let g' := fun x => g (x + s)
  have hg' : ContDiff ℝ 1 g' := hg.comp (contDiff_id.add contDiff_const)
  have h1 := integrate_compact_mul hη.continuous (partial_continuous hg' e) hηc
  have h2 := integrate_compact_mul (partial_continuous hη e) hg'.continuous (partial_compact hηc e)
  have h3 := integrate_compact_mul hη.continuous hg'.continuous hηc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h2 h1 h3
    (fun x _ => hη.differentiable one_ne_zero x)
    (fun x _ => hg'.differentiable one_ne_zero x)
  change (∫ x, η x * partialDerivative g' e x) =
    -∫ x, partialDerivative η e x * g' x at h
  simp only [g', shifted_partial hg] at h ⊢
  linarith

private theorem reaction_derivative {u : Plane → ℝ} (hu : ContDiff ℝ 2 u)
    (e x : Plane) :
    partialDerivative (fun y => u y ^ 3 - u y) e x =
      (3 * (u x)^2 - 1) * partialDerivative u e x := by
  have h := (hu.differentiable (by norm_num) x).hasFDerivAt
  have he := congrArg (fun L : Plane →L[ℝ] ℝ => L e) ((h.pow 3).sub h).fderiv
  unfold partialDerivative
  simp only [sub_apply, smul_apply, smul_eq_mul] at he
  change (fderiv ℝ (fun y => u y ^ 3 - u y) x) e =
    3 • u x ^ (3 - 1) * (fderiv ℝ u x) e - (fderiv ℝ u x) e at he
  rw [he]
  norm_num
  ring

theorem weak_partial {u : Plane → ℝ} (hu : DeGiorgi.IsBoundedSolution u)
    (e : Plane) {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ x, inner ℝ (∇ (partialDerivative u e) x) (∇ η x)) +
      (∫ x, η x * ((3 * (u x)^2 - 1) * partialDerivative u e x)) = 0 := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let g (i : Fin 3) := partialDerivative u (b i)
  let a (i : Fin 3) := partialDerivative η (b i)
  let F (x : Plane) := u x ^ 3 - u x
  let W (t : ℝ) := (∑ i, ∫ x, a i x * g i (x + t • e)) + ∫ x, η x * F (x + t • e)
  have hg (i : Fin 3) : ContDiff ℝ 1 (g i) := partial_contDiff hu.regular (b i)
  have ha (i : Fin 3) : Continuous (a i) := partial_continuous hη (b i)
  have hac (i : Fin 3) : HasCompactSupport (a i) := partial_compact hηc (b i)
  have hU : ContDiff ℝ 1 u := hu.regular.of_le (by norm_num)
  have hF : ContDiff ℝ 1 F := (hU.pow 3).sub hU
  have hW : W = fun _ => 0 := by
    funext t
    have hLi (i : Fin 3) : Integrable
        (fun x => η x * partialDerivative (g i) (b i) (x + t • e)) :=
      integrate_compact_mul hη.continuous
        ((partial_continuous (hg i) (b i)).comp (continuous_id.add continuous_const)) hηc
    have hsum : (∑ i, ∫ x, a i x * g i (x + t • e)) = -(∫ x, η x * F (x + t • e)) := by
      calc
        _ = ∑ i, -(∫ x, η x * partialDerivative (g i) (b i) (x + t • e)) :=
          sum_congr rfl fun i _ => integrate_shifted_by_parts (hg i) hη hηc _ _
        _ = -(∫ x, ∑ i, η x * partialDerivative (g i) (b i) (x + t • e)) := by
          rw [sum_neg_distrib, integral_finsetSum _ (fun i _ => hLi i)]
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [] with x
          rw [← mul_sum]
          change η x * (∑ i, partialDerivative (partialDerivative u (b i)) (b i)
            (x + t • e)) = η x * F (x + t • e)
          rw [← laplacian_as_partials hu.regular b]
          congr 1
          have hpde := hu.solution (x + t • e)
          dsimp [F]
          linarith
    change (∑ i, ∫ x, a i x * g i (x + t • e)) + (∫ x, η x * F (x + t • e)) = 0
    rw [hsum, neg_add_cancel]
  have hsumdiff := HasDerivAt.fun_sum (u := (univ : Finset (Fin 3)))
    (fun i _ => shifted_integral_deriv (ha i) (hac i) (hg i) e)
  have hD : HasDerivAt W ((∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
      ∫ x, η x * partialDerivative F e x) 0 :=
    hsumdiff.add (shifted_integral_deriv hη.continuous hηc hF e)
  have hz := hD.deriv
  rw [hW, deriv_const] at hz
  calc
    _ = (∑ i, ∫ x, a i x * partialDerivative (g i) e x) +
        (∫ x, η x * partialDerivative F e x) := ?_
    _ = 0 := hz.symm
  congr 1
  · have hIi (i : Fin 3) : Integrable
        (fun x => a i x * partialDerivative (g i) e x) :=
      integrate_compact_mul (ha i) (partial_continuous (hg i) e) (hac i)
    rw [← integral_finsetSum _ (fun i _ => hIi i)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [inner_gradient_as_partials _ _ b]
    apply sum_congr rfl
    intro i _
    change partialDerivative (partialDerivative u e) (b i) x * a i x =
      a i x * partialDerivative (partialDerivative u (b i)) e x
    rw [partial_comm hu.regular, mul_comm]
  · apply integral_congr_ae
    filter_upwards [] with x
    change η x * ((3 * u x ^ 2 - 1) * partialDerivative u e x) =
      η x * partialDerivative (fun y => u y ^ 3 - u y) e x
    rw [reaction_derivative hu.regular]

private theorem gradient_product {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (x : Plane) :
    ∇ (fun y => f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  unfold gradient
  rw [fderiv_fun_mul (hf.differentiable one_ne_zero x) (hg.differentiable one_ne_zero x)]
  simp only [map_add, map_smul]

private theorem inner_gradient_integrable {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) :
    Integrable (fun x => inner ℝ (∇ f x) (∇ g x)) := by
  have hGrad {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) : Continuous (∇ h) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hh.continuous_fderiv one_ne_zero)
  apply ((hGrad hf).inner (hGrad hg)).integrable_of_hasCompactSupport
  apply hgc.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ g x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem quotient_flux {v w η : Plane → ℝ} (hv : ContDiff ℝ 1 v)
    (hw : ContDiff ℝ 1 w) (hη : ContDiff ℝ 1 η) (hne : ∀ x, v x ≠ 0) (x : Plane) :
    (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x) =
      inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
      inner ℝ (∇ v x) (∇ (fun y => w y * η y) x) := by
  let q := fun y => w y / v y
  have hq : ContDiff ℝ 1 q := hw.div hv hne
  have hqv (y : Plane) : v y * q y = w y := by
    dsimp [q]
    field_simp [hne y]
  have hwq : (fun y => v y * q y) = w := funext hqv
  have hgw := gradient_product hv hq x
  rw [hwq] at hgw
  change (v x)^2 * inner ℝ (∇ q x) (∇ η x) = _
  rw [gradient_product hv hη, gradient_product hw hη]
  simp only [inner_add_right, real_inner_smul_right]
  rw [real_inner_comm (∇ w x) (∇ v x)]
  rw [hgw]
  simp only [inner_add_left, real_inner_smul_left]
  rw [← hqv x]
  ring

set_option maxHeartbeats 600000 in
theorem solution (u : Plane → ℝ) (i : Fin 3) (hu : DeGiorgi.IsBoundedSolution u)
    (hpos : DeGiorgi.HasPositiveDeriv u) :
    let v := partialDerivative u (EuclideanSpace.single 0 1)
    let w := partialDerivative u (EuclideanSpace.single i 1)
    ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x)^2 * inner ℝ (∇ (fun y => w y / v y) x) (∇ η x)) = 0 := by
  intro v w η hη hηc
  have hv : ContDiff ℝ 1 v := partial_contDiff hu.regular _
  have hw : ContDiff ℝ 1 w := partial_contDiff hu.regular _
  have hv0 (x : Plane) : v x ≠ 0 := by
    have h := hpos x
    rw [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
    exact h.ne'
  have hvη : ContDiff ℝ 1 (fun x => v x * η x) := hv.mul hη
  have hwη : ContDiff ℝ 1 (fun x => w x * η x) := hw.mul hη
  have hvηc : HasCompactSupport (fun x => v x * η x) := hηc.mul_left (f := v)
  have hwηc : HasCompactSupport (fun x => w x * η x) := hηc.mul_left (f := w)
  have hweakW := weak_partial hu (EuclideanSpace.single i 1) hvη hvηc
  have hweakV := weak_partial hu (EuclideanSpace.single 0 1) hwη hwηc
  let reaction := fun x => 3 * (u x)^2 - 1
  have hcancel : (∫ x, (v x * η x) * (reaction x * w x)) =
      (∫ x, (w x * η x) * (reaction x * v x)) :=
    integral_congr_ae (ae_of_all _ fun x => by ring)
  change (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) +
    (∫ x, (v x * η x) * (reaction x * w x)) = 0 at hweakW
  change (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) +
    (∫ x, (w x * η x) * (reaction x * v x)) = 0 at hweakV
  have hdiff : (∫ x, inner ℝ (∇ w x) (∇ (fun y => v y * η y) x)) =
      (∫ x, inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) := by
    rw [hcancel] at hweakW
    linarith
  calc
    _ = ∫ x, (inner ℝ (∇ w x) (∇ (fun y => v y * η y) x) -
        inner ℝ (∇ v x) (∇ (fun y => w y * η y) x)) :=
      integral_congr_ae (ae_of_all _ (quotient_flux hv hw hη hv0))
    _ = 0 := by
      rw [integral_sub (inner_gradient_integrable hw hvη hvηc)
        (inner_gradient_integrable hv hwη hwηc), hdiff, sub_self]

end OMA.DeGiorgiWeak3

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Metric Set Filter
open scoped Gradient

private abbrev Plane := ℝ^3

private theorem gradient_continuous {u : Plane → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (∇ u) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hu.continuous_fderiv one_ne_zero)

private theorem gradient_compact {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (∇ u) := by
  apply hu.mono'
  intro x hx
  apply support_fderiv_subset ℝ
  change fderiv ℝ u x ≠ 0
  intro he
  exact hx (by simp [gradient, he])

private theorem norm_gradient {u : Plane → ℝ} (x : Plane) :
    ‖∇ u x‖ = ‖fderiv ℝ u x‖ :=
  (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

private noncomputable def baseBump : ContDiffBump (0 : Plane) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private noncomputable def cutoff (r : ℝ) (x : Plane) : ℝ := baseBump (r⁻¹ • x)

private theorem cutoff_smooth (r : ℝ) : ContDiff ℝ 1 (cutoff r) := by
  have h : ContDiff ℝ 1 (fun x : Plane => r⁻¹ • x) := contDiff_id.const_smul _
  exact baseBump.contDiff.comp h

private theorem cutoff_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (cutoff r) :=
  baseBump.hasCompactSupport.comp_smul (inv_ne_zero hr.ne')

private theorem cutoff_bounds (r : ℝ) (x : Plane) : 0 ≤ cutoff r x ∧ cutoff r x ≤ 1 :=
  ⟨baseBump.nonneg, baseBump.le_one⟩

private theorem cutoff_one {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∈ closedBall (0 : Plane) r) : cutoff r x = 1 := by
  apply baseBump.one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, div_le_iff₀ hr, show baseBump.rIn = 1 from rfl, one_mul]
  exact mem_closedBall_zero_iff.mp hx

private theorem cutoff_zero {r : ℝ} (hr : 0 < r) {x : Plane}
    (hx : x ∉ closedBall (0 : Plane) (2 * r)) : cutoff r x = 0 := by
  apply baseBump.zero_of_le_dist
  change 2 ≤ dist (r⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_eq_div, le_div_iff₀ hr]
  exact le_of_lt (lt_of_not_ge (fun he => hx (mem_closedBall_zero_iff.mpr he)))

private theorem gradient_zero_of_cutoff_zero {r : ℝ} {x : Plane} (h : cutoff r x = 0) :
    ∇ (cutoff r) x = 0 := by
  have hmin : IsLocalMin (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).1
  simp [gradient, hmin.fderiv_eq_zero]

private theorem gradient_zero_of_cutoff_one {r : ℝ} {x : Plane} (h : cutoff r x = 1) :
    ∇ (cutoff r) x = 0 := by
  have hmax : IsLocalMax (cutoff r) x :=
    Eventually.of_forall fun y => by rw [h]; exact (cutoff_bounds r y).2
  simp [gradient, hmax.fderiv_eq_zero]

private theorem cutoff_fderiv (r : ℝ) (x : Plane) :
    fderiv ℝ (cutoff r) x =
      (fderiv ℝ (fun y : Plane => baseBump y) (r⁻¹ • x)).comp
        (r⁻¹ • ContinuousLinearMap.id ℝ Plane) := by
  let L : Plane →L[ℝ] Plane := r⁻¹ • ContinuousLinearMap.id ℝ Plane
  have hdiff : Differentiable ℝ (fun y : Plane => baseBump y) :=
    (baseBump.contDiff (n := 1)).differentiable (by norm_num)
  exact ((hdiff (L x)).hasFDerivAt.comp x L.hasFDerivAt).fderiv

private theorem cutoff_gradient_norm {r : ℝ} (hr : 0 < r) (M : ℝ)
    (hM : ∀ x : Plane, ‖fderiv ℝ (fun y : Plane => baseBump y) x‖ ≤ M)
    (x : Plane) : ‖∇ (cutoff r) x‖ ≤ M / r := by
  rw [norm_gradient, cutoff_fderiv]
  apply ContinuousLinearMap.opNorm_comp_le _ _ |>.trans
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ContinuousLinearMap.norm_id, mul_one,
    div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hM _) (inv_nonneg.mpr hr.le)

private theorem compact_gradient_square {u : Plane → ℝ} (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => ‖∇ u x‖ ^ 2) := by
  apply (gradient_compact hu).mono'
  intro x hx
  apply subset_closure
  change ∇ u x ≠ 0
  intro he
  exact hx (by simp [he])

private theorem cutoff_weighted_bound (f : Plane → ℝ) (hf : Continuous f) (C₀ : ℝ)
    (hgrow : ∀ R : ℝ, 1 ≤ R → (∫ x in ball (0 : Plane) R, (f x) ^ 2) ≤ C₀ * R ^ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : ℝ, 1 ≤ r → (∫ x, (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) ≤ K := by
  obtain ⟨M, hM⟩ := (baseBump.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((baseBump.contDiff (n := 1)).continuous_fderiv one_ne_zero)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hC0 : 0 ≤ C₀ := by
    have h := hgrow 1 le_rfl
    have h0 : 0 ≤ ∫ x in ball (0 : Plane) 1, (f x) ^ 2 :=
      setIntegral_nonneg measurableSet_ball (fun x _ => sq_nonneg _)
    nlinarith
  refine ⟨9 * C₀ * M ^ 2, by positivity, ?_⟩
  intro r hr
  have hr0 : 0 < r := by linarith
  have hcompact : HasCompactSupport (fun x => (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) :=
    (compact_gradient_square (cutoff_compact hr0)).mul_left
  have hcont : Continuous (fun x => (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2) :=
    (hf.pow 2).mul ((gradient_continuous (cutoff_smooth r)).norm.pow 2)
  have hInt := hcont.integrable_of_hasCompactSupport (μ := volume) hcompact
  have hfi : IntegrableOn (fun x => (f x) ^ 2) (ball (0 : Plane) (3 * r)) :=
    ((hf.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) (3 * r))).mono_set
      ball_subset_closedBall
  calc
    _ = ∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2 * ‖∇ (cutoff r) x‖ ^ 2 := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have hx' : x ∉ closedBall (0 : Plane) (2 * r) := by
        intro h
        apply hx
        rw [mem_ball_zero_iff]
        rw [mem_closedBall_zero_iff] at h
        linarith
      rw [gradient_zero_of_cutoff_zero (cutoff_zero hr0 hx')]
      simp
    _ ≤ ∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2 * (M / r) ^ 2 := by
      apply setIntegral_mono_on hInt.integrableOn (hfi.mul_const _) measurableSet_ball
      intro x _
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (cutoff_gradient_norm hr0 M hM x) 2) (sq_nonneg _)
    _ = (∫ x in ball (0 : Plane) (3 * r), (f x) ^ 2) * (M / r) ^ 2 := integral_mul_const _ _
    _ ≤ (C₀ * (3 * r) ^ 2) * (M / r) ^ 2 :=
      mul_le_mul_of_nonneg_right (hgrow _ (by linarith)) (sq_nonneg _)
    _ = 9 * C₀ * M ^ 2 := by field_simp; ring

end OMA.SpaceLiouville

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Filter Set Metric
open scoped Gradient

private noncomputable def energy (v q : Plane → ℝ) (x : Plane) : ℝ :=
  (v x) ^ 2 * ‖∇ q x‖ ^ 2

private theorem energy_continuous {v q : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) : Continuous (energy v q) :=
  (hv.continuous.pow 2).mul ((gradient_continuous hq).norm.pow 2)

private theorem energy_nonneg (v q : Plane → ℝ) (x : Plane) : 0 ≤ energy v q x := by
  unfold energy
  positivity

private theorem energy_cutoff_integrable {v q η : Plane → ℝ}
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hs : HasCompactSupport η) : Integrable (fun x => (η x) ^ 2 * energy v q x) := by
  have hx : HasCompactSupport (fun x => (η x) ^ 2 * energy v q x) := by
    apply hs.mono'
    intro x h
    apply subset_closure
    change η x ≠ 0
    intro he
    exact h (by simp [he])
  exact ((hη.continuous.pow 2).mul (energy_continuous hv hq)).integrable_of_hasCompactSupport hx

private theorem young {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    2 * a * b ≤ δ * a ^ 2 + b ^ 2 / δ := by
  apply sub_nonneg.mp
  have he : δ * a ^ 2 + b ^ 2 / δ - 2 * a * b = (δ * a - b) ^ 2 / δ := by
    field_simp [hδ.ne']
    ring
  rw [he]
  exact div_nonneg (sq_nonneg _) hδ.le

private theorem test_gradient {q η : Plane → ℝ} (hq : ContDiff ℝ 1 q)
    (hη : ContDiff ℝ 1 η) (x : Plane) :
    ∇ (fun y => q y * (η y) ^ 2) x =
      (η x) ^ 2 • ∇ q x + (2 * q x * η x) • ∇ η x := by
  have hqd := (hq.differentiable one_ne_zero x)
  have hηd := (hη.differentiable one_ne_zero x)
  have hm := fderiv_fun_mul (c := q) (d := fun y => (η y) ^ 2) hqd (hηd.pow 2)
  have hp := fderiv_fun_pow 2 hηd
  unfold gradient
  rw [hm, hp]
  simp only [map_add, map_smul, show 2 - (1 : ℕ) = 1 by decide, pow_one, nsmul_eq_mul,
    Nat.cast_ofNat, smul_smul]
  rw [add_comm]
  congr 1
  congr 1
  ring

private theorem weak_energy_estimate (v q η A : Plane → ℝ) (δ : ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hη : ContDiff ℝ 1 η)
    (hηc : HasCompactSupport η) (hvpos : ∀ x, 0 < v x)
    (hη0 : ∀ x, 0 ≤ η x) (hδ : 0 < δ)
    (hweak : ∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)) = 0)
    (hAi : Integrable A) (hA0 : ∀ x, 0 ≤ A x)
    (hA : ∀ x, ∇ η x ≠ 0 → (η x) ^ 2 * energy v q x ≤ A x) :
    (∫ x, (η x) ^ 2 * energy v q x) ≤
      δ * (∫ x, A x) + (1 / δ) * (∫ x, (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
  let ψ := fun x => q x * (η x) ^ 2
  have hψ : ContDiff ℝ 1 ψ := hq.mul (hη.pow 2)
  have hψc : HasCompactSupport ψ := by
    apply hηc.mono'
    intro x hx
    apply subset_closure
    change η x ≠ 0
    intro he
    exact hx (by simp [ψ, he])
  let F := fun x => (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x)
  have hFc : HasCompactSupport F := by
    apply (gradient_compact hψc).mono'
    intro x hx
    apply subset_closure
    change ∇ ψ x ≠ 0
    intro he
    apply hx
    change (v x) ^ 2 * inner ℝ (∇ q x) (∇ ψ x) = 0
    rw [he, inner_zero_right, mul_zero]
  have hFi : Integrable F :=
    ((hv.continuous.pow 2).mul
      ((gradient_continuous hq).inner (gradient_continuous hψ))).integrable_of_hasCompactSupport hFc
  have hFzero : (∫ x, F x) = 0 := hweak ψ hψ hψc
  have hGi : Integrable (fun x => (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) :=
    (((hv.continuous.mul hq.continuous).pow 2).mul
      ((gradient_continuous hη).norm.pow 2)).integrable_of_hasCompactSupport
      (compact_gradient_square hηc).mul_left
  have hCross (x : Plane) :
      F x = (η x) ^ 2 * energy v q x +
        2 * (η x) * (v x) ^ 2 * (q x) * inner ℝ (∇ q x) (∇ η x) := by
    simp only [F, ψ, test_gradient hq hη, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, energy]
    ring
  have hpoint (x : Plane) :
      (η x) ^ 2 * energy v q x ≤ F x + δ * A x + (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
    rw [hCross]
    by_cases hz : ∇ η x = 0
    · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), inner_zero_right, mul_zero,
        add_zero]
      exact le_add_of_nonneg_right (mul_nonneg hδ.le (hA0 x))
    have hb : -(v x * q x * inner ℝ (∇ q x) (∇ η x)) ≤
        |v x * q x| * (‖∇ q x‖ * ‖∇ η x‖) := by
      calc
        _ ≤ |v x * q x * inner ℝ (∇ q x) (∇ η x)| := neg_le_abs _
        _ = |v x * q x| * |inner ℝ (∇ q x) (∇ η x)| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    have hxb := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * η x * v x by
      exact mul_nonneg (mul_nonneg (by norm_num) (hη0 x)) (hvpos x).le)
    have hxy := young hδ (η x * v x * ‖∇ q x‖) (|v x * q x| * ‖∇ η x‖)
    rw [show (|v x * q x| * ‖∇ η x‖) ^ 2 = (v x * q x) ^ 2 * ‖∇ η x‖ ^ 2 by
      rw [mul_pow, sq_abs]] at hxy
    have hxa := mul_le_mul_of_nonneg_left (hA x hz) hδ.le
    unfold energy at hxa
    simp only [div_eq_mul_inv] at hxy ⊢
    nlinarith only [hxb, hxy, hxa]
  have hi := integral_mono (energy_cutoff_integrable hv hq hη hηc)
    ((hFi.add (hAi.const_mul δ)).add (hGi.const_mul (1 / δ))) hpoint
  simp only [Pi.add_apply] at hi
  have hsum1 : (∫ x, F x + δ * A x) = (∫ x, F x) + ∫ x, δ * A x :=
    integral_add hFi (hAi.const_mul δ)
  have hsum2 : (∫ x, F x + δ * A x + (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2)) =
      (∫ x, F x + δ * A x) + ∫ x, (1 / δ) * ((v x * q x) ^ 2 * ‖∇ η x‖ ^ 2) := by
    simpa only [Pi.add_apply] using
      integral_add (hFi.add (hAi.const_mul δ)) (hGi.const_mul (1 / δ))
  rw [hsum2, hsum1, hFzero, zero_add, integral_const_mul, integral_const_mul] at hi
  exact hi

end OMA.SpaceLiouville

namespace OMA.SpaceLiouville

open EuclideanGeometry InnerProductSpace MeasureTheory Metric Set Filter
open scoped Gradient Topology

theorem constant_of_weak_divergence (v q : Plane → ℝ)
    (hv : ContDiff ℝ 1 v) (hq : ContDiff ℝ 1 q) (hvpos : ∀ x, 0 < v x)
    (hb : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
      (∫ x in Metric.ball (0 : Plane) R, (v x * q x) ^ 2) ≤ C * R ^ 2)
    (hweak : ∀ η : Plane → ℝ, ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x, (v x) ^ 2 * inner ℝ (∇ q x) (∇ η x)) = 0) :
    ∃ c : ℝ, ∀ x, q x = c := by
  classical
  obtain ⟨C, hC⟩ := hb
  obtain ⟨K, hK0, hCut⟩ := cutoff_weighted_bound (fun x => v x * q x)
    (hv.continuous.mul hq.continuous) C hC
  let E := energy v q
  let r := fun m : ℕ => (m : ℝ) + 1
  let S := fun m => closedBall (0 : Plane) (r m)
  let W := fun m x => (cutoff (r m) x) ^ 2 * E x
  have hp (m : ℕ) : 0 < r m := by dsimp [r]; positivity
  have hp1 (m : ℕ) : 1 ≤ r m := by dsimp [r]; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  have hS (m : ℕ) : MeasurableSet (S m) := measurableSet_closedBall
  have hEc : Continuous E := energy_continuous hv hq
  have hE0 (x : Plane) : 0 ≤ E x := energy_nonneg _ _ _
  have hWi (m : ℕ) : Integrable (W m) :=
    energy_cutoff_integrable hv hq (cutoff_smooth _) (cutoff_compact (hp m))
  have hW0 (m : ℕ) (x : Plane) : 0 ≤ W m x :=
    mul_nonneg (sq_nonneg _) (hE0 x)
  have hLocal (m : ℕ) : (∫ x in S m, E x) ≤ ∫ x, W m x := by
    calc
      _ = ∫ x in S m, W m x := by
        apply setIntegral_congr_fun (hS m)
        intro x hx
        change E x = (cutoff (r m) x) ^ 2 * E x
        rw [cutoff_one (hp m) hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_le_integral (hWi _) (ae_of_all _ (hW0 _))
  have hBound (m : ℕ) : (∫ x in S m, E x) ≤ 4 * K := by
    have h1 := weak_energy_estimate v q (cutoff (r m)) (W m) (1 / 2)
      hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
      (fun x => (cutoff_bounds _ x).1) (by norm_num) hweak (hWi m) (hW0 m) (by simp [W, E])
    change (∫ x, W m x) ≤ (1 / 2) * (∫ x, W m x) +
      (1 / (1 / 2)) * (∫ x, (v x * q x) ^ 2 * ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
    have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp1 m))
      (by positivity : (0 : ℝ) ≤ 1 / (1 / 2))
    linarith [hLocal m]
  have hrTop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hCover : AECover (volume : Measure Plane) atTop S := aecover_closedBall hrTop
  have hEi : Integrable E := hCover.integrable_of_integral_bounded_of_nonneg_ae
    (4 * K)
    (fun m => hEc.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
    (ae_of_all _ hE0) (Eventually.of_forall hBound)
  let I := ∫ x, E x
  have hLimit : Tendsto (fun m : ℕ => ∫ x in S m, E x) atTop (𝓝 I) :=
    hCover.integral_tendsto_of_countably_generated hEi
  have hTail : Tendsto (fun m : ℕ => ∫ x in (S m)ᶜ, E x) atTop (𝓝 (0 : ℝ)) := by
    have hsub : Tendsto (fun m : ℕ => I - ∫ x in S m, E x) atTop (𝓝 (I - I)) :=
      tendsto_const_nhds.sub hLimit
    rw [sub_self] at hsub
    exact hsub.congr fun m => (setIntegral_compl (hS m) hEi).symm
  have hBig (δ : ℝ) (hδ : 0 < δ) : I ≤ (1 / δ) * K := by
    have hEst (m : ℕ) : (∫ x in S m, E x) ≤
        δ * (∫ x in (S m)ᶜ, E x) + (1 / δ) * K := by
      let A := (S m)ᶜ.indicator E
      have hAi : Integrable A := hEi.indicator (hS m).compl
      have hA0 (x : Plane) : 0 ≤ A x := by
        by_cases hx : x ∈ (S m)ᶜ
        · rw [show A x = E x from indicator_of_mem hx _]
          exact hE0 x
        · rw [show A x = 0 from indicator_of_notMem hx _]
      have hDom (x : Plane) (hx : ∇ (cutoff (r m)) x ≠ 0) : W m x ≤ A x := by
        have hxS : x ∈ (S m)ᶜ := fun h =>
          hx (gradient_zero_of_cutoff_one (cutoff_one (hp m) h))
        rw [show A x = E x from indicator_of_mem hxS _]
        change (cutoff (r m) x) ^ 2 * E x ≤ E x
        have hη := cutoff_bounds (r m) x
        exact mul_le_of_le_one_left (hE0 x) (pow_le_one₀ hη.1 hη.2)
      have h1 := weak_energy_estimate v q (cutoff (r m)) A δ
        hv hq (cutoff_smooth _) (cutoff_compact (hp m)) hvpos
        (fun x => (cutoff_bounds _ x).1) hδ hweak hAi hA0 hDom
      change (∫ x, W m x) ≤ δ * (∫ x, A x) +
        (1 / δ) * (∫ x, (v x * q x) ^ 2 * ‖∇ (cutoff (r m)) x‖ ^ 2) at h1
      rw [show (∫ x, A x) = ∫ x in (S m)ᶜ, E x from integral_indicator (hS m).compl] at h1
      have h2 := mul_le_mul_of_nonneg_left (hCut (r m) (hp1 m))
        (by positivity : 0 ≤ 1 / δ)
      linarith [hLocal m]
    have hright : Tendsto (fun m => δ * (∫ x in (S m)ᶜ, E x) + (1 / δ) * K)
        atTop (𝓝 ((1 / δ) * K)) := by
      simpa only [mul_zero, zero_add] using (tendsto_const_nhds.mul hTail).add
        (tendsto_const_nhds (x := (1 / δ) * K))
    exact le_of_tendsto_of_tendsto hLimit hright (Eventually.of_forall hEst)
  have hI : I = 0 := by
    have hI0 : 0 ≤ I := integral_nonneg hE0
    by_contra h
    have hIp : 0 < I := lt_of_le_of_ne hI0 (fun h0 => h h0.symm)
    let δ := (K + 1) / I
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have h1 := hBig δ hδ
    have h2 : I * δ ≤ K := (le_div_iff₀ hδ).mp (by
      simpa only [div_mul_eq_mul_div, one_mul] using h1)
    have hd : I * δ = K + 1 := by dsimp [δ]; field_simp [hIp.ne']
    linarith
  have hAE : E =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hE0 hEi).mp hI
  have hzero : E = 0 := (hEc.ae_eq_iff_eq volume continuous_zero).mp hAE
  have hfzero (x : Plane) : fderiv ℝ q x = 0 := by
    have hx := congrFun hzero x
    change (v x) ^ 2 * ‖∇ q x‖ ^ 2 = 0 at hx
    have hy : ‖∇ q x‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hx).resolve_left (pow_ne_zero _ (hvpos x).ne')
    have hnorm : ‖∇ q x‖ = 0 := by
      by_contra h
      exact (pow_ne_zero _ h) hy
    have hg : ∇ q x = 0 := norm_eq_zero.mp hnorm
    rw [← toDual_gradient, hg, map_zero]
  exact ⟨q 0, fun x => is_const_of_fderiv_eq_zero (hq.differentiable one_ne_zero) hfzero x 0⟩

end OMA.SpaceLiouville


namespace OMA.DeGiorgiC

section Core
open InnerProductSpace MeasureTheory Filter Set Metric
open scoped Topology Laplacian Gradient

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev Plane2 := EuclideanSpace ℝ (Fin 2)

structure IsBoundedSol (u : Space → ℝ) : Prop where
  regular : ContDiff ℝ 2 u
  bounded : ∃ C, ∀ x, |u x| ≤ C
  solution : ∀ x, (Δ u x) + u x - (u x) ^ 3 = 0

noncomputable def e3 (i : Fin 3) : Space := EuclideanSpace.single i 1
noncomputable def e2 (i : Fin 2) : Plane2 := EuclideanSpace.single i 1

noncomputable def pd3 (f : Space → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ f x (e3 i)

noncomputable def pd2 (f : Plane2 → ℝ) (i : Fin 2) (y : Plane2) : ℝ :=
  fderiv ℝ f y (e2 i)

noncomputable def pd32 (f : Space → ℝ) (i j : Fin 3) (x : Space) : ℝ :=
  pd3 (pd3 f i) j x

noncomputable def pd22 (f : Plane2 → ℝ) (i j : Fin 2) (y : Plane2) : ℝ :=
  pd2 (pd2 f i) j y

noncomputable def mk3 (t : ℝ) (y : Plane2) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![t, y 0, y 1]

noncomputable def mk2 (s t : ℝ) : Plane2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![s, t]

noncomputable def proj2 (x : Space) : Plane2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 1, x 2]

def Q3 (R : ℝ) : Set Space := {x : Space | ∀ i : Fin 3, x i ∈ Icc (-R) R}
def Q2 (R : ℝ) : Set Plane2 := {y : Plane2 | ∀ i : Fin 2, y i ∈ Icc (-R) R}

noncomputable def Wpot (s : ℝ) : ℝ := (1 - s ^ 2) ^ 2 / 4

noncomputable def e3_en (f : Space → ℝ) (x : Space) : ℝ :=
  (1 / 2) * (∑ i : Fin 3, (pd3 f i x) ^ 2) + Wpot (f x)

noncomputable def e2_en (f : Plane2 → ℝ) (y : Plane2) : ℝ :=
  (1 / 2) * (∑ i : Fin 2, (pd2 f i y) ^ 2) + Wpot (f y)

noncomputable def K_sz (f : Plane2 → ℝ) (y : Plane2) : ℝ :=
  (pd2 f 0 y * pd22 f 1 0 y - pd2 f 1 y * pd22 f 0 0 y) ^ 2 +
  (pd2 f 0 y * pd22 f 1 1 y - pd2 f 1 y * pd22 f 0 1 y) ^ 2

private theorem mk2_0 (s t : ℝ) : (mk2 s t) 0 = s := rfl
private theorem mk2_1 (s t : ℝ) : (mk2 s t) 1 = t := rfl

private theorem mk2_add_e0 (s h t : ℝ) : mk2 s t + h • e2 0 = mk2 (s + h) t := by
  ext i; fin_cases i <;> simp [mk2, e2]

private theorem mk2_add_e1 (s t h : ℝ) : mk2 s t + h • e2 1 = mk2 s (t + h) := by
  ext i; fin_cases i <;> simp [mk2, e2]

private theorem mk2_eta (q : Plane2) : mk2 (q 0) (q 1) = q := by
  ext i; fin_cases i <;> simp [mk2]

private theorem mk3_coord (t : ℝ) (y : Plane2) :
    (mk3 t y) 0 = t ∧ (mk3 t y) 1 = y 0 ∧ (mk3 t y) 2 = y 1 := by
  simp [mk3]

private theorem proj2_coord (x : Space) :
    (proj2 x) 0 = x 1 ∧ (proj2 x) 1 = x 2 := by
  simp [proj2]

private theorem mk3_proj2 (x : Space) : mk3 (x 0) (proj2 x) = x := by
  ext i; fin_cases i <;> simp [mk3, proj2]

private theorem proj2_mk3 (t : ℝ) (y : Plane2) : proj2 (mk3 t y) = y := by
  ext i; fin_cases i <;> simp [mk3, proj2]

private theorem mk3_add_e0 (t s : ℝ) (y : Plane2) : mk3 t y + s • e3 0 = mk3 (t + s) y := by
  ext i; fin_cases i <;> simp [mk3, e3]

private theorem mk3_add_e2 (t s : ℝ) (y : Plane2) (i : Fin 2) :
    mk3 t (y + s • e2 i) = mk3 t y + s • e3 i.succ := by
  ext j; fin_cases i <;> fin_cases j <;> simp [mk3, e2, e3]

private theorem line_deriv3 {u : Space → ℝ} (hu : ContDiff ℝ 1 u) (x d : Space) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (x + s • d)) (fderiv ℝ u (x + t • d) d) t :=
  (hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const d).const_add x))

private theorem line_deriv2 {f : Plane2 → ℝ} (hf : ContDiff ℝ 1 f) (y d : Plane2) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • d)) (fderiv ℝ f (y + t • d) d) t :=
  (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t
    (by simpa using (((hasDerivAt_id t).smul_const d).const_add y))

private theorem isCompact_Q3 (R : ℝ) : IsCompact (Q3 R) := by
  have h1 : Q3 R = (EuclideanSpace.equiv (Fin 3) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 3 => Icc (-R) R) := by
    ext x; constructor
    · intro hx; exact ⟨fun i => x i, fun i _ => hx i, by ext i; simp⟩
    · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
  rw [h1]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous

private theorem isCompact_Q2 (R : ℝ) : IsCompact (Q2 R) := by
  have h1 : Q2 R = (EuclideanSpace.equiv (Fin 2) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 2 => Icc (-R) R) := by
    ext y; constructor
    · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
    · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
  rw [h1]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous

private theorem measurableSet_Q2 (R : ℝ) : MeasurableSet (Q2 R) :=
  (isCompact_Q2 R).isClosed.measurableSet

private theorem volume_Q2 {R : ℝ} (hR : 0 ≤ R) :
    volume (Q2 R) = ENNReal.ofReal ((2 * R) ^ 2) := by
  have hmp := PiLp.volume_preserving_toLp (Fin 2)
  have hpre : (WithLp.toLp 2 : (Fin 2 → ℝ) → Plane2) ⁻¹' Q2 R =
      Set.pi Set.univ (fun _ : Fin 2 => Icc (-R) R) := by
    ext f; constructor
    · intro h i _; exact h i
    · intro h i; exact h i (Set.mem_univ i)
  rw [← hmp.measure_preimage (measurableSet_Q2 R).nullMeasurableSet, hpre,
    volume_pi_pi (fun _ : Fin 2 => Icc (-R) R)]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]; congr 2; ring

private theorem contDiff_proj2 : ContDiff ℝ 1 proj2 := by
  let L : Space →L[ℝ] Plane2 :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).smulRight (e2 0)) +
    ((EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).smulRight (e2 1))
  have hL : (L : Space → Plane2) = proj2 := by ext x i; fin_cases i <;> simp [L, proj2, e2]
  rw [← hL]; exact L.contDiff

private theorem inner_grad3_pts (f g : Space → ℝ) (x y : Space) :
    inner ℝ (∇ f x) (∇ g y) = ∑ i : Fin 3, pd3 f i x * pd3 g i y := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl; intro i _
  have hb : b i = e3 i := by ext j; simp [b, e3, EuclideanSpace.basisFun_apply]
  have hf (h : Space → ℝ) (z : Space) : inner ℝ (∇ h z) (b i) = pd3 h i z := by
    rw [← toDual_apply_apply, toDual_gradient, hb]; rfl
  rw [hf f x, real_inner_comm (∇ g y) (b i), hf g y]

private theorem inner_grad3_eq (f g : Space → ℝ) (x : Space) :
    inner ℝ (∇ f x) (∇ g x) = ∑ i : Fin 3, pd3 f i x * pd3 g i x :=
  inner_grad3_pts f g x x

private theorem norm_grad3_sq (f : Space → ℝ) (x : Space) :
    ‖∇ f x‖ ^ 2 = ∑ i : Fin 3, (pd3 f i x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_grad3_eq]
  apply Finset.sum_congr rfl; intro i _; ring

private theorem inner_grad2_eq (f g : Plane2 → ℝ) (y : Plane2) :
    inner ℝ (∇ f y) (∇ g y) = ∑ i : Fin 2, pd2 f i y * pd2 g i y := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  rw [← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl; intro i _
  have hb : b i = e2 i := by ext j; simp [b, e2, EuclideanSpace.basisFun_apply]
  have hf (h : Plane2 → ℝ) : inner ℝ (∇ h y) (b i) = pd2 h i y := by
    rw [← toDual_apply_apply, toDual_gradient, hb]; rfl
  rw [hf f, real_inner_comm (∇ g y) (b i), hf g]

private theorem norm_grad2_sq (f : Plane2 → ℝ) (y : Plane2) :
    ‖∇ f y‖ ^ 2 = ∑ i : Fin 2, (pd2 f i y) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_grad2_eq]
  apply Finset.sum_congr rfl; intro i _; ring

private theorem hasDerivAt_glue {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c = g c) :
    HasDerivAt (fun s : ℝ => if s ≤ c then f s else g s) d c := by
  rw [hasDerivAt_iff_tendsto_slope_zero, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ1, hδ1, hf_b⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hasDerivAt_iff_tendsto_slope_zero.mp hf) ε hε
  obtain ⟨δ2, hδ2, hg_b⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hasDerivAt_iff_tendsto_slope_zero.mp hg) ε hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun h hh_ne hh_lt => ?_⟩
  simp only [le_refl, ↓reduceIte]
  by_cases hle : c + h ≤ c
  · simp only [hle, ↓reduceIte]; exact hf_b hh_ne (lt_of_lt_of_le hh_lt (min_le_left _ _))
  · simp only [hle, ↓reduceIte, hfg]; exact hg_b hh_ne (lt_of_lt_of_le hh_lt (min_le_right _ _))

private theorem continuousAt_glue {f g : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c) (hfg : f c = g c) :
    ContinuousAt (fun s : ℝ => if s ≤ c then f s else g s) c := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ1, hδ1, hf_b⟩ := Metric.continuousAt_iff.mp hf ε hε
  obtain ⟨δ2, hδ2, hg_b⟩ := Metric.continuousAt_iff.mp hg ε hε
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs => ?_⟩
  simp only [le_refl, ↓reduceIte]
  by_cases hle : s ≤ c
  · simp only [hle, ↓reduceIte]; exact hf_b (lt_of_lt_of_le hs (min_le_left _ _))
  · simp only [hle, ↓reduceIte, hfg]; exact hg_b (lt_of_lt_of_le hs (min_le_right _ _))

private noncomputable def hermite (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then 3 * t ^ 2 - 2 * t ^ 3 else 1

private noncomputable def hermite' (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then 6 * t - 6 * t ^ 2 else 0

private theorem hermite_bounds (t : ℝ) : 0 ≤ hermite t ∧ hermite t ≤ 1 := by
  unfold hermite; split_ifs with h0 h1
  · exact ⟨le_rfl, zero_le_one⟩
  · push Not at h0
    refine ⟨by nlinarith [sq_nonneg t], ?_⟩
    have : 1 - (3 * t ^ 2 - 2 * t ^ 3) = (1 - t) ^ 2 * (1 + 2 * t) := by ring
    nlinarith [sq_nonneg (1 - t)]
  · exact ⟨zero_le_one, le_rfl⟩

private theorem hermite'_abs_le (t : ℝ) : |hermite' t| ≤ 3 / 2 := by
  unfold hermite'; split_ifs with h0 h1
  · norm_num
  · push Not at h0; rw [abs_le]; exact ⟨by nlinarith, by nlinarith [sq_nonneg (t - 1 / 2)]⟩
  · norm_num

private theorem hermite_zero_of_le {t : ℝ} (ht : t ≤ 0) : hermite t = 0 := by
  unfold hermite; simp [ht]

private theorem hermite_one_of_ge {t : ℝ} (ht : 1 ≤ t) : hermite t = 1 := by
  unfold hermite; by_cases h1 : t = 1
  · subst h1; norm_num
  · rw [if_neg (by linarith), if_neg (by linarith [lt_of_le_of_ne ht (Ne.symm h1)])]

private theorem hermite'_zero_of_le {t : ℝ} (ht : t ≤ 0) : hermite' t = 0 := by
  unfold hermite'; simp [ht]

private theorem hasDerivAt_hermite (t : ℝ) : HasDerivAt hermite (hermite' t) t := by
  have hp (s : ℝ) : HasDerivAt (fun x : ℝ => 3 * x ^ 2 - 2 * x ^ 3) (6 * s - 6 * s ^ 2) s :=
    (((hasDerivAt_pow 2 s).const_mul (3 : ℝ)).fun_sub
      ((hasDerivAt_pow 3 s).const_mul (2 : ℝ))).congr_deriv (by norm_num; ring)
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · have hev : hermite =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [gt_mem_nhds ht0] with s hs; exact hermite_zero_of_le hs.le
    simpa [hermite', ht0.le] using (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · have hev : hermite =ᶠ[𝓝 (0 : ℝ)] fun s => if s ≤ 0 then 0 else 3 * s ^ 2 - 2 * s ^ 3 := by
      filter_upwards [gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
      unfold hermite; split_ifs with h0 h1 <;> first | rfl | linarith
    have hg := hasDerivAt_glue (c := (0 : ℝ)) (d := (0 : ℝ))
      (hasDerivAt_const 0 0) (by simpa using hp 0) (by norm_num)
    simpa [hermite'] using hg.congr_of_eventuallyEq hev
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · have hev : hermite =ᶠ[𝓝 t] fun s => 3 * s ^ 2 - 2 * s ^ 3 := by
        filter_upwards [(lt_mem_nhds ht0).and (gt_mem_nhds ht1)] with s ⟨hs0, hs1⟩
        unfold hermite; rw [if_neg (not_le.mpr hs0), if_pos hs1.le]
      simpa [hermite', not_le.mpr ht0, ht1.le] using (hp t).congr_of_eventuallyEq hev
    · have hev : hermite =ᶠ[𝓝 (1 : ℝ)] fun s => if s ≤ 1 then 3 * s ^ 2 - 2 * s ^ 3 else 1 := by
        filter_upwards [lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
        unfold hermite; rw [if_neg (not_le.mpr hs)]
      have hg := hasDerivAt_glue (c := (1 : ℝ)) (d := (0 : ℝ))
        (by simpa using hp 1) (hasDerivAt_const 1 1) (by norm_num)
      simpa [hermite'] using hg.congr_of_eventuallyEq hev
    · have hev : hermite =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
        filter_upwards [lt_mem_nhds ht1] with s hs; exact hermite_one_of_ge hs.le
      simpa [hermite', not_le.mpr ht0, not_le.mpr ht1] using
        (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq hev

private theorem continuous_hermite' : Continuous hermite' := by
  have hpc : Continuous (fun s : ℝ => 6 * s - 6 * s ^ 2) :=
    (continuous_const.mul continuous_id).sub (continuous_const.mul (continuous_id.pow 2))
  rw [continuous_iff_continuousAt]; intro t
  rcases lt_trichotomy t 0 with ht0 | rfl | ht0
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [gt_mem_nhds ht0] with s hs; unfold hermite'; rw [if_pos hs.le]
  · have hev : hermite' =ᶠ[𝓝 (0 : ℝ)] fun s => if s ≤ 0 then 0 else 6 * s - 6 * s ^ 2 := by
      filter_upwards [gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
      unfold hermite'; split_ifs with h0 h1 <;> first | rfl | linarith
    exact (continuousAt_glue (c := (0 : ℝ)) continuousAt_const hpc.continuousAt (by norm_num)).congr hev.symm
  · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
    · refine hpc.continuousAt.congr ?_
      filter_upwards [(lt_mem_nhds ht0).and (gt_mem_nhds ht1)] with s ⟨hs0, hs1⟩
      unfold hermite'; rw [if_neg (not_le.mpr hs0), if_pos hs1.le]
    · have hev : hermite' =ᶠ[𝓝 (1 : ℝ)] fun s => if s ≤ 1 then 6 * s - 6 * s ^ 2 else 0 := by
        filter_upwards [lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)] with s hs
        unfold hermite'; rw [if_neg (not_le.mpr hs)]
      exact (continuousAt_glue (c := (1 : ℝ)) hpc.continuousAt continuousAt_const (by norm_num)).congr hev.symm
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [lt_mem_nhds ht1] with s hs
      unfold hermite'; rw [if_neg (by linarith), if_neg (not_le.mpr hs)]

private theorem contDiff_hermite : ContDiff ℝ 1 hermite := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hasDerivAt_hermite t).differentiableAt, ?_⟩
  rw [show deriv hermite = hermite' from funext fun t => (hasDerivAt_hermite t).deriv]
  exact continuous_hermite'

private noncomputable def cut1 (R s : ℝ) : ℝ := hermite (R - s) * hermite (R + s)

private theorem contDiff_cut1 (R : ℝ) : ContDiff ℝ 1 (cut1 R) :=
  (contDiff_hermite.comp (contDiff_const.sub contDiff_id)).mul
    (contDiff_hermite.comp (contDiff_const.add contDiff_id))

private theorem cut1_bounds (R s : ℝ) : 0 ≤ cut1 R s ∧ cut1 R s ≤ 1 := by
  have h1 := hermite_bounds (R - s); have h2 := hermite_bounds (R + s)
  exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩

private theorem cut1_one {R s : ℝ} (hs : s ∈ Icc (-(R - 1)) (R - 1)) : cut1 R s = 1 := by
  unfold cut1; rw [hermite_one_of_ge (by linarith [hs.2]), hermite_one_of_ge (by linarith [hs.1]), mul_one]

private theorem cut1_zero {R s : ℝ} (hs : R ≤ |s|) : cut1 R s = 0 := by
  unfold cut1
  rcases le_or_gt 0 s with h | h
  · rw [abs_of_nonneg h] at hs; rw [hermite_zero_of_le (t := R - s) (by linarith), zero_mul]
  · rw [abs_of_neg h] at hs; rw [hermite_zero_of_le (t := R + s) (by linarith), mul_zero]

private theorem hasCompactSupport_cut1 (R : ℝ) : HasCompactSupport (cut1 R) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -max R 0) (b := max R 0)) ?_
  intro s hs; rw [Function.mem_support] at hs; rw [Set.mem_Icc, ← abs_le]
  by_contra! hgt; exact hs (cut1_zero (le_trans (le_max_left R 0) hgt.le))

private theorem deriv_cut1_props (R s : ℝ) :
    |deriv (cut1 R) s| ≤ 3 ∧
    (s ∈ Icc (-(R - 1)) (R - 1) → deriv (cut1 R) s = 0) ∧
    (R ≤ |s| → deriv (cut1 R) s = 0) := by
  have hd1 : HasDerivAt (fun t : ℝ => hermite (R - t)) (-hermite' (R - s)) s :=
    ((hasDerivAt_hermite (R - s)).comp s
      (by simpa using (hasDerivAt_const s R).fun_sub (hasDerivAt_id s))).congr_deriv (by ring)
  have hd2 : HasDerivAt (fun t : ℝ => hermite (R + t)) (hermite' (R + s)) s :=
    ((hasDerivAt_hermite (R + s)).comp s
      (by simpa using (hasDerivAt_id s).const_add R)).congr_deriv (by ring)
  have hder : deriv (cut1 R) s =
      -hermite' (R - s) * hermite (R + s) + hermite (R - s) * hermite' (R + s) := by
    rw [show cut1 R = fun t => hermite (R - t) * hermite (R + t) from rfl, (hd1.fun_mul hd2).deriv]
  refine ⟨?_, ?_, ?_⟩
  · rw [hder]
    have ha : |-hermite' (R - s) * hermite (R + s)| ≤ 3 / 2 := by
      rw [abs_mul, abs_neg, abs_of_nonneg (hermite_bounds _).1]
      nlinarith [abs_nonneg (hermite' (R - s)), hermite'_abs_le (R - s), (hermite_bounds (R + s)).2]
    have hc : |hermite (R - s) * hermite' (R + s)| ≤ 3 / 2 := by
      rw [abs_mul, abs_of_nonneg (hermite_bounds _).1]
      nlinarith [abs_nonneg (hermite' (R + s)), hermite'_abs_le (R + s), (hermite_bounds (R - s)).2]
    exact (abs_add_le _ _).trans (by linarith)
  · intro hs; rw [hder]
    have h0 (t : ℝ) (ht : 1 ≤ t) : hermite' t = 0 := by
      unfold hermite'; split_ifs with h1 h2
      · rfl
      · have : t = 1 := le_antisymm h2 ht; subst this; norm_num
      · rfl
    rw [h0 (R - s) (by linarith [hs.2]), h0 (R + s) (by linarith [hs.1])]; ring
  · intro hs; rw [hder]
    rcases le_or_gt 0 s with h | h
    · rw [abs_of_nonneg h] at hs; rw [hermite_zero_of_le (t := R - s) (by linarith), hermite'_zero_of_le (t := R - s) (by linarith)]; ring
    · rw [abs_of_neg h] at hs; rw [hermite_zero_of_le (t := R + s) (by linarith), hermite'_zero_of_le (t := R + s) (by linarith)]; ring

private theorem deriv_cut1_abs_le (R s : ℝ) : |deriv (cut1 R) s| ≤ 3 := (deriv_cut1_props R s).1
private theorem deriv_cut1_zero_inner {R s : ℝ} (hs : s ∈ Icc (-(R - 1)) (R - 1)) : deriv (cut1 R) s = 0 := (deriv_cut1_props R s).2.1 hs
private theorem deriv_cut1_zero_outer {R s : ℝ} (hs : R ≤ |s|) : deriv (cut1 R) s = 0 := (deriv_cut1_props R s).2.2 hs

private theorem integral_cut1_ge {L : ℝ} (hL : 2 ≤ L) :
    2 * (L - 1) ≤ ∫ s : ℝ, cut1 L s := by
  have hint : Integrable (cut1 L) :=
    (contDiff_cut1 L).continuous.integrable_of_hasCompactSupport (hasCompactSupport_cut1 L)
  have h1 : (∫ s in Icc (-(L - 1)) (L - 1), cut1 L s) ≤ ∫ s : ℝ, cut1 L s :=
    setIntegral_le_integral hint (ae_of_all _ fun s => (cut1_bounds L s).1)
  have h2 : (∫ s in Icc (-(L - 1)) (L - 1), cut1 L s) = 2 * (L - 1) := by
    have hcongr : (∫ s in Icc (-(L - 1)) (L - 1), cut1 L s) =
        ∫ _s in Icc (-(L - 1)) (L - 1), (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs => cut1_one hs
    rw [hcongr, setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]; ring
  linarith

private theorem integral_cut1_sq_ge {L : ℝ} (hL : 2 ≤ L) :
    2 * (L - 1) ≤ ∫ s : ℝ, (cut1 L s) ^ 2 := by
  have hint : Integrable (fun s : ℝ => (cut1 L s) ^ 2) :=
    ((contDiff_cut1 L).continuous.pow 2).integrable_of_hasCompactSupport
      ((hasCompactSupport_cut1 L).mono' fun s hs => subset_closure fun h0 => hs (by simp [h0]))
  have h1 : (∫ s in Icc (-(L - 1)) (L - 1), (cut1 L s) ^ 2) ≤ ∫ s : ℝ, (cut1 L s) ^ 2 :=
    setIntegral_le_integral hint (ae_of_all _ fun s => sq_nonneg _)
  have h2 : (∫ s in Icc (-(L - 1)) (L - 1), (cut1 L s) ^ 2) = 2 * (L - 1) := by
    have hcongr : (∫ s in Icc (-(L - 1)) (L - 1), (cut1 L s) ^ 2) =
        ∫ _s in Icc (-(L - 1)) (L - 1), (1 : ℝ) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [cut1_one hs, one_pow]
    rw [hcongr, setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]; ring
  linarith

private theorem integral_deriv_cut1_sq_le {L : ℝ} (hL : 2 ≤ L) :
    (∫ s : ℝ, (deriv (cut1 L) s) ^ 2) ≤ 18 := by
  let S : Set ℝ := Icc (-L) L \ Icc (-(L - 1)) (L - 1)
  have hSm : MeasurableSet S := measurableSet_Icc.diff measurableSet_Icc
  have hsupp : ∀ s ∉ S, (deriv (cut1 L) s) ^ 2 = 0 := by
    intro s hs
    by_cases h1 : s ∈ Icc (-L) L
    · rw [deriv_cut1_zero_inner (by by_contra hnot; exact hs ⟨h1, hnot⟩), zero_pow two_ne_zero]
    · have h2 : L ≤ |s| := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at h1
        rcases h1 with hlt | hgt
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [deriv_cut1_zero_outer h2, zero_pow two_ne_zero]
  have hint : Integrable (fun s : ℝ => (deriv (cut1 L) s) ^ 2) := by
    refine (((contDiff_cut1 L).continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -L) (b := L)) ?_
    intro s hs; by_contra hnot; exact hs (hsupp s fun hS => hnot hS.1)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
  have hfin : volume S ≠ ⊤ :=
    ((measure_mono sdiff_subset).trans_lt (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)).ne
  have hmono := setIntegral_mono_on hint.integrableOn (integrableOn_const (C := (9 : ℝ)) hfin) hSm
    (fun s _ => by rw [← sq_abs (deriv (cut1 L) s)]; nlinarith [abs_nonneg (deriv (cut1 L) s), deriv_cut1_abs_le L s])
  rw [setIntegral_const, smul_eq_mul] at hmono
  have hvol : volume.real S = 2 := by
    have hsub : Icc (-(L - 1)) (L - 1) ⊆ Icc (-L) L := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hfin1 : volume (Icc (-(L - 1)) (L - 1)) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    rw [Measure.real, measure_sdiff hsub measurableSet_Icc.nullMeasurableSet hfin1,
      Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_sub _ (by linarith),
      ENNReal.toReal_ofReal (by linarith)]; ring
  rw [hvol] at hmono; linarith

end Core

namespace Mod1
open InnerProductSpace MeasureTheory Filter Set Metric Finset
open scoped Topology Laplacian
private theorem local_max_second_nonpos {f g : ℝ → ℝ} {s : ℝ}
    (hf : ∀ t, HasDerivAt f (g t) t) (hg : HasDerivAt g s 0)
    (hm : IsLocalMax f 0) : s ≤ 0 := by
  by_contra! hs
  have hg0 : g 0 = 0 := (hf 0).deriv.symm.trans hm.deriv_eq_zero
  have hslope : Tendsto (fun t => (g t - g 0) / t) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    have h1 := hg.tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_inv_mul] using h1
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < g t := by
    filter_upwards [hslope (lt_mem_nhds hs), self_mem_nhdsWithin] with t ht ht0
    change 0 < (g t - g 0) / t at ht
    rw [hg0, sub_zero] at ht
    exact (div_pos_iff_of_pos_right ht0).mp ht
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t ≤ f 0 :=
    hm.filter_mono nhdsWithin_le_nhds
  obtain ⟨δ, hδ, hIoo⟩ := (Metric.mem_nhdsWithin_iff.mp (hpos.and hle))
  have hmem : ∀ t ∈ Ioo (0 : ℝ) δ, 0 < g t ∧ f t ≤ f 0 := by
    intro t ⟨ht0, htδ⟩
    exact hIoo ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht0]; exact htδ, ht0⟩
  have ht_pos : 0 < δ / 2 := half_pos hδ
  have hdiff : ∀ x ∈ Ioo (0 : ℝ) (δ / 2), HasDerivAt f (g x) x := fun x _ => hf x
  have hcont : ContinuousOn f (Icc 0 (δ / 2)) :=
    (continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt).continuousOn
  obtain ⟨c, ⟨hc0, hc1⟩, hslope_eq⟩ := exists_hasDerivAt_eq_slope f g ht_pos hcont hdiff
  have hc_pos : 0 < g c := (hmem c ⟨hc0, lt_trans hc1 (half_lt_self hδ)⟩).1
  have hft_le : f (δ / 2) ≤ f 0 := (hmem (δ / 2) ⟨ht_pos, half_lt_self hδ⟩).2
  have hquot_le : (f (δ / 2) - f 0) / (δ / 2 - 0) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hft_le) (by linarith)
  linarith

private theorem line_second3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x : Space) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => pd3 u i (x + t • e3 i)) (pd32 u i i x) 0 := by
  have h1 : ContDiff ℝ 1 (pd3 u i) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  simpa [pd32, pd3] using line_deriv3 h1 x (e3 i) 0

private theorem laplacian_eq_sum_pd32 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x : Space) :
    (Δ u) x = ∑ i : Fin 3, pd32 u i i x := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  apply sum_congr rfl
  intro i _
  have hb : b i = e3 i := by
    ext j
    simp [b, e3, EuclideanSpace.basisFun_apply]
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  rw [iteratedFDeriv_two_apply, hb]
  unfold pd32 pd3
  rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const (e3 i))]
  simp

private theorem le_one_of_bounded_sol {u : Space → ℝ} (hu : IsBoundedSol u)
    (x0 : Space) : u x0 ≤ 1 := by
  by_contra! hgt
  obtain ⟨C, hC⟩ := hu.bounded
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  let a0 := (u x0 + 1) / 2
  have ha0_gt : 1 < a0 := by dsimp [a0]; linarith
  have ha0_lt : a0 < u x0 := by dsimp [a0]; linarith
  have hgap : 0 < a0 ^ 3 - a0 := by
    have : a0 ^ 3 - a0 = a0 * (a0 - 1) * (a0 + 1) := by ring
    rw [this]; positivity
  let ε := min ((u x0 - a0) / (‖x0‖ ^ 2 + 1)) ((a0 ^ 3 - a0) / 12)
  have hε_pos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε_x0 : ε * ‖x0‖ ^ 2 < u x0 - a0 := by
    calc ε * ‖x0‖ ^ 2 ≤ ((u x0 - a0) / (‖x0‖ ^ 2 + 1)) * ‖x0‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
      _ < ((u x0 - a0) / (‖x0‖ ^ 2 + 1)) * (‖x0‖ ^ 2 + 1) :=
          mul_lt_mul_of_pos_left (by linarith) (by positivity)
      _ = u x0 - a0 := by field_simp
  have hε_gap : 6 * ε < a0 ^ 3 - a0 := by
    have hle : ε ≤ (a0 ^ 3 - a0) / 12 := min_le_right _ _
    linarith
  let f (x : Space) : ℝ := u x - ε * ‖x‖ ^ 2
  have hf_cont : Continuous f :=
    hu.regular.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hfx0 : a0 < f x0 := by dsimp [f]; linarith
  let R := max ‖x0‖ (Real.sqrt ((C - f x0 + 1) / ε))
  have hR_x0 : x0 ∈ closedBall (0 : Space) R := by
    rw [mem_closedBall, dist_zero_right]
    exact le_max_left _ _
  obtain ⟨xm, _, hxm_max⟩ := (isCompact_closedBall (0 : Space) R).exists_isMaxOn
    ⟨x0, hR_x0⟩ hf_cont.continuousOn
  have hglobal : ∀ x : Space, f x ≤ f xm := by
    intro x
    by_cases hx : x ∈ closedBall (0 : Space) R
    · exact isMaxOn_iff.mp hxm_max x hx
    · have hlt : R < ‖x‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at hx
        exact hx
      have hsq : (C - f x0 + 1) / ε < ‖x‖ ^ 2 := by
        have h1 : Real.sqrt ((C - f x0 + 1) / ε) ≤ R := le_max_right _ _
        have h2 : Real.sqrt ((C - f x0 + 1) / ε) < ‖x‖ := lt_of_le_of_lt h1 hlt
        have h3 : (Real.sqrt ((C - f x0 + 1) / ε)) ^ 2 < ‖x‖ ^ 2 :=
          sq_lt_sq' (by linarith [Real.sqrt_nonneg ((C - f x0 + 1) / ε)]) h2
        have hnum : 0 ≤ (C - f x0 + 1) / ε := by
          have hux0 : u x0 ≤ C := (abs_le.mp (hC x0)).2
          have : f x0 ≤ C := by dsimp [f]; nlinarith [sq_nonneg ‖x0‖]
          exact div_nonneg (by linarith) hε_pos.le
        rwa [Real.sq_sqrt hnum] at h3
      have hfx_lt : f x < f x0 := by
        have hux : u x ≤ C := (abs_le.mp (hC x)).2
        have hmul : C - f x0 + 1 < ε * ‖x‖ ^ 2 := (div_lt_iff₀' hε_pos).mp hsq
        dsimp [f]
        linarith
      exact hfx_lt.le.trans (isMaxOn_iff.mp hxm_max x0 hR_x0)
  have huxm_ge : a0 ≤ u xm := by
    have h1 : f x0 ≤ f xm := hglobal x0
    have h2 : f xm ≤ u xm := by dsimp [f]; nlinarith [sq_nonneg ‖xm‖]
    linarith
  have hsec (i : Fin 3) : pd32 u i i xm - 2 * ε ≤ 0 := by
    let φ (t : ℝ) := f (xm + t • e3 i)
    let ψ (t : ℝ) := pd3 u i (xm + t • e3 i) - 2 * ε * (xm i + t)
    have hnorm_sq (t : ℝ) : ‖xm + t • e3 i‖ ^ 2 = ‖xm‖ ^ 2 + 2 * xm i * t + t ^ 2 := by
      rw [norm_add_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have he1 : ‖e3 i‖ = 1 := by simp [e3]
      have hin : inner ℝ xm (t • e3 i) = t * xm i := by
        rw [real_inner_smul_right, e3, EuclideanSpace.inner_single_right]
        simp
      rw [he1, hin]
      ring
    have hφ (t : ℝ) : HasDerivAt φ (ψ t) t := by
      have h1 : HasDerivAt (fun s => u (xm + s • e3 i)) (pd3 u i (xm + t • e3 i)) t :=
        line_deriv3 (hu.regular.of_le (by norm_num)) xm (e3 i) t
      have ha1 : HasDerivAt (fun s : ℝ => ‖xm‖ ^ 2 + 2 * xm i * s) (2 * xm i) t := by
        simpa using ((hasDerivAt_id t).const_mul (2 * xm i)).const_add (‖xm‖ ^ 2)
      have ha2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      have ha : HasDerivAt (fun s : ℝ => ‖xm‖ ^ 2 + 2 * xm i * s + s ^ 2) (2 * xm i + 2 * t) t :=
        ha1.add ha2
      have h2 : HasDerivAt (fun s => ε * (‖xm‖ ^ 2 + 2 * xm i * s + s ^ 2))
          (2 * ε * (xm i + t)) t :=
        (ha.const_mul ε).congr_deriv (by ring)
      have h2' : HasDerivAt (fun s => ε * ‖xm + s • e3 i‖ ^ 2) (2 * ε * (xm i + t)) t := by
        have heq : (fun s => ε * ‖xm + s • e3 i‖ ^ 2) =
            fun s => ε * (‖xm‖ ^ 2 + 2 * xm i * s + s ^ 2) := by
          ext s; rw [hnorm_sq s]
        rwa [heq]
      exact h1.fun_sub h2'
    have hψ : HasDerivAt ψ (pd32 u i i xm - 2 * ε) 0 := by
      have h1 := line_second3 hu.regular xm i
      have h2 : HasDerivAt (fun t : ℝ => 2 * ε * (xm i + t)) (2 * ε) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_add (xm i)).const_mul (2 * ε)
      exact h1.sub h2
    have hm : IsLocalMax φ 0 :=
      Eventually.of_forall fun t => by simpa [φ] using hglobal (xm + t • e3 i)
    exact local_max_second_nonpos hφ hψ hm
  have hlap : (Δ u) xm ≤ 6 * ε := by
    rw [laplacian_eq_sum_pd32 hu.regular xm, Fin.sum_univ_three]
    linarith [hsec 0, hsec 1, hsec 2]
  have hpde : u xm ^ 3 - u xm = (Δ u) xm := by linarith [hu.solution xm]
  have hmono : a0 ^ 3 - a0 ≤ u xm ^ 3 - u xm := by
    have hdiff : (u xm ^ 3 - u xm) - (a0 ^ 3 - a0) =
        (u xm - a0) * (u xm ^ 2 + u xm * a0 + a0 ^ 2 - 1) := by ring
    have hfac : 0 ≤ u xm ^ 2 + u xm * a0 + a0 ^ 2 - 1 := by nlinarith
    have hprod : 0 ≤ (u xm - a0) * (u xm ^ 2 + u xm * a0 + a0 ^ 2 - 1) :=
      mul_nonneg (by linarith) hfac
    linarith
  linarith

private theorem abs_le_one_of_bounded_sol {u : Space → ℝ} (hu : IsBoundedSol u)
    (x : Space) : |u x| ≤ 1 := by
  rw [abs_le]
  refine ⟨?_, le_one_of_bounded_sol hu x⟩
  have hneg : IsBoundedSol (fun y => -u y) := by
    refine ⟨hu.regular.neg, ?_, ?_⟩
    · obtain ⟨C, hC⟩ := hu.bounded
      exact ⟨C, fun y => by simpa [abs_neg] using hC y⟩
    · intro y
      have hlap : (Δ (fun z => -u z)) y = -(Δ u) y := by
        rw [laplacian_eq_sum_pd32 hu.regular.neg, laplacian_eq_sum_pd32 hu.regular]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        have h1 : pd3 (fun z => -u z) i = fun z => -pd3 u i z := by
          funext z
          unfold pd3
          rw [fderiv_fun_neg]
          simp
        unfold pd32
        rw [h1]
        unfold pd3
        rw [fderiv_fun_neg]
        simp
      rw [hlap]
      linarith [hu.solution y]
  linarith [le_one_of_bounded_sol hneg x]

private noncomputable def g1 (t s : ℝ) : ℝ :=
  (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(s ^ 2) / (4 * t))

private noncomputable def g1' (t s : ℝ) : ℝ :=
  (-s / (2 * t)) * g1 t s

private noncomputable def g1'' (t s : ℝ) : ℝ :=
  (s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g1 t s

private noncomputable def G (t : ℝ) (z : Space) : ℝ :=
  ∏ i : Fin 3, g1 t (z i)

private noncomputable def dG (i : Fin 3) (t : ℝ) (z : Space) : ℝ :=
  (-z i / (2 * t)) * G t z

private noncomputable def ΔG (t : ℝ) (z : Space) : ℝ :=
  ∑ i : Fin 3, ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z

private theorem g1_pos {t : ℝ} (ht : 0 < t) (s : ℝ) : 0 < g1 t s := by
  unfold g1
  positivity

private theorem G_pos {t : ℝ} (ht : 0 < t) (z : Space) : 0 < G t z :=
  Finset.prod_pos fun i _ => g1_pos ht (z i)

private theorem hasDerivAt_g1_space {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (g1 t) (g1' t s) s := by
  have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / (4 * t)) (-s / (2 * t)) s := by
    have ha := ((hasDerivAt_pow 2 s).neg).div_const (4 * t)
    refine ha.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    field_simp [ht.ne']
    ring
  have h2 := h1.exp.const_mul (Real.sqrt (4 * Real.pi * t))⁻¹
  refine h2.congr_deriv ?_
  unfold g1' g1
  ring

private theorem hasDerivAt_g1'_space {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (g1' t) (g1'' t s) s := by
  have h1 : HasDerivAt (fun x : ℝ => -x / (2 * t)) (-1 / (2 * t)) s := by
    simpa using ((hasDerivAt_id s).neg).div_const (2 * t)
  have h2 := h1.mul (hasDerivAt_g1_space ht s)
  refine h2.congr_deriv ?_
  unfold g1'' g1'
  field_simp [ht.ne']
  ring

private theorem hasDerivAt_g1_time {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (fun τ : ℝ => g1 τ s) (g1'' t s) t := by
  have h4pi : 0 < 4 * Real.pi * t := by positivity
  have hsqrt : HasDerivAt (fun τ : ℝ => Real.sqrt (4 * Real.pi * τ))
      ((4 * Real.pi) / (2 * Real.sqrt (4 * Real.pi * t))) t := by
    have hlin : HasDerivAt (fun τ : ℝ => 4 * Real.pi * τ) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    exact (hlin.sqrt h4pi.ne').congr_deriv (by ring)
  have hinv : HasDerivAt (fun τ : ℝ => (Real.sqrt (4 * Real.pi * τ))⁻¹)
      (-(4 * Real.pi / (2 * Real.sqrt (4 * Real.pi * t))) / (Real.sqrt (4 * Real.pi * t)) ^ 2) t :=
    hsqrt.inv (Real.sqrt_ne_zero'.mpr h4pi)
  have hexp_arg : HasDerivAt (fun τ : ℝ => -(s ^ 2) / (4 * τ)) (s ^ 2 / (4 * t ^ 2)) t := by
    have h4 : HasDerivAt (fun τ : ℝ => 4 * τ) 4 t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have hdiv := (hasDerivAt_const t (-(s ^ 2))).div h4 (by positivity)
    refine hdiv.congr_deriv ?_
    field_simp [ht.ne']
    ring
  have hprod := hinv.mul hexp_arg.exp
  refine hprod.congr_deriv ?_
  unfold g1'' g1
  rw [Real.sq_sqrt h4pi.le]
  have hsqne : Real.sqrt (4 * Real.pi * t) ≠ 0 := Real.sqrt_ne_zero'.mpr h4pi
  have hpine : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [ht.ne', hsqne, hpine]
  ring

private theorem integrable_g1 {t : ℝ} (ht : 0 < t) : Integrable (g1 t) := by
  have hb : 0 < (4 * t)⁻¹ := by positivity
  have h := (integrable_exp_neg_mul_sq hb).const_mul (Real.sqrt (4 * Real.pi * t))⁻¹
  have heq : g1 t = fun s => (Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * s ^ 2) := by
    ext s; unfold g1; congr 2; ring
  rwa [heq]

private theorem integral_g1 {t : ℝ} (ht : 0 < t) : ∫ s : ℝ, g1 t s = 1 := by
  have h4pi : 0 < 4 * Real.pi * t := by positivity
  have hsub : (fun s : ℝ => Real.exp (-(s ^ 2) / (4 * t))) =
      fun s : ℝ => Real.exp (-(4 * t)⁻¹ * s ^ 2) := by
    ext s; congr 1; ring
  unfold g1
  rw [integral_const_mul, hsub, integral_gaussian (4 * t)⁻¹]
  have hdiv : Real.pi / (4 * t)⁻¹ = 4 * Real.pi * t := by field_simp
  rw [hdiv]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr h4pi)

private theorem sq_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (s : ℝ) :
    s ^ 2 * Real.exp (-a * s ^ 2) ≤ (2 / a) * Real.exp (-(a / 2) * s ^ 2) := by
  have hexp : (a / 2) * s ^ 2 ≤ Real.exp ((a / 2) * s ^ 2) := by
    linarith [Real.add_one_le_exp ((a / 2) * s ^ 2)]
  have hmul := mul_le_mul_of_nonneg_right hexp (Real.exp_nonneg (-a * s ^ 2))
  have hcomb : Real.exp ((a / 2) * s ^ 2) * Real.exp (-a * s ^ 2) =
      Real.exp (-(a / 2) * s ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hcomb] at hmul
  have h2a : 0 < 2 / a := by positivity
  have hfinal := mul_le_mul_of_nonneg_left hmul h2a.le
  calc s ^ 2 * Real.exp (-a * s ^ 2)
      = (2 / a) * ((a / 2) * s ^ 2 * Real.exp (-a * s ^ 2)) := by field_simp [ha.ne']
    _ ≤ (2 / a) * Real.exp (-(a / 2) * s ^ 2) := hfinal

private theorem abs_mul_exp_neg_le {a : ℝ} (ha : 0 < a) (s : ℝ) :
    |s| * Real.exp (-a * s ^ 2) ≤ (1 + 2 / a) * Real.exp (-(a / 2) * s ^ 2) := by
  have habs : |s| ≤ 1 + s ^ 2 := by
    nlinarith [sq_nonneg (|s| - 1), sq_abs s]
  have h1 : |s| * Real.exp (-a * s ^ 2) ≤ Real.exp (-a * s ^ 2) + s ^ 2 * Real.exp (-a * s ^ 2) := by
    nlinarith [Real.exp_nonneg (-a * s ^ 2)]
  have h2 : Real.exp (-a * s ^ 2) ≤ Real.exp (-(a / 2) * s ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg s])
  linarith [sq_mul_exp_neg_le ha s]

private theorem integrable_g1' {t : ℝ} (ht : 0 < t) : Integrable (g1' t) := by
  have ha : 0 < (4 * t)⁻¹ := by positivity
  have hdom : Integrable (fun s : ℝ =>
      ((2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * (1 + 2 / (4 * t)⁻¹)) *
        Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun s => ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold g1' g1; fun_prop))
  · rw [Real.norm_eq_abs]
    unfold g1' g1
    rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))),
      abs_of_pos (Real.exp_pos _)]
    have heq : -(s ^ 2) / (4 * t) = -(4 * t)⁻¹ * s ^ 2 := by ring
    rw [heq]
    have hb := abs_mul_exp_neg_le ha s
    have hcoeff : 0 ≤ (2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
    calc |s| / (2 * t) * ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * s ^ 2))
        = (2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ * (|s| * Real.exp (-(4 * t)⁻¹ * s ^ 2)) := by
          ring
      _ ≤ (2 * t)⁻¹ * (Real.sqrt (4 * Real.pi * t))⁻¹ *
            ((1 + 2 / (4 * t)⁻¹) * Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2)) :=
          mul_le_mul_of_nonneg_left hb hcoeff
      _ = _ := by ring

private theorem integrable_g1'' {t : ℝ} (ht : 0 < t) : Integrable (g1'' t) := by
  have ha : 0 < (4 * t)⁻¹ := by positivity
  have hdom : Integrable (fun s : ℝ =>
      ((Real.sqrt (4 * Real.pi * t))⁻¹ * ((4 * t ^ 2)⁻¹ * (2 / (4 * t)⁻¹) + (2 * t)⁻¹)) *
        Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity)).const_mul _
  refine hdom.mono' ?_ (ae_of_all _ fun s => ?_)
  · exact (Continuous.aestronglyMeasurable (by unfold g1'' g1; fun_prop))
  · rw [Real.norm_eq_abs]
    unfold g1'' g1
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))),
      abs_of_pos (Real.exp_pos _)]
    have heq : -(s ^ 2) / (4 * t) = -(4 * t)⁻¹ * s ^ 2 := by ring
    rw [heq]
    have htri : |s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤ s ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
      calc |s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)|
          ≤ |s ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
        _ = s ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
            rw [abs_of_nonneg (by positivity), abs_of_pos (by positivity)]
    have h1 := sq_mul_exp_neg_le ha s
    have h2 : Real.exp (-(4 * t)⁻¹ * s ^ 2) ≤ Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith [sq_nonneg s])
    have hc : 0 ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ := by positivity
    calc |s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| *
            ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * s ^ 2))
        ≤ (s ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) *
            ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-(4 * t)⁻¹ * s ^ 2)) :=
          mul_le_mul_of_nonneg_right htri (by positivity)
      _ = (Real.sqrt (4 * Real.pi * t))⁻¹ *
            ((4 * t ^ 2)⁻¹ * (s ^ 2 * Real.exp (-(4 * t)⁻¹ * s ^ 2)) +
              (2 * t)⁻¹ * Real.exp (-(4 * t)⁻¹ * s ^ 2)) := by ring
      _ ≤ (Real.sqrt (4 * Real.pi * t))⁻¹ *
            ((4 * t ^ 2)⁻¹ * ((2 / (4 * t)⁻¹) * Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2)) +
              (2 * t)⁻¹ * Real.exp (-((4 * t)⁻¹ / 2) * s ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
            (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = _ := by ring

private theorem integral_abs_g1' {t : ℝ} (ht : 0 < t) :
    ∫ s : ℝ, |g1' t s| = (Real.sqrt (Real.pi * t))⁻¹ := by
  let f (s : ℝ) : ℝ := (s / (2 * t)) * Real.exp (-(s ^ 2) / (4 * t))
  let F (s : ℝ) : ℝ := -Real.exp (-(s ^ 2) / (4 * t))
  have hderiv (s : ℝ) : HasDerivAt F (f s) s := by
    have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / (4 * t)) (-s / (2 * t)) s := by
      have ha := ((hasDerivAt_pow 2 s).neg).div_const (4 * t)
      refine ha.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      field_simp [ht.ne']
      ring
    exact h1.exp.neg.congr_deriv (by dsimp [f]; ring)
  have hlim : Tendsto F atTop (𝓝 0) := by
    have harg : Tendsto (fun s : ℝ => -(s ^ 2) / (4 * t)) atTop atBot := by
      have hsq : Tendsto (fun s : ℝ => s ^ 2) atTop atTop :=
        (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
      have hdiv : Tendsto (fun s : ℝ => s ^ 2 / (4 * t)) atTop atTop :=
        Tendsto.atTop_div_const (by positivity) hsq
      exact (tendsto_neg_atTop_atBot.comp hdiv).congr fun s => by simp [Function.comp_def]; ring
    simpa [F] using (Real.tendsto_exp_atBot.comp harg).neg
  have hint_f : Integrable (fun s : ℝ => |f s|) := by
    have h := (integrable_g1' ht).norm
    have heq : (fun s : ℝ => |f s|) =
        fun s : ℝ => Real.sqrt (4 * Real.pi * t) * ‖g1' t s‖ := by
      ext s
      rw [Real.norm_eq_abs]
      unfold g1' g1
      dsimp [f]
      rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_neg,
        abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))),
        abs_of_pos (Real.exp_pos _)]
      have hsqne : Real.sqrt (4 * Real.pi * t) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (by positivity)
      field_simp [hsqne]
    rw [heq]
    exact h.const_mul _
  have hint_f_Ioi : IntegrableOn f (Ioi (0 : ℝ)) := by
    refine hint_f.integrableOn.congr_fun (fun s hs => ?_) measurableSet_Ioi
    have hs0 : 0 < s := hs
    dsimp [f]
    exact abs_of_nonneg (by positivity)
  have hIoi : ∫ s in Ioi (0 : ℝ), f s = 1 := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun s _ => hderiv s) hint_f_Ioi hlim
    simpa [F] using h
  have hIoi_abs : ∫ s in Ioi (0 : ℝ), |f s| = 1 := by
    rw [← hIoi]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    have hs0 : 0 < s := hs
    dsimp [f]
    exact abs_of_nonneg (by positivity)
  have hIic_abs : ∫ s in Iic (0 : ℝ), |f s| = 1 := by
    have heven : ∀ s : ℝ, |f (-s)| = |f s| := by
      intro s
      dsimp [f]
      rw [neg_div, neg_sq, abs_mul, abs_neg, ← abs_mul]
    have h1 := integral_comp_neg_Iic (f := fun s => |f s|) (0 : ℝ)
    simp only [neg_zero] at h1
    have heq_f : (fun s : ℝ => |f s|) = fun s => |f (-s)| := funext fun s => (heven s).symm
    rw [heq_f, h1, hIoi_abs]
  have htotal : ∫ s : ℝ, |f s| = 2 := by
    have hsplit := integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic hint_f
    rw [compl_Iic] at hsplit
    linarith [hIic_abs, hIoi_abs]
  have heq : (fun s : ℝ => |g1' t s|) =
      fun s : ℝ => (Real.sqrt (4 * Real.pi * t))⁻¹ * |f s| := by
    ext s
    unfold g1' g1
    dsimp [f]
    rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_neg,
      abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))),
      abs_of_pos (Real.exp_pos _)]
    ring
  rw [heq, integral_const_mul, htotal]
  have hsq : Real.sqrt (4 * Real.pi * t) = 2 * Real.sqrt (Real.pi * t) := by
    rw [show 4 * Real.pi * t = 2 ^ 2 * (Real.pi * t) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  rw [hsq]
  have hne : Real.sqrt (Real.pi * t) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
  field_simp [hne]

private theorem integrable_prod3 {f : Fin 3 → ℝ → ℝ} (hf : ∀ i, Integrable (f i)) :
    Integrable (fun z : Space => ∏ i : Fin 3, f i (z i)) := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  exact Integrable.fintype_prod hf

private theorem integral_prod3 (f : Fin 3 → ℝ → ℝ) :
    (∫ z : Space, ∏ i : Fin 3, f i (z i)) = ∏ i : Fin 3, ∫ s : ℝ, f i s := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).measurableEmbedding]
  exact integral_fintype_prod_volume_eq_prod f

private theorem integrable_G {t : ℝ} (ht : 0 < t) : Integrable (G t) :=
  integrable_prod3 fun _ => integrable_g1 ht

private theorem integral_G {t : ℝ} (ht : 0 < t) : ∫ z : Space, G t z = 1 := by
  unfold G
  rw [integral_prod3 (fun _ s => g1 t s)]
  simp [Fin.prod_univ_three, integral_g1 ht]

private theorem dG_eq_prod (i : Fin 3) (t : ℝ) (z : Space) :
    dG i t z = ∏ j : Fin 3, (if j = i then g1' t (z j) else g1 t (z j)) := by
  unfold dG G g1'
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

private theorem integrable_dG (i : Fin 3) {t : ℝ} (ht : 0 < t) : Integrable (dG i t) := by
  have heq : dG i t = fun z : Space => ∏ j : Fin 3, (if j = i then g1' t (z j) else g1 t (z j)) :=
    funext (dG_eq_prod i t)
  rw [heq]
  refine integrable_prod3 (f := fun j s => if j = i then g1' t s else g1 t s) ?_
  intro j
  split_ifs
  · exact integrable_g1' ht
  · exact integrable_g1 ht

private theorem integral_abs_dG (i : Fin 3) {t : ℝ} (ht : 0 < t) :
    ∫ z : Space, |dG i t z| = (Real.sqrt (Real.pi * t))⁻¹ := by
  have heq : (fun z : Space => |dG i t z|) =
      fun z => ∏ j : Fin 3, (if j = i then |g1' t (z j)| else g1 t (z j)) := by
    ext z
    rw [dG_eq_prod, Finset.abs_prod]
    apply Finset.prod_congr rfl
    intro j _
    split_ifs
    · rfl
    · exact abs_of_pos (g1_pos ht _)
  rw [heq, integral_prod3 (fun j s => if j = i then |g1' t s| else g1 t s)]
  fin_cases i <;> simp [Fin.prod_univ_three, integral_g1 ht, integral_abs_g1' ht]

private theorem ΔG_term_eq_prod (i : Fin 3) (t : ℝ) (z : Space) :
    ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z =
      ∏ j : Fin 3, (if j = i then g1'' t (z j) else g1 t (z j)) := by
  unfold G g1''
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

private theorem integrable_ΔG {t : ℝ} (ht : 0 < t) : Integrable (ΔG t) := by
  unfold ΔG
  apply integrable_finsetSum
  intro i _
  have heq : (fun z : Space => ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z) =
      fun z => ∏ j : Fin 3, (if j = i then g1'' t (z j) else g1 t (z j)) :=
    funext (ΔG_term_eq_prod i t)
  rw [heq]
  refine integrable_prod3 (f := fun j s => if j = i then g1'' t s else g1 t s) ?_
  intro j
  split_ifs
  · exact integrable_g1'' ht
  · exact integrable_g1 ht

private theorem contDiff_G {t : ℝ} (ht : 0 < t) : ContDiff ℝ 2 (G t) := by
  have hcoord (i : Fin 3) : ContDiff ℝ 2 (fun z : Space => g1 t (z i)) := by
    unfold g1
    have hc : ContDiff ℝ 2 (fun z : Space => z i) := (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    exact contDiff_const.mul (((hc.pow 2).neg.div_const (4 * t)).exp)
  have heq : G t = fun z => g1 t (z 0) * g1 t (z 1) * g1 t (z 2) := by
    ext z; unfold G; simp [Fin.prod_univ_three, mul_assoc]
  rw [heq]
  exact ((hcoord 0).mul (hcoord 1)).mul (hcoord 2)

private theorem pd3_G {t : ℝ} (ht : 0 < t) (i : Fin 3) (z : Space) :
    pd3 (G t) i z = dG i t z := by
  have hline : HasDerivAt (fun s : ℝ => G t (z + s • e3 i)) (dG i t z) 0 := by
    have hcoord (j : Fin 3) (s : ℝ) : (z + s • e3 i) j = z j + if j = i then s else 0 := by
      simp [e3, eq_comm]
    have hterm (j : Fin 3) : HasDerivAt (fun s : ℝ => g1 t ((z + s • e3 i) j))
        (if j = i then g1' t (z j) else 0) 0 := by
      simp_rw [hcoord j]
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte]
        have ha : HasDerivAt (fun s : ℝ => z j + s) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (z j)
        have hb : HasDerivAt (g1 t) (g1' t (z j)) (z j + 0) := by
          simpa using hasDerivAt_g1_space ht (z j)
        have hc := hb.comp 0 ha
        rw [mul_one] at hc
        exact hc
      · simp only [hji, ↓reduceIte, add_zero]
        exact hasDerivAt_const 0 _
    have h3 := ((hterm 0).fun_mul (hterm 1)).fun_mul (hterm 2)
    have hfun : (fun s : ℝ => g1 t ((z + s • e3 i) 0) * g1 t ((z + s • e3 i) 1) *
        g1 t ((z + s • e3 i) 2)) = fun s => G t (z + s • e3 i) := by
      ext s; unfold G; simp [Fin.prod_univ_three, mul_assoc]
    rw [hfun] at h3
    refine h3.congr_deriv ?_
    rw [dG_eq_prod]
    fin_cases i <;> simp [Fin.prod_univ_three, e3, g1'] <;> ring
  have hline2 := line_deriv3 ((contDiff_G ht).of_le (by norm_num)) z (e3 i) 0
  simp only [zero_smul, add_zero] at hline2
  exact hline2.unique hline

private theorem pd32_G {t : ℝ} (ht : 0 < t) (i : Fin 3) (z : Space) :
    pd32 (G t) i i z = ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z := by
  have heq : pd3 (G t) i = dG i t := funext fun w => pd3_G ht i w
  unfold pd32
  rw [heq]
  have hdG_c1 : ContDiff ℝ 1 (dG i t) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ (G t)) := (contDiff_G ht).fderiv_right (by norm_num)
    have h2 : ContDiff ℝ 1 (pd3 (G t) i) := h1.clm_apply contDiff_const
    rwa [heq] at h2
  have hline : HasDerivAt (fun s : ℝ => dG i t (z + s • e3 i))
      (((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z) 0 := by
    have hcoord (j : Fin 3) (s : ℝ) : (z + s • e3 i) j = z j + if j = i then s else 0 := by
      simp [e3, eq_comm]
    have hterm (j : Fin 3) : HasDerivAt
        (fun s : ℝ => if j = i then g1' t ((z + s • e3 i) j) else g1 t ((z + s • e3 i) j))
        (if j = i then g1'' t (z j) else 0) 0 := by
      simp_rw [hcoord j]
      by_cases hji : j = i
      · subst hji
        simp only [↓reduceIte]
        have ha : HasDerivAt (fun s : ℝ => z j + s) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (z j)
        have hb : HasDerivAt (g1' t) (g1'' t (z j)) (z j + 0) := by
          simpa using hasDerivAt_g1'_space ht (z j)
        have hc := hb.comp 0 ha
        rw [mul_one] at hc
        exact hc
      · simp only [hji, ↓reduceIte, add_zero]
        exact hasDerivAt_const 0 _
    have h3 := ((hterm 0).fun_mul (hterm 1)).fun_mul (hterm 2)
    have hfun : (fun s : ℝ =>
        (if (0 : Fin 3) = i then g1' t ((z + s • e3 i) 0) else g1 t ((z + s • e3 i) 0)) *
        (if (1 : Fin 3) = i then g1' t ((z + s • e3 i) 1) else g1 t ((z + s • e3 i) 1)) *
        (if (2 : Fin 3) = i then g1' t ((z + s • e3 i) 2) else g1 t ((z + s • e3 i) 2))) =
        fun s => dG i t (z + s • e3 i) := by
      ext s; rw [dG_eq_prod]; simp [Fin.prod_univ_three, mul_assoc]
    rw [hfun] at h3
    refine h3.congr_deriv ?_
    rw [ΔG_term_eq_prod]
    fin_cases i <;> simp [Fin.prod_univ_three, e3, g1''] <;> ring
  have hline2 := line_deriv3 hdG_c1 z (e3 i) 0
  simp only [zero_smul, add_zero] at hline2
  exact hline2.unique hline

private theorem hasDerivAt_G_time {t : ℝ} (ht : 0 < t) (z : Space) :
    HasDerivAt (fun τ : ℝ => G τ z) (ΔG t z) t := by
  have h3 := ((hasDerivAt_g1_time ht (z 0)).fun_mul (hasDerivAt_g1_time ht (z 1))).fun_mul
    (hasDerivAt_g1_time ht (z 2))
  have hfun : (fun τ : ℝ => g1 τ (z 0) * g1 τ (z 1) * g1 τ (z 2)) = fun τ => G τ z := by
    ext τ; unfold G; simp [Fin.prod_univ_three, mul_assoc]
  rw [hfun] at h3
  refine h3.congr_deriv ?_
  unfold ΔG
  simp_rw [ΔG_term_eq_prod]
  simp [Fin.sum_univ_three, Fin.prod_univ_three]
  ring

private noncomputable def P (h : Space → ℝ) (t : ℝ) (x : Space) : ℝ :=
  ∫ z : Space, G t z * h (x + z)

private noncomputable def I (h : Space → ℝ) (x : Space) : ℝ :=
  ∫ t in Ioc (0 : ℝ) 1, P h t x

private theorem integrable_G_mul_bounded {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) {t : ℝ} (ht : 0 < t) (x : Space) :
    Integrable (fun z : Space => G t z * h (x + z)) := by
  refine ((integrable_G ht).const_mul M).mono' ?_ (ae_of_all _ fun z => ?_)
  · exact ((contDiff_G ht).continuous.mul (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (G_pos ht z), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hb (x + z)) (G_pos ht z).le

private theorem abs_P_le {h : Space → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y, |h y| ≤ M) {t : ℝ} (ht : 0 < t) (x : Space) :
    |P h t x| ≤ M := by
  unfold P
  calc |∫ z : Space, G t z * h (x + z)|
      = ‖∫ z : Space, G t z * h (x + z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Space, ‖G t z * h (x + z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : Space, M * G t z := by
        by_cases hint : Integrable (fun z : Space => ‖G t z * h (x + z)‖)
        · apply integral_mono hint ((integrable_G ht).const_mul M)
          intro z
          dsimp only
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (G_pos ht z), mul_comm M]
          exact mul_le_mul_of_nonneg_left (hb _) (G_pos ht z).le
        · rw [integral_undef hint]
          exact integral_nonneg fun z => mul_nonneg hM (G_pos ht z).le
    _ = M := by rw [integral_const_mul, integral_G ht, mul_one]

private theorem P_eq_sub (h : Space → ℝ) (t : ℝ) (x : Space) :
    P h t x = ∫ y : Space, G t (y - x) * h y := by
  unfold P
  have h1 := integral_add_left_eq_self (μ := volume) (fun y : Space => G t (y - x) * h y) x
  simpa [add_sub_cancel_left] using h1

private theorem P_scale (h : Space → ℝ) {t : ℝ} (ht : 0 < t) (x : Space) :
    P h t x = ∫ w : Space, G 1 w * h (x + Real.sqrt t • w) := by
  unfold P
  have hsq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hcomp := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure Space))
    (fun z : Space => G t z * h (x + z)) (Real.sqrt t) (hR := hsq_pos.le)
  rw [finrank_euclideanSpace_fin] at hcomp
  have hGscale (w : Space) : (Real.sqrt t) ^ 3 * G t (Real.sqrt t • w) = G 1 w := by
    unfold G g1
    have hsq1 : Real.sqrt (4 * Real.pi * t) = Real.sqrt t * Real.sqrt (4 * Real.pi * 1) := by
      rw [mul_one, ← Real.sqrt_mul ht.le]
      congr 1; ring
    have hterm (i : Fin 3) : Real.sqrt t *
        ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-((Real.sqrt t • w) i) ^ 2 / (4 * t))) =
        (Real.sqrt (4 * Real.pi * 1))⁻¹ * Real.exp (-(w i) ^ 2 / (4 * 1)) := by
      have hwi : ((Real.sqrt t • w) i) ^ 2 = t * (w i) ^ 2 := by
        simp [mul_pow, Real.sq_sqrt ht.le]
      rw [hwi, hsq1]
      have hrat : -(t * (w i) ^ 2) / (4 * t) = -(w i) ^ 2 / (4 * 1) := by
        field_simp [ht.ne']
      rw [hrat]
      have hne1 : Real.sqrt t ≠ 0 := hsq_pos.ne'
      have hne2 : Real.sqrt (4 * Real.pi * 1) ≠ 0 := Real.sqrt_ne_zero'.mpr (by positivity)
      field_simp [hne1, hne2]
    calc (Real.sqrt t) ^ 3 * ∏ i : Fin 3,
            ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-((Real.sqrt t • w) i) ^ 2 / (4 * t)))
        = ∏ i : Fin 3, (Real.sqrt t *
            ((Real.sqrt (4 * Real.pi * t))⁻¹ * Real.exp (-((Real.sqrt t • w) i) ^ 2 / (4 * t)))) := by
          simp [Fin.prod_univ_three]; ring
      _ = ∏ i : Fin 3, ((Real.sqrt (4 * Real.pi * 1))⁻¹ * Real.exp (-(w i) ^ 2 / (4 * 1))) :=
          Finset.prod_congr rfl fun i _ => hterm i
  have hinv : (Real.sqrt t ^ 3)⁻¹ * (∫ z : Space, G t z * h (x + z)) =
      ∫ w : Space, G t (Real.sqrt t • w) * h (x + Real.sqrt t • w) := by
    simpa [smul_eq_mul] using hcomp.symm
  have hmul := congrArg ((Real.sqrt t) ^ 3 * ·) hinv
  have hne3 : (Real.sqrt t) ^ 3 ≠ 0 := pow_ne_zero 3 hsq_pos.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hne3, one_mul, ← integral_const_mul] at hmul
  rw [hmul]
  apply integral_congr_ae
  filter_upwards with w
  rw [← mul_assoc, hGscale w]

private theorem tendsto_P_zero_seq {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) (x : Space) :
    Tendsto (fun n : ℕ => P h (1 / ((n : ℝ) + 2)) x) atTop (𝓝 (h x)) := by
  have htn (n : ℕ) : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have heq : (fun n : ℕ => P h (1 / ((n : ℝ) + 2)) x) =
      fun n : ℕ => ∫ w : Space, G 1 w * h (x + Real.sqrt (1 / ((n : ℝ) + 2)) • w) := by
    funext n
    exact P_scale h (htn n) x
  rw [heq]
  have hlim : Tendsto (fun n : ℕ => ∫ w : Space, G 1 w * h (x + Real.sqrt (1 / ((n : ℝ) + 2)) • w))
      atTop (𝓝 (∫ w : Space, G 1 w * h x)) := by
    apply tendsto_integral_of_dominated_convergence (fun w => M * G 1 w)
    · intro n
      have hsmul : Continuous (fun w : Space => x + Real.sqrt (1 / ((n : ℝ) + 2)) • w) :=
        continuous_const.add ((continuous_const : Continuous (fun _ : Space => Real.sqrt (1 / ((n : ℝ) + 2)))).smul continuous_id)
      exact ((contDiff_G one_pos).continuous.mul (hc.comp hsmul)).aestronglyMeasurable
    · exact (integrable_G one_pos).const_mul M
    · intro n
      refine ae_of_all _ fun w => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (G_pos one_pos w), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hb _) (G_pos one_pos w).le
    · refine ae_of_all _ fun w => ?_
      have hseq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => by
          simp [Function.comp_def]; push_cast; ring
      have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (1 / ((n : ℝ) + 2))) atTop (𝓝 0) := by
        have h1 := (Real.continuous_sqrt.tendsto 0).comp hseq
        rw [Real.sqrt_zero] at h1
        exact h1
      have harg : Tendsto (fun n : ℕ => x + Real.sqrt (1 / ((n : ℝ) + 2)) • w) atTop (𝓝 x) := by
        have h1 := (tendsto_const_nhds (x := x)).add (hsqrt.smul (tendsto_const_nhds (x := w)))
        simpa using h1
      exact (tendsto_const_nhds (x := G 1 w)).mul ((hc.tendsto x).comp harg)
  simpa [integral_mul_const, integral_G one_pos] using hlim

private theorem hasDerivAt_P_time_raw {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) {t : ℝ} (ht : 0 < t) (x : Space) :
    HasDerivAt (fun τ : ℝ => P h τ x) (∫ z : Space, ΔG t z * h (x + z)) t := by
  let a := t / 2
  let b := 2 * t
  have ha : 0 < a := half_pos ht
  have hb_pos : 0 < b := by positivity
  have hs : Icc a b ∈ 𝓝 t := Icc_mem_nhds (by dsimp [a]; linarith) (by dsimp [b]; linarith)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  let C1 := (Real.sqrt (4 * Real.pi * a))⁻¹
  let C2 := 1 / (4 * a ^ 2) * (2 / (4 * b)⁻¹) + 1 / (2 * a)
  let bound (z : Space) : ℝ :=
    M * (3 * (C1 ^ 3 * C2)) * ∏ i : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z i) ^ 2)
  have hbound_int : Integrable bound := by
    have hprod : Integrable (fun z : Space => ∏ i : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z i) ^ 2)) :=
      integrable_prod3 fun _ => integrable_exp_neg_mul_sq (by positivity)
    exact hprod.const_mul _
  have hdom : ∀ᵐ z : Space ∂volume, ∀ τ ∈ Icc a b, ‖ΔG τ z * h (x + z)‖ ≤ bound z := by
    refine ae_of_all _ fun z τ ⟨hτa, hτb⟩ => ?_
    have hτ : 0 < τ := lt_of_lt_of_le ha hτa
    rw [Real.norm_eq_abs, abs_mul]
    have hG_le (j : Fin 3) : g1 τ (z j) ≤ C1 * Real.exp (-(4 * b)⁻¹ * (z j) ^ 2) := by
      unfold g1
      apply mul_le_mul
      · exact inv_anti₀ (Real.sqrt_pos.mpr (by positivity))
          (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
      · apply Real.exp_le_exp.mpr
        have h1 : (4 * b)⁻¹ ≤ (4 * τ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
        have h2 : -(z j ^ 2) / (4 * τ) = -(4 * τ)⁻¹ * (z j) ^ 2 := by ring
        rw [h2]
        nlinarith [sq_nonneg (z j)]
      · exact Real.exp_nonneg _
      · positivity
    have hG_le2 (j : Fin 3) : g1 τ (z j) ≤ C1 * Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by
      refine (hG_le j).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (z j), inv_pos.mpr (show 0 < 4 * b by positivity)])
    have hterm_le (i : Fin 3) : |((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) * G τ z| ≤
        (C1 ^ 3 * C2) * ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by
      rw [ΔG_term_eq_prod, Finset.abs_prod]
      have hfactor (j : Fin 3) :
          |if j = i then g1'' τ (z j) else g1 τ (z j)| ≤
            (if j = i then C1 * C2 else C1) * Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by
        split_ifs
        · unfold g1''
          rw [abs_mul, abs_of_pos (g1_pos hτ _)]
          have htri : |z j ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤
              z j ^ 2 / (4 * a ^ 2) + 1 / (2 * a) := by
            have hsub : |z j ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| ≤
                |z j ^ 2 / (4 * τ ^ 2)| + |1 / (2 * τ)| := abs_sub _ _
            have ha1 : |z j ^ 2 / (4 * τ ^ 2)| = z j ^ 2 / (4 * τ ^ 2) :=
              abs_of_nonneg (by positivity)
            have ha2 : |1 / (2 * τ)| = 1 / (2 * τ) := abs_of_pos (by positivity)
            have h1 : z j ^ 2 / (4 * τ ^ 2) ≤ z j ^ 2 / (4 * a ^ 2) :=
              div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
            have h2 : 1 / (2 * τ) ≤ 1 / (2 * a) :=
              div_le_div_of_nonneg_left zero_le_one (by positivity) (by linarith)
            linarith
          have hprod1 := mul_le_mul htri (hG_le j) (g1_pos hτ _).le (by positivity)
          have hsq := sq_mul_exp_neg_le (show 0 < (4 * b)⁻¹ by positivity) (z j)
          have hexp2 : Real.exp (-(4 * b)⁻¹ * (z j) ^ 2) ≤
              Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) :=
            Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (z j), inv_pos.mpr (show 0 < 4 * b by positivity)])
          calc |z j ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)| * g1 τ (z j)
              ≤ (z j ^ 2 / (4 * a ^ 2) + 1 / (2 * a)) * (C1 * Real.exp (-(4 * b)⁻¹ * (z j) ^ 2)) :=
                hprod1
            _ = C1 * ((1 / (4 * a ^ 2)) * (z j ^ 2 * Real.exp (-(4 * b)⁻¹ * (z j) ^ 2)) +
                  (1 / (2 * a)) * Real.exp (-(4 * b)⁻¹ * (z j) ^ 2)) := by ring
            _ ≤ C1 * ((1 / (4 * a ^ 2)) * ((2 / (4 * b)⁻¹) * Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2)) +
                  (1 / (2 * a)) * Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact add_le_add (mul_le_mul_of_nonneg_left hsq (by positivity))
                  (mul_le_mul_of_nonneg_left hexp2 (by positivity))
            _ = (C1 * C2) * Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by dsimp [C2]; ring
        · rw [abs_of_pos (g1_pos hτ _)]
          exact hG_le2 j
      calc ∏ j : Fin 3, |if j = i then g1'' τ (z j) else g1 τ (z j)|
          ≤ ∏ j : Fin 3, ((if j = i then C1 * C2 else C1) *
              Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2)) :=
            Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hfactor j)
        _ = (∏ j : Fin 3, (if j = i then C1 * C2 else C1)) *
              ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) :=
            Finset.prod_mul_distrib
        _ = (C1 ^ 3 * C2) * ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by
            congr 1; fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
    have hΔ_le : |ΔG τ z| ≤ 3 * (C1 ^ 3 * C2) *
        ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) := by
      unfold ΔG
      calc |∑ i : Fin 3, ((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) * G τ z|
          ≤ ∑ i : Fin 3, |((z i) ^ 2 / (4 * τ ^ 2) - 1 / (2 * τ)) * G τ z| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 3, (C1 ^ 3 * C2) * ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2) :=
            Finset.sum_le_sum fun i _ => hterm_le i
        _ = _ := by simp [Fin.sum_univ_three]; ring
    dsimp [bound]
    calc |ΔG τ z| * |h (x + z)|
        ≤ (3 * (C1 ^ 3 * C2) * ∏ j : Fin 3, Real.exp (-((4 * b)⁻¹ / 2) * (z j) ^ 2)) * M :=
          mul_le_mul hΔ_le (hb _) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hmeas_F : ∀ᶠ τ in 𝓝 t, AEStronglyMeasurable (fun z : Space => G τ z * h (x + z)) volume := by
    filter_upwards [hs] with τ ⟨hτa, _⟩
    have hτ : 0 < τ := lt_of_lt_of_le ha hτa
    exact ((contDiff_G hτ).continuous.mul
      (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hmeas_D : AEStronglyMeasurable (fun z : Space => ΔG t z * h (x + z)) volume := by
    have hΔcont : Continuous (ΔG t) := by
      unfold ΔG
      refine continuous_finset_sum _ fun i _ => ?_
      have hcoord : Continuous (fun z : Space => z i) := (EuclideanSpace.proj i).continuous
      exact (((hcoord.pow 2).div_const _).sub continuous_const).mul (contDiff_G ht).continuous
    exact (hΔcont.mul (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hmeas_F
    (integrable_G_mul_bounded hc hb ht x) hmeas_D hdom hbound_int
    (ae_of_all _ fun z τ ⟨hτa, _⟩ => (hasDerivAt_G_time (lt_of_lt_of_le ha hτa) z).mul_const _)
  exact hres.2

private noncomputable def bump3 : ContDiffBump (0 : Space) :=
  ⟨1, 2, by norm_num, by norm_num⟩

private theorem integral_ΔG_eq_P_laplacian {u : Space → ℝ} (hu : IsBoundedSol u)
    {t : ℝ} (ht : 0 < t) (x : Space) :
    (∫ z : Space, ΔG t z * u (x + z)) = P (Δ u) t x := by
  let u_s (z : Space) : ℝ := u (x + z)
  have hu_s : ContDiff ℝ 2 u_s := hu.regular.comp (contDiff_const.add contDiff_id)
  have hu_le : ∀ z, |u_s z| ≤ 1 := fun z => abs_le_one_of_bounded_sol hu (x + z)
  have hΔ_le : ∀ z, |(Δ u) (x + z)| ≤ 2 := fun z => by
    have hpde : (Δ u) (x + z) = u (x + z) ^ 3 - u (x + z) := by linarith [hu.solution (x + z)]
    rw [hpde]
    have h1 := abs_le_one_of_bounded_sol hu (x + z)
    calc |u (x + z) ^ 3 - u (x + z)| ≤ |u (x + z) ^ 3| + |u (x + z)| := abs_sub _ _
      _ ≤ 1 ^ 3 + 1 := add_le_add (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3) h1
      _ = 2 := by norm_num
  have hpd_s (i : Fin 3) (z : Space) : pd3 u_s i z = pd3 u i (x + z) := by
    have h1 := line_deriv3 (hu_s.of_le (by norm_num)) z (e3 i) 0
    have h2 := line_deriv3 (hu.regular.of_le (by norm_num)) (x + z) (e3 i) 0
    have heq : (fun s : ℝ => u_s (z + s • e3 i)) = fun s => u ((x + z) + s • e3 i) := by
      ext s; dsimp [u_s]; rw [add_assoc]
    rw [heq] at h1
    simpa [pd3] using h1.unique h2
  have hpd2_s (i : Fin 3) (z : Space) : pd32 u_s i i z = pd32 u i i (x + z) := by
    unfold pd32
    have heq : pd3 u_s i = fun w => pd3 u i (x + w) := funext (hpd_s i)
    rw [heq]
    have h1c : ContDiff ℝ 1 (pd3 u i) :=
      (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have h1 := line_deriv3 h1c (x + z) (e3 i) 0
    have h2 := line_deriv3 (h1c.comp ((contDiff_const (c := x)).add contDiff_id)) z (e3 i) 0
    have heq2 : (fun s : ℝ => pd3 u i (x + (z + s • e3 i))) =
        fun s => pd3 u i ((x + z) + s • e3 i) := by ext s; rw [add_assoc]
    dsimp only [Function.comp_def, id_eq] at h2
    rw [heq2] at h2
    simpa [pd3] using h2.unique h1
  obtain ⟨M1, hM1⟩ := (bump3.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    ((bump3.contDiff (n := 2)).continuous_fderiv (by norm_num))
  have hM1_0 : 0 ≤ M1 := (norm_nonneg _).trans (hM1 0)
  have hM2_ex : ∃ M2 : ℝ, 0 ≤ M2 ∧ ∀ i : Fin 3, ∀ w : Space, |pd32 bump3 i i w| ≤ M2 := by
    have hcomp (i : Fin 3) : HasCompactSupport (pd32 bump3 i i) :=
      ((bump3.hasCompactSupport.fderiv_apply ℝ (e3 i)).fderiv_apply ℝ (e3 i))
    have hcont (i : Fin 3) : Continuous (pd32 bump3 i i) :=
      ((((bump3.contDiff (n := 2)).fderiv_right (by norm_num)).clm_apply
        contDiff_const).continuous_fderiv one_ne_zero).clm_apply continuous_const
    obtain ⟨B0, hB0⟩ := (hcomp 0).exists_bound_of_continuous (hcont 0)
    obtain ⟨B1, hB1⟩ := (hcomp 1).exists_bound_of_continuous (hcont 1)
    obtain ⟨B2, hB2⟩ := (hcomp 2).exists_bound_of_continuous (hcont 2)
    refine ⟨max 0 (max B0 (max B1 B2)), le_max_left _ _, fun i w => ?_⟩
    fin_cases i
    · exact (hB0 w).trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact (hB1 w).trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _))
    · exact (hB2 w).trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _))
  obtain ⟨M2, hM2_0, hM2⟩ := hM2_ex
  let r (n : ℕ) : ℝ := (n : ℝ) + 1
  have hr_pos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hr_ge1 (n : ℕ) : 1 ≤ r n := by dsimp [r]; linarith [Nat.cast_nonneg (α := ℝ) n]
  let χ (n : ℕ) (z : Space) : ℝ := bump3 ((r n)⁻¹ • z)
  have hχ_c2 (n : ℕ) : ContDiff ℝ 2 (χ n) :=
    (bump3.contDiff (n := 2)).comp (contDiff_id.const_smul _)
  have hχ_supp (n : ℕ) : HasCompactSupport (χ n) :=
    bump3.hasCompactSupport.comp_smul (inv_ne_zero (hr_pos n).ne')
  have hχ_pd (n : ℕ) (i : Fin 3) (z : Space) :
      pd3 (χ n) i z = (r n)⁻¹ * pd3 bump3 i ((r n)⁻¹ • z) := by
    have h1 := line_deriv3 ((hχ_c2 n).of_le (by norm_num)) z (e3 i) 0
    have h2 : HasDerivAt (fun s : ℝ => bump3 ((r n)⁻¹ • z + s • ((r n)⁻¹ • e3 i)))
        (fderiv ℝ bump3 ((r n)⁻¹ • z) ((r n)⁻¹ • e3 i)) 0 := by
      simpa using line_deriv3 (bump3.contDiff (n := 1)) ((r n)⁻¹ • z) ((r n)⁻¹ • e3 i) 0
    have heq : (fun s : ℝ => χ n (z + s • e3 i)) =
        fun s => bump3 ((r n)⁻¹ • z + s • ((r n)⁻¹ • e3 i)) := by
      ext s; dsimp [χ]; rw [smul_add, smul_comm]
    rw [heq] at h1
    have huq := h1.unique h2
    simp only [zero_smul, add_zero, map_smul, smul_eq_mul] at huq
    exact huq
  have hχ_pd2 (n : ℕ) (i : Fin 3) (z : Space) :
      pd32 (χ n) i i z = (r n)⁻¹ ^ 2 * pd32 bump3 i i ((r n)⁻¹ • z) := by
    unfold pd32
    have heq : pd3 (χ n) i = fun w => (r n)⁻¹ * pd3 bump3 i ((r n)⁻¹ • w) := funext (hχ_pd n i)
    rw [heq]
    have hbc1 : ContDiff ℝ 1 (pd3 bump3 i) :=
      ((bump3.contDiff (n := 2)).fderiv_right (by norm_num)).clm_apply contDiff_const
    have h1 := line_deriv3 ((contDiff_const (c := (r n)⁻¹)).mul (hbc1.comp (contDiff_id.const_smul (r n)⁻¹))) z (e3 i) 0
    have h2 : HasDerivAt (fun s : ℝ => (r n)⁻¹ * pd3 bump3 i ((r n)⁻¹ • z + s • ((r n)⁻¹ • e3 i)))
        ((r n)⁻¹ * fderiv ℝ (pd3 bump3 i) ((r n)⁻¹ • z) ((r n)⁻¹ • e3 i)) 0 := by
      simpa using (line_deriv3 hbc1 ((r n)⁻¹ • z) ((r n)⁻¹ • e3 i) 0).const_mul (r n)⁻¹
    have heq2 : (fun s : ℝ => (r n)⁻¹ * pd3 bump3 i ((r n)⁻¹ • (z + s • e3 i))) =
        fun s => (r n)⁻¹ * pd3 bump3 i ((r n)⁻¹ • z + s • ((r n)⁻¹ • e3 i)) := by
      ext s; rw [smul_add, smul_comm]
    dsimp only [Function.comp_def, id_eq] at h1
    rw [heq2] at h1
    have huq := h1.unique h2
    simp only [zero_smul, add_zero, map_smul, smul_eq_mul] at huq
    unfold pd3 at huq ⊢
    rw [huq]
    ring
  have hχ_pd_le (n : ℕ) (i : Fin 3) (z : Space) : |pd3 (χ n) i z| ≤ M1 / r n := by
    rw [hχ_pd, abs_mul, abs_of_pos (inv_pos.mpr (hr_pos n)), div_eq_inv_mul]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (hr_pos n).le)
    calc |pd3 bump3 i ((r n)⁻¹ • z)|
        ≤ ‖fderiv ℝ bump3 ((r n)⁻¹ • z)‖ * ‖e3 i‖ := (fderiv ℝ bump3 _).le_opNorm _
      _ ≤ M1 := by simpa [e3] using hM1 ((r n)⁻¹ • z)
  have hχ_pd2_le (n : ℕ) (i : Fin 3) (z : Space) : |pd32 (χ n) i i z| ≤ M2 / (r n) ^ 2 := by
    rw [hχ_pd2, abs_mul, abs_of_pos (pow_pos (inv_pos.mpr (hr_pos n)) 2), inv_pow, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_left (hM2 i _) (by positivity)
  have hIBP_n (n : ℕ) :
      (∫ z : Space, (G t z * χ n z) * (Δ u) (x + z)) =
        ∫ z : Space, (ΔG t z * χ n z +
          2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z +
          G t z * ∑ i : Fin 3, pd32 (χ n) i i z) * u (x + z) := by
    let φ (z : Space) : ℝ := G t z * χ n z
    have hφ_c2 : ContDiff ℝ 2 φ := (contDiff_G ht).mul (hχ_c2 n)
    have hφ_supp : HasCompactSupport φ := (hχ_supp n).mul_left
    have hφ_pd (i : Fin 3) (z : Space) :
        pd3 φ i z = dG i t z * χ n z + G t z * pd3 (χ n) i z := by
      have h1 := line_deriv3 (hφ_c2.of_le (by norm_num)) z (e3 i) 0
      have h2 := (line_deriv3 ((contDiff_G ht).of_le (by norm_num)) z (e3 i) 0).mul
        (line_deriv3 ((hχ_c2 n).of_le (by norm_num)) z (e3 i) 0)
      have huq := h1.unique h2
      simp only [zero_smul, add_zero] at huq
      change pd3 φ i z = pd3 (G t) i z * χ n z + G t z * pd3 (χ n) i z at huq
      rw [huq, pd3_G ht]
    have hφ_pd2 (i : Fin 3) (z : Space) :
        pd32 φ i i z = ((z i) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * G t z * χ n z +
          2 * dG i t z * pd3 (χ n) i z + G t z * pd32 (χ n) i i z := by
      unfold pd32
      have heq : pd3 φ i = fun w => pd3 (G t) i w * χ n w + G t w * pd3 (χ n) i w := by
        ext w; rw [hφ_pd, pd3_G ht]
      rw [heq]
      have hG1 : ContDiff ℝ 1 (pd3 (G t) i) :=
        ((contDiff_G ht).fderiv_right (by norm_num)).clm_apply contDiff_const
      have hχ1 : ContDiff ℝ 1 (pd3 (χ n) i) :=
        ((hχ_c2 n).fderiv_right (by norm_num)).clm_apply contDiff_const
      have h1 := line_deriv3 ((hG1.mul ((hχ_c2 n).of_le (by norm_num))).add
        (((contDiff_G ht).of_le (by norm_num)).mul hχ1)) z (e3 i) 0
      have h2 := ((line_deriv3 hG1 z (e3 i) 0).mul
        (line_deriv3 ((hχ_c2 n).of_le (by norm_num)) z (e3 i) 0)).add
        ((line_deriv3 ((contDiff_G ht).of_le (by norm_num)) z (e3 i) 0).mul
          (line_deriv3 hχ1 z (e3 i) 0))
      have huq := h1.unique h2
      simp only [zero_smul, add_zero] at huq
      change pd3 (fun w => pd3 (G t) i w * χ n w + G t w * pd3 (χ n) i w) i z =
        pd32 (G t) i i z * χ n z + pd3 (G t) i z * pd3 (χ n) i z +
        (pd3 (G t) i z * pd3 (χ n) i z + G t z * pd32 (χ n) i i z) at huq
      rw [huq, pd32_G ht, pd3_G ht]
      unfold pd32
      ring
    have hterm (i : Fin 3) :
        (∫ z : Space, φ z * pd32 u_s i i z) = ∫ z : Space, pd32 φ i i z * u_s z := by
      have hφ_c1 : ContDiff ℝ 1 φ := hφ_c2.of_le (by norm_num)
      have hφ1_c1 : ContDiff ℝ 1 (pd3 φ i) :=
        (hφ_c2.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hφ1_supp : HasCompactSupport (pd3 φ i) := hφ_supp.fderiv_apply ℝ (e3 i)
      have hφ2_supp : HasCompactSupport (pd32 φ i i) := hφ1_supp.fderiv_apply ℝ (e3 i)
      have hu1_c1 : ContDiff ℝ 1 (pd3 u_s i) :=
        (hu_s.fderiv_right (by norm_num)).clm_apply contDiff_const
      have hInt1 : Integrable (fun z => pd3 φ i z * pd3 u_s i z) :=
        (hφ1_c1.continuous.mul hu1_c1.continuous).integrable_of_hasCompactSupport
          (hφ1_supp.mul_right)
      have hInt2 : Integrable (fun z => φ z * pd32 u_s i i z) :=
        (hφ_c1.continuous.mul ((hu1_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
          (hφ_supp.mul_right)
      have hInt3 : Integrable (fun z => φ z * pd3 u_s i z) :=
        (hφ_c1.continuous.mul hu1_c1.continuous).integrable_of_hasCompactSupport
          (hφ_supp.mul_right)
      have hInt4 : Integrable (fun z => pd32 φ i i z * u_s z) :=
        (((hφ1_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
          hu_s.continuous).integrable_of_hasCompactSupport (hφ2_supp.mul_right)
      have hInt5 : Integrable (fun z => pd3 φ i z * u_s z) :=
        (hφ1_c1.continuous.mul hu_s.continuous).integrable_of_hasCompactSupport
          (hφ1_supp.mul_right)
      have hibp1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e3 i)
        hInt1 hInt2 hInt3
        (fun z _ => hφ_c1.differentiable one_ne_zero z)
        (fun z _ => hu1_c1.differentiable one_ne_zero z)
      have hibp2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := e3 i)
        hInt4 hInt1 hInt5
        (fun z _ => hφ1_c1.differentiable one_ne_zero z)
        (fun z _ => (hu_s.of_le (by norm_num)).differentiable one_ne_zero z)
      change (∫ z, φ z * pd32 u_s i i z) = -∫ z, pd3 φ i z * pd3 u_s i z at hibp1
      change (∫ z, pd3 φ i z * pd3 u_s i z) = -∫ z, pd32 φ i i z * u_s z at hibp2
      linarith
    have hL_int (i : Fin 3) : Integrable (fun z => φ z * pd32 u_s i i z) :=
      (hφ_c2.continuous.mul
        ((((hu_s.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hφ_supp.mul_right)
    have hR_int (i : Fin 3) : Integrable (fun z => pd32 φ i i z * u_s z) :=
      (((((hφ_c2.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const).mul
        hu_s.continuous).integrable_of_hasCompactSupport
        (((hφ_supp.fderiv_apply ℝ (e3 i)).fderiv_apply ℝ (e3 i)).mul_right)
    calc (∫ z : Space, (G t z * χ n z) * (Δ u) (x + z))
        = ∫ z : Space, ∑ i : Fin 3, φ z * pd32 u_s i i z := by
          apply integral_congr_ae
          filter_upwards with z
          rw [laplacian_eq_sum_pd32 hu.regular (x + z), mul_sum]
          apply sum_congr rfl
          intro i _
          rw [hpd2_s i z]
      _ = ∑ i : Fin 3, ∫ z : Space, φ z * pd32 u_s i i z :=
          integral_finset_sum _ fun i _ => hL_int i
      _ = ∑ i : Fin 3, ∫ z : Space, pd32 φ i i z * u_s z :=
          sum_congr rfl fun i _ => hterm i
      _ = ∫ z : Space, ∑ i : Fin 3, pd32 φ i i z * u_s z :=
          (integral_finset_sum _ fun i _ => hR_int i).symm
      _ = _ := by
          apply integral_congr_ae
          filter_upwards with z
          rw [← sum_mul]
          congr 1
          simp_rw [hφ_pd2]
          unfold ΔG
          simp only [Fin.sum_univ_three]
          ring
  have hχ_tendsto (z : Space) : Tendsto (fun n : ℕ => χ n z) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil ‖z‖)] with n hn
    symm
    apply bump3.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (hr_pos n), inv_mul_eq_div, div_le_iff₀ (hr_pos n)]
    change ‖z‖ ≤ 1 * r n
    have hceil : ‖z‖ ≤ (Nat.ceil ‖z‖ : ℝ) := Nat.le_ceil ‖z‖
    have hnat : (Nat.ceil ‖z‖ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
    dsimp [r]
    linarith
  have hL_lim : Tendsto (fun n : ℕ => ∫ z : Space, (G t z * χ n z) * (Δ u) (x + z))
      atTop (𝓝 (P (Δ u) t x)) := by
    unfold P
    apply tendsto_integral_of_dominated_convergence (fun z => 2 * G t z)
    · intro n
      have hΔcont : Continuous (Δ u) := by
        have heq : Δ u = fun y => u y ^ 3 - u y := funext fun y => by linarith [hu.solution y]
        rw [heq]
        exact (hu.regular.continuous.pow 3).sub hu.regular.continuous
      exact (((contDiff_G ht).continuous.mul (hχ_c2 n).continuous).mul
        (hΔcont.comp (continuous_const.add continuous_id))).aestronglyMeasurable
    · exact (integrable_G ht).const_mul 2
    · intro n
      refine ae_of_all _ fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (G_pos ht z),
        abs_of_nonneg bump3.nonneg]
      have hχ1 : χ n z ≤ 1 := bump3.le_one
      have h2 := hΔ_le z
      have hprod1 : G t z * χ n z ≤ G t z :=
        mul_le_of_le_one_right (G_pos ht z).le hχ1
      have hprod2 : G t z * χ n z * |Δ u (x + z)| ≤ G t z * 2 :=
        mul_le_mul hprod1 h2 (abs_nonneg _) (G_pos ht z).le
      change G t z * χ n z * |Δ u (x + z)| ≤ 2 * G t z
      linarith
    · refine ae_of_all _ fun z => ?_
      have := ((tendsto_const_nhds (x := G t z)).mul (hχ_tendsto z)).mul (tendsto_const_nhds (x := Δ u (x + z)))
      simpa using this
  have hR_lim : Tendsto (fun n : ℕ => ∫ z : Space, (ΔG t z * χ n z +
      2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z +
      G t z * ∑ i : Fin 3, pd32 (χ n) i i z) * u (x + z))
      atTop (𝓝 (∫ z : Space, ΔG t z * u (x + z))) := by
    let bnd (z : Space) : ℝ :=
      |ΔG t z| + 2 * M1 * ∑ i : Fin 3, |dG i t z| + 3 * M2 * G t z
    have hbnd_int : Integrable bnd := by
      refine (((integrable_ΔG ht).norm).add ?_).add ((integrable_G ht).const_mul _)
      exact (integrable_finset_sum _ fun i _ => (integrable_dG i ht).norm).const_mul _
    apply tendsto_integral_of_dominated_convergence bnd
    · intro n
      have hΔG_cont : Continuous (ΔG t) := by
        unfold ΔG
        refine continuous_finset_sum _ fun i _ => ?_
        have hcoord : Continuous (fun z : Space => z i) := (EuclideanSpace.proj i).continuous
        exact (((hcoord.pow 2).div_const _).sub continuous_const).mul (contDiff_G ht).continuous
      have hdG_cont (i : Fin 3) : Continuous (dG i t) := by
        unfold dG
        exact (((EuclideanSpace.proj i).continuous.neg).div_const _).mul (contDiff_G ht).continuous
      have hχ1_cont (i : Fin 3) : Continuous (pd3 (χ n) i) :=
        ((hχ_c2 n).continuous_fderiv (by norm_num)).clm_apply continuous_const
      have hχ2_cont (i : Fin 3) : Continuous (pd32 (χ n) i i) :=
        ((((hχ_c2 n).fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          one_ne_zero).clm_apply continuous_const
      have hcont : Continuous (fun z : Space => (ΔG t z * χ n z +
          2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z +
          G t z * ∑ i : Fin 3, pd32 (χ n) i i z) * u (x + z)) :=
        (((hΔG_cont.mul (hχ_c2 n).continuous).add
          (continuous_const.mul (continuous_finset_sum _ fun i _ => (hdG_cont i).mul (hχ1_cont i)))).add
          ((contDiff_G ht).continuous.mul (continuous_finset_sum _ fun i _ => hχ2_cont i))).mul
          (hu.regular.continuous.comp (continuous_const.add continuous_id))
      exact hcont.aestronglyMeasurable
    · exact hbnd_int
    · intro n
      refine ae_of_all _ fun z => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have hu1 : |u (x + z)| ≤ 1 := hu_le z
      have h1 : |ΔG t z * χ n z| ≤ |ΔG t z| := by
        rw [abs_mul, abs_of_nonneg bump3.nonneg]
        exact mul_le_of_le_one_right (abs_nonneg _) bump3.le_one
      have h2 : |2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z| ≤
          2 * M1 * ∑ i : Fin 3, |dG i t z| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have hs : |∑ i : Fin 3, dG i t z * pd3 (χ n) i z| ≤
            M1 * ∑ i : Fin 3, |dG i t z| := by
          calc |∑ i : Fin 3, dG i t z * pd3 (χ n) i z|
              ≤ ∑ i : Fin 3, |dG i t z * pd3 (χ n) i z| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ i : Fin 3, M1 * |dG i t z| := by
                apply Finset.sum_le_sum; intro i _
                rw [abs_mul, mul_comm M1]
                have hpd : |pd3 (χ n) i z| ≤ M1 :=
                  (hχ_pd_le n i z).trans (div_le_self hM1_0 (hr_ge1 n))
                exact mul_le_mul_of_nonneg_left hpd (abs_nonneg _)
            _ = _ := by rw [← mul_sum]
        linarith
      have h3 : |G t z * ∑ i : Fin 3, pd32 (χ n) i i z| ≤ 3 * M2 * G t z := by
        rw [abs_mul, abs_of_pos (G_pos ht z)]
        have hs : |∑ i : Fin 3, pd32 (χ n) i i z| ≤ 3 * M2 := by
          calc |∑ i : Fin 3, pd32 (χ n) i i z|
              ≤ ∑ i : Fin 3, |pd32 (χ n) i i z| := abs_sum_le_sum_abs _ _
            _ ≤ ∑ _i : Fin 3, M2 := by
                apply Finset.sum_le_sum; intro i _
                exact (hχ_pd2_le n i z).trans
                  (div_le_self hM2_0 (by nlinarith [hr_ge1 n]))
            _ = 3 * M2 := by simp
        have := mul_le_mul_of_nonneg_left hs (G_pos ht z).le
        linarith
      have htot : |ΔG t z * χ n z + 2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z +
          G t z * ∑ i : Fin 3, pd32 (χ n) i i z| ≤ bnd z := by
        dsimp [bnd]
        have ha1 := abs_add_le (ΔG t z * χ n z + 2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z)
          (G t z * ∑ i : Fin 3, pd32 (χ n) i i z)
        have ha2 := abs_add_le (ΔG t z * χ n z) (2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z)
        linarith
      exact (mul_le_of_le_one_right (abs_nonneg _) hu1).trans htot
    · refine ae_of_all _ fun z => ?_
      have h1 : Tendsto (fun n : ℕ => ΔG t z * χ n z) atTop (𝓝 (ΔG t z)) := by
        simpa using tendsto_const_nhds.mul (hχ_tendsto z)
      have hinv0 : Tendsto (fun n : ℕ => (r n)⁻¹) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by simp [r, one_div]
      have hpd0 (i : Fin 3) : Tendsto (fun n : ℕ => pd3 (χ n) i z) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) (by simpa using hinv0.const_mul M1)
        rw [Real.norm_eq_abs]
        simpa [div_eq_mul_inv] using hχ_pd_le n i z
      have hpd20 (i : Fin 3) : Tendsto (fun n : ℕ => pd32 (χ n) i i z) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) (by simpa using (hinv0.pow 2).const_mul M2)
        rw [Real.norm_eq_abs]
        simpa [div_eq_mul_inv, inv_pow] using hχ_pd2_le n i z
      have h2 : Tendsto (fun n : ℕ => 2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z) atTop (𝓝 0) := by
        have hs : Tendsto (fun n : ℕ => ∑ i : Fin 3, dG i t z * pd3 (χ n) i z) atTop (𝓝 0) := by
          simpa using tendsto_finset_sum (Finset.univ : Finset (Fin 3))
            fun i _ => tendsto_const_nhds.mul (hpd0 i)
        simpa using hs.const_mul 2
      have h3 : Tendsto (fun n : ℕ => G t z * ∑ i : Fin 3, pd32 (χ n) i i z) atTop (𝓝 0) := by
        have hs : Tendsto (fun n : ℕ => ∑ i : Fin 3, pd32 (χ n) i i z) atTop (𝓝 0) := by
          simpa using tendsto_finset_sum (Finset.univ : Finset (Fin 3)) fun i _ => hpd20 i
        simpa using hs.const_mul (G t z)
      have hsum := (h1.add h2).add h3
      simpa using hsum.mul tendsto_const_nhds
  have hL_eq : (fun n : ℕ => ∫ z : Space, (G t z * χ n z) * (Δ u) (x + z)) =
      fun n : ℕ => ∫ z : Space, (ΔG t z * χ n z +
        2 * ∑ i : Fin 3, dG i t z * pd3 (χ n) i z +
        G t z * ∑ i : Fin 3, pd32 (χ n) i i z) * u (x + z) := funext hIBP_n
  rw [hL_eq] at hL_lim
  exact tendsto_nhds_unique hR_lim hL_lim

private theorem continuousOn_P_time {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) (x : Space) : ContinuousOn (fun t : ℝ => P h t x) (Ioi 0) := by
  intro t ht
  exact (hasDerivAt_P_time_raw hc hb ht x).continuousAt.continuousWithinAt

private theorem duhamel_u {u : Space → ℝ} (hu : IsBoundedSol u) (x : Space) :
    u x = P u 1 x - I (fun y => u y ^ 3 - u y) x := by
  let F (y : Space) : ℝ := u y ^ 3 - u y
  have hF_eq : Δ u = F := funext fun y => by dsimp [F]; linarith [hu.solution y]
  have hF_cont : Continuous F := (hu.regular.continuous.pow 3).sub hu.regular.continuous
  have hF_le : ∀ y, |F y| ≤ 2 := fun y => by
    have h1 := abs_le_one_of_bounded_sol hu y
    calc |u y ^ 3 - u y| ≤ |u y ^ 3| + |u y| := abs_sub _ _
      _ ≤ 1 ^ 3 + 1 := add_le_add (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3) h1
      _ = 2 := by norm_num
  have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt (fun τ => P u τ x) (P F t x) t := by
    have h1 := hasDerivAt_P_time_raw hu.regular.continuous (abs_le_one_of_bounded_sol hu) ht x
    rwa [integral_ΔG_eq_P_laplacian hu ht x, hF_eq] at h1
  let a (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have ha_pos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha_le1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hFTC (n : ℕ) : P u 1 x - P u (a n) x = ∫ t in Ioc (a n) 1, P F t x := by
    rw [← intervalIntegral.integral_of_le (ha_le1 n)]
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => P u τ x) ?_ ?_
    · intro t ht
      rw [uIcc_of_le (ha_le1 n)] at ht
      exact hderiv t (lt_of_lt_of_le (ha_pos n) ht.1)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (ha_le1 n)]
      exact (continuousOn_P_time hF_cont hF_le x).mono fun t ht =>
        lt_of_lt_of_le (ha_pos n) ht.1
  have hL_lim : Tendsto (fun n : ℕ => P u 1 x - P u (a n) x) atTop (𝓝 (P u 1 x - u x)) :=
    tendsto_const_nhds.sub (tendsto_P_zero_seq hu.regular.continuous (abs_le_one_of_bounded_sol hu) x)
  have hR_lim : Tendsto (fun n : ℕ => ∫ t in Ioc (a n) 1, P F t x) atTop (𝓝 (I F x)) := by
    unfold I
    have heq (n : ℕ) : (∫ t in Ioc (a n) 1, P F t x) =
        ∫ t in Ioc (0 : ℝ) 1, (Ioc (a n) 1).indicator (fun τ => P F τ x) t := by
      rw [setIntegral_indicator measurableSet_Ioc, inter_eq_right.mpr (Ioc_subset_Ioc_left (ha_pos n).le)]
    simp_rw [heq]
    apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (2 : ℝ))
    · intro n
      have hm : AEStronglyMeasurable (fun τ => P F τ x) (volume.restrict (Ioc (0 : ℝ) 1)) :=
        ((continuousOn_P_time hF_cont hF_le x).mono Ioc_subset_Ioi_self).aestronglyMeasurable
          measurableSet_Ioc
      exact hm.indicator measurableSet_Ioc
    · exact integrableOn_const (by simp)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      by_cases hmem : t ∈ Ioc (a n) 1
      · rw [indicator_of_mem hmem, Real.norm_eq_abs]
        exact abs_P_le (by norm_num) hF_le ht.1 x
      · rw [indicator_of_notMem hmem, norm_zero]
        norm_num
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      refine tendsto_const_nhds.congr' ?_
      have ha0 : Tendsto a atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)).congr fun n => by
          dsimp [a, Function.comp_def]; push_cast; ring
      filter_upwards [ha0 (gt_mem_nhds ht.1)] with n hn
      symm
      have hmem : t ∈ Ioc (a n) 1 := ⟨hn, ht.2⟩
      exact indicator_of_mem hmem _
  have heq_lim := tendsto_nhds_unique (hL_lim.congr hFTC) hR_lim
  linarith

private theorem hasDerivAt_P_of_bounded {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) {t : ℝ} (ht : 0 < t) (i : Fin 3) (x : Space) :
    HasDerivAt (fun s : ℝ => P h t (x + s • e3 i))
      (∫ z : Space, (-dG i t z) * h (x + z)) 0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have heq : (fun s : ℝ => P h t (x + s • e3 i)) =
      fun s => ∫ y : Space, G t ((y - x) - s • e3 i) * h y := by
    ext s
    rw [P_eq_sub]
    apply integral_congr_ae
    filter_upwards with y
    rw [sub_add_eq_sub_sub]
  rw [heq]
  have hrhs : (∫ z : Space, (-dG i t z) * h (x + z)) =
      ∫ y : Space, (-dG i t (y - x)) * h y := by
    have h1 := integral_add_left_eq_self (μ := volume) (fun y : Space => (-dG i t (y - x)) * h y) x
    simpa [add_sub_cancel_left] using h1
  rw [hrhs]
  let S : Set ℝ := Icc (-1) 1
  have hS : S ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
  let C0 := (Real.sqrt (4 * Real.pi * t))⁻¹
  let bnd (y : Space) : ℝ :=
    M * ((2 * t)⁻¹ * Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / ((8 * t)⁻¹))) *
      ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * ((y - x) j) ^ 2)
  have hbnd_int : Integrable bnd := by
    have h1 : Integrable (fun z : Space => ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (z j) ^ 2)) :=
      integrable_prod3 fun _ => integrable_exp_neg_mul_sq (by positivity)
    have h2 : Integrable (fun y : Space => ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * ((y - x) j) ^ 2)) :=
      h1.comp_sub_right x
    exact h2.const_mul _
  have hdom : ∀ᵐ y : Space ∂volume, ∀ s ∈ S,
      ‖(-dG i t ((y - x) - s • e3 i)) * h y‖ ≤ bnd y := by
    refine ae_of_all _ fun y s ⟨hs1, hs2⟩ => ?_
    have habs_s : |s| ≤ 1 := abs_le.mpr ⟨hs1, hs2⟩
    let w := y - x
    let v := w - s • e3 i
    have hv_coord (j : Fin 3) : v j = w j - if j = i then s else 0 := by
      simp [v, e3, EuclideanSpace.single_apply, eq_comm]
    have hG_bound (j : Fin 3) :
        g1 t (v j) ≤ C0 * Real.exp (1 / (4 * t)) * Real.exp (-(8 * t)⁻¹ * (w j) ^ 2) := by
      unfold g1
      have hsq : (w j) ^ 2 / 2 - 1 ≤ (v j) ^ 2 := by
        rw [hv_coord j]
        split_ifs
        · nlinarith [sq_nonneg (w j - 2 * s), sq_abs s]
        · nlinarith [sq_nonneg (w j)]
      have hexp : Real.exp (-(v j) ^ 2 / (4 * t)) ≤
          Real.exp (1 / (4 * t)) * Real.exp (-(8 * t)⁻¹ * (w j) ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have h1 : -((v j) ^ 2) / (4 * t) ≤ (1 - (w j) ^ 2 / 2) / (4 * t) :=
          div_le_div_of_nonneg_right (by linarith) (by positivity)
        have h2 : (1 - (w j) ^ 2 / 2) / (4 * t) = 1 / (4 * t) + -(8 * t)⁻¹ * (w j) ^ 2 := by
          field_simp [ht.ne']; ring
        linarith
      calc C0 * Real.exp (-(v j) ^ 2 / (4 * t))
          ≤ C0 * (Real.exp (1 / (4 * t)) * Real.exp (-(8 * t)⁻¹ * (w j) ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := by ring
    have hG_bound_other (j : Fin 3) (hji : j ≠ i) :
        g1 t (v j) ≤ C0 * Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := by
      unfold g1
      rw [hv_coord j, if_neg hji, sub_zero]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have : -(w j ^ 2) / (4 * t) = -(4 * t)⁻¹ * (w j) ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (w j), inv_pos.mpr (show 0 < 8 * t by positivity),
        show (8 * t)⁻¹ / 2 ≤ (4 * t)⁻¹ by field_simp [ht.ne']; norm_num]
    have hvi_le : |v i| ≤ |w i| + 1 := by
      rw [hv_coord i, if_pos rfl]
      exact (abs_sub _ _).trans (by linarith)
    have hvi_exp : |v i| * Real.exp (-(8 * t)⁻¹ * (w i) ^ 2) ≤
        (2 + 2 / (8 * t)⁻¹) * Real.exp (-((8 * t)⁻¹ / 2) * (w i) ^ 2) := by
      have ha : 0 < (8 * t)⁻¹ := by positivity
      have h1 := abs_mul_exp_neg_le ha (w i)
      have h2 : Real.exp (-(8 * t)⁻¹ * (w i) ^ 2) ≤ Real.exp (-((8 * t)⁻¹ / 2) * (w i) ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (w i)])
      calc |v i| * Real.exp (-(8 * t)⁻¹ * (w i) ^ 2)
          ≤ (|w i| + 1) * Real.exp (-(8 * t)⁻¹ * (w i) ^ 2) :=
            mul_le_mul_of_nonneg_right hvi_le (Real.exp_nonneg _)
        _ = |w i| * Real.exp (-(8 * t)⁻¹ * (w i) ^ 2) + Real.exp (-(8 * t)⁻¹ * (w i) ^ 2) := by ring
        _ ≤ _ := by linarith
    have hdG_le : |-dG i t v| ≤
        ((2 * t)⁻¹ * Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / (8 * t)⁻¹)) *
          ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := by
      rw [abs_neg]
      unfold dG G
      rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * t),
        abs_of_pos (Finset.prod_pos fun j _ => g1_pos ht (v j))]
      have hprod_le : |v i| * ∏ j : Fin 3, g1 t (v j) ≤
          (Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / (8 * t)⁻¹)) *
            ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := by
        have hsplit : |v i| * ∏ j : Fin 3, g1 t (v j) =
            ∏ j : Fin 3, (if j = i then |v i| * g1 t (v i) else g1 t (v j)) := by
          fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
        rw [hsplit]
        have hf (j : Fin 3) : (if j = i then |v i| * g1 t (v i) else g1 t (v j)) ≤
            (if j = i then C0 * Real.exp (1 / (4 * t)) * (2 + 2 / (8 * t)⁻¹) else C0) *
              Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := by
          split_ifs with hji
          · subst hji
            calc |v j| * g1 t (v j)
                ≤ |v j| * (C0 * Real.exp (1 / (4 * t)) * Real.exp (-(8 * t)⁻¹ * (w j) ^ 2)) :=
                  mul_le_mul_of_nonneg_left (hG_bound j) (abs_nonneg _)
              _ = C0 * Real.exp (1 / (4 * t)) * (|v j| * Real.exp (-(8 * t)⁻¹ * (w j) ^ 2)) := by ring
              _ ≤ C0 * Real.exp (1 / (4 * t)) * ((2 + 2 / (8 * t)⁻¹) *
                    Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2)) :=
                  mul_le_mul_of_nonneg_left hvi_exp (by positivity)
              _ = _ := by ring
          · exact hG_bound_other j hji
        calc ∏ j : Fin 3, (if j = i then |v i| * g1 t (v i) else g1 t (v j))
            ≤ ∏ j : Fin 3, ((if j = i then C0 * Real.exp (1 / (4 * t)) * (2 + 2 / (8 * t)⁻¹) else C0) *
                Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2)) :=
              Finset.prod_le_prod
                (fun j _ => by split_ifs; exact mul_nonneg (abs_nonneg _) (g1_pos ht _).le; exact (g1_pos ht _).le)
                (fun j _ => hf j)
          _ = (∏ j : Fin 3, (if j = i then C0 * Real.exp (1 / (4 * t)) * (2 + 2 / (8 * t)⁻¹) else C0)) *
                ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := Finset.prod_mul_distrib
          _ = _ := by congr 1; fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
      calc |v i| / (2 * t) * ∏ j : Fin 3, g1 t (v j)
          = (2 * t)⁻¹ * (|v i| * ∏ j : Fin 3, g1 t (v j)) := by ring
        _ ≤ (2 * t)⁻¹ * ((Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / (8 * t)⁻¹)) *
              ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2)) :=
            mul_le_mul_of_nonneg_left hprod_le (by positivity)
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_mul]
    have hprod_eq : bnd y =
        M * ((2 * t)⁻¹ * Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / (8 * t)⁻¹)) *
          ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2) := rfl
    rw [hprod_eq]
    calc |-dG i t v| * |h y|
        ≤ (((2 * t)⁻¹ * Real.exp (1 / (4 * t)) * C0 ^ 3 * (2 + 2 / (8 * t)⁻¹)) *
            ∏ j : Fin 3, Real.exp (-((8 * t)⁻¹ / 2) * (w j) ^ 2)) * M :=
          mul_le_mul hdG_le (hb y) (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hderiv (y : Space) (s : ℝ) :
      HasDerivAt (fun r : ℝ => G t ((y - x) - r • e3 i) * h y)
        ((-dG i t ((y - x) - s • e3 i)) * h y) s := by
    have hlin : HasDerivAt (fun r : ℝ => (y - x) - r • e3 i) (-e3 i) s := by
      have ha := (hasDerivAt_const s (y - x)).fun_sub ((hasDerivAt_id s).smul_const (e3 i))
      simpa using ha
    have h1 := ((contDiff_G ht).differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt s hlin
    have h1' : HasDerivAt (fun r : ℝ => G t ((y - x) - r • e3 i))
        (-dG i t ((y - x) - s • e3 i)) s := by
      refine h1.congr_deriv ?_
      rw [map_neg]
      exact congrArg Neg.neg (pd3_G ht i _)
    exact h1'.mul_const (h y)
  have hF0_int : Integrable (fun y : Space => G t ((y - x) - (0 : ℝ) • e3 i) * h y) := by
    simp only [zero_smul, sub_zero]
    have h1 := integrable_G_mul_bounded hc hb ht x
    have h2 := h1.comp_sub_right x
    simpa [add_sub_cancel] using h2
  have hF_meas (s : ℝ) : AEStronglyMeasurable (fun y : Space => G t ((y - x) - s • e3 i) * h y) volume :=
    (((contDiff_G ht).continuous.comp
      ((continuous_id.sub continuous_const).sub continuous_const)).mul hc).aestronglyMeasurable
  have hD_meas : AEStronglyMeasurable (fun y : Space => (-dG i t ((y - x) - (0 : ℝ) • e3 i)) * h y) volume := by
    have hc_dG : Continuous (fun y : Space => -dG i t ((y - x) - (0 : ℝ) • e3 i)) := by
      simp only [zero_smul, sub_zero]
      unfold dG
      have hcoord : Continuous (fun y : Space => (y - x) i) :=
        (EuclideanSpace.proj i).continuous.comp (continuous_id.sub continuous_const)
      exact (((hcoord.neg.div_const (2 * t)).mul
        ((contDiff_G ht).continuous.comp (continuous_id.sub continuous_const)))).neg
    exact (hc_dG.mul hc).aestronglyMeasurable
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y => G t ((y - x) - s • e3 i) * h y)
    (F' := fun s y => (-dG i t ((y - x) - s • e3 i)) * h y)
    hS (Eventually.of_forall hF_meas) hF0_int hD_meas hdom hbnd_int
    (ae_of_all _ fun y s _ => hderiv y s)
  simpa using hres.2

private theorem abs_deriv_P_le {h : Space → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y, |h y| ≤ M) {t : ℝ} (ht : 0 < t) (i : Fin 3) (x : Space) :
    |∫ z : Space, (-dG i t z) * h (x + z)| ≤ M * (Real.sqrt (Real.pi * t))⁻¹ := by
  calc |∫ z : Space, (-dG i t z) * h (x + z)|
      = ‖∫ z : Space, (-dG i t z) * h (x + z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z : Space, ‖(-dG i t z) * h (x + z)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ z : Space, M * |dG i t z| := by
        by_cases hint : Integrable (fun z : Space => ‖(-dG i t z) * h (x + z)‖)
        · apply integral_mono hint ((integrable_dG i ht).norm.const_mul M)
          intro z
          dsimp only
          rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_neg, mul_comm M]
          exact mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
        · rw [integral_undef hint]
          exact integral_nonneg fun z => mul_nonneg hM (abs_nonneg _)
    _ = M * (Real.sqrt (Real.pi * t))⁻¹ := by
        rw [integral_const_mul, integral_abs_dG i ht]

private theorem integrableOn_inv_sqrt_pi :
    IntegrableOn (fun t : ℝ => (Real.sqrt (Real.pi * t))⁻¹) (Ioc (0 : ℝ) 1) := by
  have hrpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hIoc : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hrpow
  have hconst : IntegrableOn (fun t : ℝ => (Real.sqrt Real.pi)⁻¹ * t ^ (-(1 / 2 : ℝ))) (Ioc (0 : ℝ) 1) :=
    hIoc.const_mul (Real.sqrt Real.pi)⁻¹
  refine hconst.congr_fun (fun t ht => ?_) measurableSet_Ioc
  dsimp only
  rw [Real.sqrt_mul Real.pi_pos.le, mul_inv, Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]

private theorem integral_inv_sqrt_pi_le :
    (∫ t in Ioc (0 : ℝ) 1, (Real.sqrt (Real.pi * t))⁻¹) ≤ 2 := by
  have h1 : (∫ t in Ioc (0 : ℝ) 1, (Real.sqrt (Real.pi * t))⁻¹) =
      (Real.sqrt Real.pi)⁻¹ * ∫ t in Ioc (0 : ℝ) 1, t ^ (-(1 / 2 : ℝ)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [Real.sqrt_mul Real.pi_pos.le, mul_inv, Real.rpow_neg ht.1.le, ← Real.sqrt_eq_rpow]
  rw [h1, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  have hpi : 1 ≤ Real.sqrt Real.pi := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have hinv : (Real.sqrt Real.pi)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpi
  norm_num
  linarith

private theorem hasDerivAt_I_of_bounded {h : Space → ℝ} (hc : Continuous h) {M : ℝ}
    (hb : ∀ y, |h y| ≤ M) (i : Fin 3) (x : Space) :
    HasDerivAt (fun s : ℝ => I h (x + s • e3 i))
      (∫ t in Ioc (0 : ℝ) 1, ∫ z : Space, (-dG i t z) * h (x + z)) 0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  let D (s : ℝ) (t : ℝ) : ℝ := ∫ z : Space, (-dG i t z) * h (x + s • e3 i + z)
  have hderiv_s (t : ℝ) (ht : 0 < t) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P h t (x + r • e3 i)) (D s t) s := by
    have h1 := hasDerivAt_P_of_bounded hc hb ht i (x + s • e3 i)
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have h1' : HasDerivAt (fun r : ℝ => P h t (x + s • e3 i + r • e3 i)) (D s t) ((fun r => r - s) s) := by
      simpa only [sub_self] using h1
    have hcomp := HasDerivAt.comp (h := fun r => r - s) s h1' hsub
    simp only [mul_one] at hcomp
    have hfun : (fun r : ℝ => P h t (x + s • e3 i + (r - s) • e3 i)) =
        fun r => P h t (x + r • e3 i) := by
      ext r; congr 1; module
    exact hfun ▸ hcomp
  have hD_meas : AEStronglyMeasurable (D 0) (volume.restrict (Ioc (0 : ℝ) 1)) := by
    let g (n : ℕ) (t : ℝ) : ℝ :=
      ((n : ℝ) + 1) * (P h t (x + ((n : ℝ) + 1)⁻¹ • e3 i) - P h t x)
    have hg_meas (n : ℕ) : AEStronglyMeasurable (g n) (volume.restrict (Ioc (0 : ℝ) 1)) := by
      have hcont : ContinuousOn (g n) (Ioc (0 : ℝ) 1) :=
        continuousOn_const.mul
          (((continuousOn_P_time hc hb _).mono Ioc_subset_Ioi_self).sub
            ((continuousOn_P_time hc hb _).mono Ioc_subset_Ioi_self))
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    refine aestronglyMeasurable_of_tendsto_ae atTop hg_meas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h1 := (hderiv_s t ht.1 0).tendsto_slope_zero_right
    have hseq : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] (0 : ℝ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => inv_pos.mpr (by positivity : (0 : ℝ) < (n : ℝ) + 1)⟩
      exact tendsto_one_div_add_atTop_nhds_zero_nat.congr fun n => by simp [one_div]
    have h2 := h1.comp hseq
    refine h2.congr fun n => ?_
    dsimp [g, Function.comp_def]
    simp
  have hF_meas (s : ℝ) : AEStronglyMeasurable (fun t : ℝ => P h t (x + s • e3 i))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_P_time hc hb _).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  have hF0_int : Integrable (fun t : ℝ => P h t (x + (0 : ℝ) • e3 i))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine (integrableOn_const (C := M) (hs := by simp)).mono' (hF_meas 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_P_le hM0 hb ht.1 _
  have hbound_int : Integrable (fun t : ℝ => M * (Real.sqrt (Real.pi * t))⁻¹)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    integrableOn_inv_sqrt_pi.const_mul M
  have hdom : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)), ∀ s ∈ Set.univ,
      ‖D s t‖ ≤ M * (Real.sqrt (Real.pi * t))⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
    rw [Real.norm_eq_abs]
    exact abs_deriv_P_le hM0 hb ht.1 i (x + s • e3 i)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun s t => P h t (x + s • e3 i)) (F' := D) univ_mem
    (Eventually.of_forall hF_meas) hF0_int hD_meas hdom hbound_int
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
      exact hderiv_s t ht.1 s)
  simpa [I, D] using hres.2

private theorem abs_deriv_I_le {h : Space → ℝ} (hc : Continuous h) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ y, |h y| ≤ M) (i : Fin 3) (x : Space) :
    |∫ t in Ioc (0 : ℝ) 1, ∫ z : Space, (-dG i t z) * h (x + z)| ≤ 2 * M := by
  let D (t : ℝ) : ℝ := ∫ z : Space, (-dG i t z) * h (x + z)
  calc |∫ t in Ioc (0 : ℝ) 1, D t|
      = ‖∫ t in Ioc (0 : ℝ) 1, D t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, ‖D t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioc (0 : ℝ) 1, M * (Real.sqrt (Real.pi * t))⁻¹ := by
        by_cases hint : IntegrableOn (fun t => ‖D t‖) (Ioc (0 : ℝ) 1)
        · apply setIntegral_mono_on hint (integrableOn_inv_sqrt_pi.const_mul M) measurableSet_Ioc
          intro t ht
          rw [Real.norm_eq_abs]
          exact abs_deriv_P_le hM hb ht.1 i x
        · rw [integral_undef hint]
          exact setIntegral_nonneg measurableSet_Ioc fun t ht => by positivity
    _ = M * ∫ t in Ioc (0 : ℝ) 1, (Real.sqrt (Real.pi * t))⁻¹ := integral_const_mul _ _
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left integral_inv_sqrt_pi_le hM
    _ = 2 * M := by ring

private theorem hasDerivAt_P_comm {h : Space → ℝ} (h1 : ContDiff ℝ 1 h) {M M' : ℝ}
    {j : Fin 3} (hb : ∀ y, |h y| ≤ M) (hbp : ∀ y, |pd3 h j y| ≤ M') {t : ℝ} (ht : 0 < t)
    (x : Space) :
    HasDerivAt (fun s : ℝ => P h t (x + s • e3 j)) (P (pd3 h j) t x) 0 := by
  have hpd_cont : Continuous (pd3 h j) :=
    (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF_meas (s : ℝ) : AEStronglyMeasurable (fun z : Space => G t z * h (x + s • e3 j + z)) volume :=
    ((contDiff_G ht).continuous.mul
      (h1.continuous.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hD_meas : AEStronglyMeasurable (fun z : Space => G t z * pd3 h j (x + (0 : ℝ) • e3 j + z)) volume :=
    ((contDiff_G ht).continuous.mul
      (hpd_cont.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun s z => G t z * h (x + s • e3 j + z))
    (F' := fun s z => G t z * pd3 h j (x + s • e3 j + z)) univ_mem
    (Eventually.of_forall hF_meas)
    (integrable_G_mul_bounded h1.continuous hb ht (x + (0 : ℝ) • e3 j))
    hD_meas
    (ae_of_all _ fun z s _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (G_pos ht z), mul_comm M']
      exact mul_le_mul_of_nonneg_left (hbp _) (G_pos ht z).le)
    ((integrable_G ht).const_mul M')
    (ae_of_all _ fun z s _ => by
      have hl := line_deriv3 h1 (x + z) (e3 j) s
      have heq : (fun r : ℝ => h ((x + z) + r • e3 j)) = fun r => h (x + r • e3 j + z) := by
        ext r; congr 1; module
      have hl' : HasDerivAt (fun r : ℝ => h (x + r • e3 j + z)) (pd3 h j (x + s • e3 j + z)) s := by
        rw [← heq]
        refine hl.congr_deriv ?_
        unfold pd3
        exact congrArg (fun p => fderiv ℝ h p (e3 j)) (by module)
      exact hl'.const_mul (G t z))
  simpa [P] using hres.2

private theorem hasDerivAt_I_comm {h : Space → ℝ} (h1 : ContDiff ℝ 1 h) {M M' : ℝ}
    {j : Fin 3} (hb : ∀ y, |h y| ≤ M) (hbp : ∀ y, |pd3 h j y| ≤ M') (x : Space) :
    HasDerivAt (fun s : ℝ => I h (x + s • e3 j)) (I (pd3 h j) x) 0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hb 0)
  have hM'0 : 0 ≤ M' := (abs_nonneg _).trans (hbp 0)
  have hpd_cont : Continuous (pd3 h j) :=
    (h1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hderiv_s (t : ℝ) (ht : 0 < t) (s : ℝ) :
      HasDerivAt (fun r : ℝ => P h t (x + r • e3 j)) (P (pd3 h j) t (x + s • e3 j)) s := by
    have hp := hasDerivAt_P_comm h1 hb hbp ht (x + s • e3 j)
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have hp' : HasDerivAt (fun r : ℝ => P h t (x + s • e3 j + r • e3 j))
        (P (pd3 h j) t (x + s • e3 j)) ((fun r => r - s) s) := by simpa only [sub_self] using hp
    have hcomp := HasDerivAt.comp (h := fun r => r - s) s hp' hsub
    simp only [mul_one] at hcomp
    have hfun : (fun r : ℝ => P h t (x + s • e3 j + (r - s) • e3 j)) =
        fun r => P h t (x + r • e3 j) := by ext r; congr 1; module
    exact hfun ▸ hcomp
  have hF_meas (s : ℝ) : AEStronglyMeasurable (fun t : ℝ => P h t (x + s • e3 j))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_P_time h1.continuous hb _).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  have hF0_int : Integrable (fun t : ℝ => P h t (x + (0 : ℝ) • e3 j))
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    refine (integrableOn_const (C := M) (hs := by simp)).mono' (hF_meas 0) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    exact abs_P_le hM0 hb ht.1 _
  have hD_meas : AEStronglyMeasurable (fun t : ℝ => P (pd3 h j) t (x + (0 : ℝ) • e3 j))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_P_time hpd_cont hbp _).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc
  have hdom : ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)), ∀ s ∈ (Set.univ : Set ℝ),
      ‖P (pd3 h j) t (x + s • e3 j)‖ ≤ M' := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
    rw [Real.norm_eq_abs]
    exact abs_P_le hM'0 hbp ht.1 _
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (F := fun s t => P h t (x + s • e3 j))
    (F' := fun s t => P (pd3 h j) t (x + s • e3 j)) univ_mem
    (Eventually.of_forall hF_meas) hF0_int hD_meas hdom
    (integrableOn_const (C := M') (hs := by simp))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht s _
      exact hderiv_s t ht.1 s)
  simpa [I] using hres.2

private theorem one_step_deriv_gain {v F : Space → ℝ} (hv : Continuous v) (hF : Continuous F)
    {Mv MF : ℝ} (hMv : ∀ y, |v y| ≤ Mv) (hMF : ∀ y, |F y| ≤ MF)
    (hrep : ∀ y, v y = P v 1 y - I F y) (i : Fin 3) (x : Space) :
    ∃ d : ℝ, HasDerivAt (fun s : ℝ => v (x + s • e3 i)) d 0 ∧ |d| ≤ Mv + 2 * MF := by
  have hMv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0)
  have hMF0 : 0 ≤ MF := (abs_nonneg _).trans (hMF 0)
  have h1 := hasDerivAt_P_of_bounded hv hMv one_pos i x
  have h2 := hasDerivAt_I_of_bounded hF hMF i x
  have hsub := h1.fun_sub h2
  have heq : (fun s : ℝ => P v 1 (x + s • e3 i) - I F (x + s • e3 i)) =
      fun s => v (x + s • e3 i) := by
    ext s; exact (hrep _).symm
  rw [heq] at hsub
  refine ⟨_, hsub, ?_⟩
  have hb1 : |∫ z : Space, (-dG i 1 z) * v (x + z)| ≤ Mv := by
    have h := abs_deriv_P_le hMv0 hMv one_pos i x
    have hpi : (Real.sqrt (Real.pi * 1))⁻¹ ≤ 1 := by
      rw [mul_one]
      apply inv_le_one_of_one_le₀
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith [Real.two_le_pi])
    exact h.trans (mul_le_of_le_one_right hMv0 hpi)
  have hb2 := abs_deriv_I_le hF hMF0 hMF i x
  calc |(_ : ℝ) - _| ≤ |_| + |_| := abs_sub _ _
    _ ≤ Mv + 2 * MF := add_le_add hb1 hb2

private theorem lipschitz_of_axis_derivs {f : Space → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ x (i : Fin 3), ∃ d : ℝ, HasDerivAt (fun s : ℝ => f (x + s • e3 i)) d 0 ∧ |d| ≤ L)
    (x y : Space) : |f y - f x| ≤ 3 * L * ‖y - x‖ := by
  have hstep (p : Space) (i : Fin 3) (t : ℝ) : |f (p + t • e3 i) - f p| ≤ L * |t| := by
    let g (s : ℝ) : ℝ := f (p + s • e3 i)
    have hgd (s : ℝ) : ∃ d, HasDerivAt g d s ∧ |d| ≤ L := by
      obtain ⟨d, hds, hdl⟩ := hd (p + s • e3 i) i
      refine ⟨d, ?_, hdl⟩
      have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
        simpa using (hasDerivAt_id s).sub_const s
      have hds' : HasDerivAt (fun r : ℝ => f (p + s • e3 i + r • e3 i)) d ((fun r => r - s) s) := by
        simpa only [sub_self] using hds
      have hcomp := HasDerivAt.comp (h := fun r => r - s) s hds' hsub
      simp only [mul_one] at hcomp
      have hfun : (fun r : ℝ => f (p + s • e3 i + (r - s) • e3 i)) = g := by
        ext r; dsimp [g]; congr 1; module
      exact hfun ▸ hcomp
    by_cases ht : t = 0
    · simp [ht]
    · have hcont : Continuous g := continuous_iff_continuousAt.mpr fun s => (hgd s).choose_spec.1.continuousAt
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => (hgd s).choose) hneg
          hcont.continuousOn (fun s _ => (hgd s).choose_spec.1)
        have hcle : |(hgd c).choose| ≤ L := (hgd c).choose_spec.2
        have hgt : g 0 - g t = (0 - t) * (hgd c).choose := by
          have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hneg))).mp hc
          linarith
        have : |g t - g 0| = |t| * |(hgd c).choose| := by
          rw [show g t - g 0 = -(g 0 - g t) by ring, abs_neg, hgt, abs_mul, zero_sub, abs_neg]
        simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left hcle (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
      · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => (hgd s).choose) hpos
          hcont.continuousOn (fun s _ => (hgd s).choose_spec.1)
        have hcle : |(hgd c).choose| ≤ L := (hgd c).choose_spec.2
        have hgt : g t - g 0 = (t - 0) * (hgd c).choose := by
          have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hpos))).mp hc
          linarith
        have : |g t - g 0| = |t| * |(hgd c).choose| := by
          rw [hgt, abs_mul, sub_zero]
        simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left hcle (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
  let d := y - x
  let p1 := x + d 0 • e3 0
  let p2 := p1 + d 1 • e3 1
  have hp3 : p2 + d 2 • e3 2 = y := by
    ext j
    fin_cases j <;> simp [p2, p1, d, e3]
  have hcoord (i : Fin 3) : |d i| ≤ ‖y - x‖ := by
    have := PiLp.norm_apply_le (y - x) i
    simpa [d, Real.norm_eq_abs] using this
  have h0 := hstep x 0 (d 0)
  have h1 := hstep p1 1 (d 1)
  have h2 := hstep p2 2 (d 2)
  rw [hp3] at h2
  have htri : |f y - f x| ≤ |f y - f p2| + |f p2 - f p1| + |f p1 - f x| := by
    have : f y - f x = (f y - f p2) + (f p2 - f p1) + (f p1 - f x) := by ring
    rw [this]
    have h1 := abs_add_le (f y - f p2 + (f p2 - f p1)) (f p1 - f x)
    have h2 := abs_add_le (f y - f p2) (f p2 - f p1)
    linarith
  have hb0 : L * |d 0| ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (hcoord 0) hL
  have hb1 : L * |d 1| ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (hcoord 1) hL
  have hb2 : L * |d 2| ≤ L * ‖y - x‖ := mul_le_mul_of_nonneg_left (hcoord 2) hL
  linarith

theorem exists_C3_bounds {u : Space → ℝ} (hu : IsBoundedSol u) :
    (∀ x, |u x| ≤ 1) ∧
    ∃ C1 C2 C3 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ 0 ≤ C3 ∧
      (∀ x i, |pd3 u i x| ≤ C1) ∧
      (∀ x i j, |pd32 u i j x| ≤ C2) ∧
      (∀ x y i j, |pd32 u i j y - pd32 u i j x| ≤ C3 * ‖y - x‖) := by
  have hu1 : ∀ x, |u x| ≤ 1 := abs_le_one_of_bounded_sol hu
  let F (y : Space) : ℝ := u y ^ 3 - u y
  have hF_c2 : ContDiff ℝ 2 F := (hu.regular.pow 3).sub hu.regular
  have hF_le : ∀ y, |F y| ≤ 2 := fun y => by
    have h1 := hu1 y
    calc |u y ^ 3 - u y| ≤ |u y ^ 3| + |u y| := abs_sub _ _
      _ ≤ 1 ^ 3 + 1 := add_le_add (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 3) h1
      _ = 2 := by norm_num
  have hpd1_le (x : Space) (i : Fin 3) : |pd3 u i x| ≤ 5 := by
    obtain ⟨d, hd, hle⟩ := one_step_deriv_gain hu.regular.continuous hF_c2.continuous hu1 hF_le
      (duhamel_u hu) i x
    have hl := line_deriv3 (hu.regular.of_le (by norm_num)) x (e3 i) 0
    simp only [zero_smul, add_zero] at hl
    have heq : pd3 u i x = d := hl.unique hd
    rw [heq]
    linarith
  have hpd1_F (j : Fin 3) (x : Space) : pd3 F j x = (3 * u x ^ 2 - 1) * pd3 u j x := by
    have hl := line_deriv3 (hF_c2.of_le (by norm_num)) x (e3 j) 0
    have hline_u := line_deriv3 (hu.regular.of_le (by norm_num)) x (e3 j) 0
    have hpow := (hline_u.fun_pow 3).fun_sub hline_u
    have huq := hl.unique hpow
    simp only [zero_smul, add_zero, Nat.add_one_sub_one] at huq
    change pd3 F j x = _ at huq
    rw [huq]; unfold pd3; ring
  have hpd1_F_le (j : Fin 3) (x : Space) : |pd3 F j x| ≤ 10 := by
    rw [hpd1_F, abs_mul]
    have h1 : |3 * u x ^ 2 - 1| ≤ 2 := by
      have hsq : u x ^ 2 ≤ 1 := by rw [← sq_abs (u x)]; nlinarith [hu1 x, abs_nonneg (u x)]
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u x)]
    have h2 : |pd3 u j x| ≤ 5 := hpd1_le x j
    nlinarith [abs_nonneg (3 * u x ^ 2 - 1), abs_nonneg (pd3 u j x)]
  have hduhamel1 (j : Fin 3) (x : Space) :
      pd3 u j x = P (pd3 u j) 1 x - I (pd3 F j) x := by
    have h1 := hasDerivAt_P_comm (hu.regular.of_le (by norm_num)) hu1 (fun y => hpd1_le y j) one_pos x
    have h2 := hasDerivAt_I_comm (hF_c2.of_le (by norm_num)) hF_le (hpd1_F_le j) x
    have hsub := h1.fun_sub h2
    have heq : (fun s : ℝ => P u 1 (x + s • e3 j) - I F (x + s • e3 j)) =
        fun s => u (x + s • e3 j) := by ext s; exact (duhamel_u hu _).symm
    rw [heq] at hsub
    have hl := line_deriv3 (hu.regular.of_le (by norm_num)) x (e3 j) 0
    simp only [zero_smul, add_zero] at hl
    exact hl.unique hsub
  have hpd2_le (x : Space) (j k : Fin 3) : |pd32 u j k x| ≤ 25 := by
    have h1c : ContDiff ℝ 1 (pd3 u j) := (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hFc : ContDiff ℝ 1 (pd3 F j) := (hF_c2.fderiv_right (by norm_num)).clm_apply contDiff_const
    obtain ⟨d, hd, hle⟩ := one_step_deriv_gain h1c.continuous hFc.continuous
      (fun y => hpd1_le y j) (hpd1_F_le j) (hduhamel1 j) k x
    have hl := line_deriv3 h1c x (e3 k) 0
    simp only [zero_smul, add_zero] at hl
    have heq : pd32 u j k x = d := hl.unique hd
    rw [heq]
    linarith
  have hpd2_F (j k : Fin 3) (x : Space) :
      pd32 F j k x = (3 * u x ^ 2 - 1) * pd32 u j k x + 6 * u x * pd3 u k x * pd3 u j x := by
    unfold pd32
    have heq : pd3 F j = fun y => (3 * u y ^ 2 - 1) * pd3 u j y := funext (hpd1_F j)
    rw [heq]
    have h1c : ContDiff ℝ 1 (pd3 u j) := (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hcoeff : ContDiff ℝ 1 (fun y => 3 * u y ^ 2 - 1) :=
      (contDiff_const.mul ((hu.regular.of_le (by norm_num)).pow 2)).sub contDiff_const
    have hl := line_deriv3 (hcoeff.mul h1c) x (e3 k) 0
    have hlu := line_deriv3 (hu.regular.of_le (by norm_num)) x (e3 k) 0
    have hlc : HasDerivAt (fun s : ℝ => 3 * u (x + s • e3 k) ^ 2 - 1)
        (6 * u x * pd3 u k x) 0 := by
      have ha := ((hlu.fun_pow 2).const_mul (3 : ℝ)).sub_const (1 : ℝ)
      refine ha.congr_deriv ?_
      simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
      unfold pd3; ring
    have hlp := line_deriv3 h1c x (e3 k) 0
    have hprod := hlc.fun_mul hlp
    have huq := hl.unique hprod
    simp only [zero_smul, add_zero] at huq
    change pd3 (fun y => (3 * u y ^ 2 - 1) * pd3 u j y) k x = _ at huq
    rw [huq]
    unfold pd3
    ring
  have hpd2_F_le (j k : Fin 3) (x : Space) : |pd32 F j k x| ≤ 200 := by
    rw [hpd2_F]
    have h1 : |3 * u x ^ 2 - 1| ≤ 2 := by
      have hsq : u x ^ 2 ≤ 1 := by rw [← sq_abs (u x)]; nlinarith [hu1 x, abs_nonneg (u x)]
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (u x)]
    have h2 : |pd32 u j k x| ≤ 25 := hpd2_le x j k
    have h3 : |u x| ≤ 1 := hu1 x
    have h4 : |pd3 u k x| ≤ 5 := hpd1_le x k
    have h5 : |pd3 u j x| ≤ 5 := hpd1_le x j
    have ha : |(3 * u x ^ 2 - 1) * pd32 u j k x| ≤ 50 := by
      rw [abs_mul]; nlinarith [abs_nonneg (3 * u x ^ 2 - 1), abs_nonneg (pd32 u j k x)]
    have hb : |6 * u x * pd3 u k x * pd3 u j x| ≤ 150 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
      have h6 : |u x| * |pd3 u k x| ≤ 5 := by nlinarith [abs_nonneg (u x), abs_nonneg (pd3 u k x)]
      nlinarith [abs_nonneg (pd3 u j x), mul_nonneg (abs_nonneg (u x)) (abs_nonneg (pd3 u k x))]
    exact (abs_add_le _ _).trans (by linarith)
  have hduhamel2 (j k : Fin 3) (x : Space) :
      pd32 u j k x = P (pd32 u j k) 1 x - I (pd32 F j k) x := by
    have h1c : ContDiff ℝ 1 (pd3 u j) := (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hFc : ContDiff ℝ 1 (pd3 F j) := (hF_c2.fderiv_right (by norm_num)).clm_apply contDiff_const
    have h1 := hasDerivAt_P_comm h1c (fun y => hpd1_le y j) (fun y => hpd2_le y j k) one_pos x
    have h2 := hasDerivAt_I_comm hFc (hpd1_F_le j) (hpd2_F_le j k) x
    have hsub := h1.fun_sub h2
    have heq : (fun s : ℝ => P (pd3 u j) 1 (x + s • e3 k) - I (pd3 F j) (x + s • e3 k)) =
        fun s => pd3 u j (x + s • e3 k) := by ext s; exact (hduhamel1 j _).symm
    rw [heq] at hsub
    have hl := line_deriv3 h1c x (e3 k) 0
    simp only [zero_smul, add_zero] at hl
    exact hl.unique hsub
  have hpd3_lip (x y : Space) (j k : Fin 3) : |pd32 u j k y - pd32 u j k x| ≤ 1275 * ‖y - x‖ := by
    have h2c : Continuous (pd32 u j k) :=
      (((hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    have hF2c : Continuous (pd32 F j k) :=
      (((hF_c2.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    have hax : ∀ p (l : Fin 3), ∃ d : ℝ,
        HasDerivAt (fun s : ℝ => pd32 u j k (p + s • e3 l)) d 0 ∧ |d| ≤ 425 := by
      intro p l
      obtain ⟨d, hd, hle⟩ := one_step_deriv_gain h2c hF2c (fun w => hpd2_le w j k)
        (hpd2_F_le j k) (hduhamel2 j k) l p
      exact ⟨d, hd, by linarith⟩
    have := lipschitz_of_axis_derivs (L := 425) (by norm_num) hax x y
    linarith
  exact ⟨hu1, 5, 25, 1275, by norm_num, by norm_num, by norm_num, hpd1_le, hpd2_le, hpd3_lip⟩

end Mod1

namespace Mod2
open InnerProductSpace Filter Set Metric Finset
open scoped Topology Laplacian
private theorem norm_proj2_sub_le (x z : Space) : ‖proj2 x - proj2 z‖ ≤ ‖x - z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
    PiLp.sub_apply, proj2_coord]
  nlinarith [sq_nonneg (x 0 - z 0)]

private theorem taylor_lip_bound {f g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : ∀ s, HasDerivAt f (g s) s) (hlip : ∀ s t, |g t - g s| ≤ L * |t - s|)
    (x h : ℝ) : |(f (x + h) - f x) - h * g x| ≤ L * h ^ 2 := by
  by_cases hh : h = 0
  · simp [hh]
  · have hcont : Continuous f :=
      continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt
    rcases lt_or_gt_of_ne hh with hneg | hpos
    · have hlt : x + h < x := by linarith
      obtain ⟨c, ⟨hc1, hc2⟩, hc⟩ := exists_hasDerivAt_eq_slope f g hlt
        hcont.continuousOn (fun s _ => hd s)
      have hdiff : f x - f (x + h) = (x - (x + h)) * g c := by
        have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt))).mp hc
        linarith
      have hrewrite : (f (x + h) - f x) - h * g x = h * (g c - g x) := by linarith
      rw [hrewrite, abs_mul]
      have hcx : |c - x| ≤ |h| := by
        rw [abs_of_neg (by linarith), abs_of_neg hneg]; linarith
      calc |h| * |g c - g x| ≤ |h| * (L * |c - x|) :=
            mul_le_mul_of_nonneg_left (hlip x c) (abs_nonneg _)
        _ ≤ |h| * (L * |h|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcx hL) (abs_nonneg _)
        _ = L * h ^ 2 := by rw [← sq_abs h]; ring
    · have hlt : x < x + h := by linarith
      obtain ⟨c, ⟨hc1, hc2⟩, hc⟩ := exists_hasDerivAt_eq_slope f g hlt
        hcont.continuousOn (fun s _ => hd s)
      have hdiff : f (x + h) - f x = ((x + h) - x) * g c := by
        have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt))).mp hc
        linarith
      have hrewrite : (f (x + h) - f x) - h * g x = h * (g c - g x) := by linarith
      rw [hrewrite, abs_mul]
      have hcx : |c - x| ≤ |h| := by
        rw [abs_of_pos (by linarith), abs_of_pos hpos]; linarith
      calc |h| * |g c - g x| ≤ |h| * (L * |c - x|) :=
            mul_le_mul_of_nonneg_left (hlip x c) (abs_nonneg _)
        _ ≤ |h| * (L * |h|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcx hL) (abs_nonneg _)
        _ = L * h ^ 2 := by rw [← sq_abs h]; ring

private theorem uniform_deriv_limit_of_shift {f g : Space → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (i : Fin 3)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => f (x + s • e3 i)) (g x) 0)
    (hlip : ∀ x y, |g y - g x| ≤ L * ‖y - x‖)
    {f_lim : Space → ℝ}
    (hconv : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |f (x + T • e3 0) - f_lim x| ≤ ε) :
    ∃ g_lim : Space → ℝ,
      (∀ x y, |g_lim y - g_lim x| ≤ L * ‖y - x‖) ∧
      (∀ x, HasDerivAt (fun s : ℝ => f_lim (x + s • e3 i)) (g_lim x) 0) ∧
      (∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
        ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |g (x + T • e3 0) - g_lim x| ≤ ε) := by
  have hline (T : ℝ) (x : Space) (s : ℝ) :
      HasDerivAt (fun r : ℝ => f (x + r • e3 i + T • e3 0)) (g (x + s • e3 i + T • e3 0)) s := by
    have h1 := hd (x + s • e3 i + T • e3 0)
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have h1' : HasDerivAt (fun r : ℝ => f (x + s • e3 i + T • e3 0 + r • e3 i))
        (g (x + s • e3 i + T • e3 0)) ((fun r => r - s) s) := by
      simpa only [sub_self] using h1
    have hcomp := HasDerivAt.comp (h := fun r => r - s) s h1' hsub
    simp only [mul_one] at hcomp
    have hfun : (fun r : ℝ => f (x + s • e3 i + T • e3 0 + (r - s) • e3 i)) =
        fun r => f (x + r • e3 i + T • e3 0) := by ext r; congr 1; module
    exact hfun ▸ hcomp
  have hlip_line (T : ℝ) (x : Space) (s t : ℝ) :
      |g (x + t • e3 i + T • e3 0) - g (x + s • e3 i + T • e3 0)| ≤ L * |t - s| := by
    have h := hlip (x + s • e3 i + T • e3 0) (x + t • e3 i + T • e3 0)
    have hsub : (x + t • e3 i + T • e3 0) - (x + s • e3 i + T • e3 0) = (t - s) • e3 i := by module
    rw [hsub, norm_smul, Real.norm_eq_abs, show ‖e3 i‖ = 1 by simp [e3], mul_one] at h
    exact h
  have hcauchy_unif (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
      ∃ T0 : ℝ, ∀ T S : ℝ, T0 ≤ T → T0 ≤ S → ∀ x ∈ Q3 R,
        |g (x + T • e3 0) - g (x + S • e3 0)| ≤ ε := by
    let h : ℝ := ε / (4 * (L + 1))
    have hh_pos : 0 < h := by dsimp [h]; positivity
    have hLh : 2 * L * h ≤ ε / 2 := by
      have h1 : L / (L + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have h2 : 2 * L * h = (ε / 2) * (L / (L + 1)) := by dsimp [h]; field_simp; ring
      rw [h2]; exact mul_le_of_le_one_right (by positivity) h1
    obtain ⟨T0, hT0⟩ := hconv (R + h) (by linarith) (ε * h / 8) (by positivity)
    refine ⟨T0, fun T S hT hS x hx => ?_⟩
    have hx_mem : x ∈ Q3 (R + h) := fun j =>
      ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩
    have hxh_mem : x + h • e3 i ∈ Q3 (R + h) := by
      intro j
      have hc : (x + h • e3 i) j = x j + if j = i then h else 0 := by
        simp [e3, EuclideanSpace.single_apply, eq_comm]
      rw [hc]
      split_ifs <;> constructor <;> linarith [(hx j).1, (hx j).2]
    have hdiff_d (s : ℝ) :
        HasDerivAt (fun r : ℝ => f (x + r • e3 i + T • e3 0) - f (x + r • e3 i + S • e3 0))
          (g (x + s • e3 i + T • e3 0) - g (x + s • e3 i + S • e3 0)) s :=
      (hline T x s).sub (hline S x s)
    have hdiff_lip (s t : ℝ) :
        |(g (x + t • e3 i + T • e3 0) - g (x + t • e3 i + S • e3 0)) -
          (g (x + s • e3 i + T • e3 0) - g (x + s • e3 i + S • e3 0))| ≤ (2 * L) * |t - s| := by
      have hre : (g (x + t • e3 i + T • e3 0) - g (x + t • e3 i + S • e3 0)) -
          (g (x + s • e3 i + T • e3 0) - g (x + s • e3 i + S • e3 0)) =
          (g (x + t • e3 i + T • e3 0) - g (x + s • e3 i + T • e3 0)) -
          (g (x + t • e3 i + S • e3 0) - g (x + s • e3 i + S • e3 0)) := by ring
      rw [hre]
      exact (abs_sub _ _).trans (by linarith [hlip_line T x s t, hlip_line S x s t])
    have htay := taylor_lip_bound (by positivity : 0 ≤ 2 * L) hdiff_d hdiff_lip 0 h
    simp only [zero_add, zero_smul, add_zero] at htay
    have h1 : |f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0)| ≤ ε * h / 4 := by
      have ha := hT0 T hT _ hxh_mem
      have hb := hT0 S hS _ hxh_mem
      have hre : f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0) =
          (f (x + h • e3 i + T • e3 0) - f_lim (x + h • e3 i)) -
          (f (x + h • e3 i + S • e3 0) - f_lim (x + h • e3 i)) := by ring
      rw [hre]; exact (abs_sub _ _).trans (by linarith)
    have h2 : |f (x + T • e3 0) - f (x + S • e3 0)| ≤ ε * h / 4 := by
      have ha := hT0 T hT _ hx_mem
      have hb := hT0 S hS _ hx_mem
      have hre : f (x + T • e3 0) - f (x + S • e3 0) =
          (f (x + T • e3 0) - f_lim x) - (f (x + S • e3 0) - f_lim x) := by ring
      rw [hre]; exact (abs_sub _ _).trans (by linarith)
    have h3 : h * |g (x + T • e3 0) - g (x + S • e3 0)| ≤ ε * h := by
      have htri : |h * (g (x + T • e3 0) - g (x + S • e3 0))| ≤
          |(f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0)) -
            (f (x + T • e3 0) - f (x + S • e3 0))| + 2 * L * h ^ 2 := by
        have hre : h * (g (x + T • e3 0) - g (x + S • e3 0)) =
            ((f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0)) -
              (f (x + T • e3 0) - f (x + S • e3 0))) -
            (((f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0)) -
              (f (x + T • e3 0) - f (x + S • e3 0))) -
              h * (g (x + T • e3 0) - g (x + S • e3 0))) := by ring
        rw [hre]; exact (abs_sub _ _).trans (by linarith)
      rw [abs_mul, abs_of_pos hh_pos] at htri
      have hsub : |(f (x + h • e3 i + T • e3 0) - f (x + h • e3 i + S • e3 0)) -
          (f (x + T • e3 0) - f (x + S • e3 0))| ≤ ε * h / 2 :=
        (abs_sub _ _).trans (by linarith)
      nlinarith
    exact le_of_mul_le_mul_left (by linarith : h * |g (x + T • e3 0) - g (x + S • e3 0)| ≤ h * ε) hh_pos
  have hex_lim (x : Space) : ∃ l : ℝ, Tendsto (fun T : ℝ => g (x + T • e3 0)) atTop (𝓝 l) := by
    have hseq : CauchySeq (fun n : ℕ => g (x + (n : ℝ) • e3 0)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      let R := max (|x 0|) (max (|x 1|) (|x 2|))
      have hR : 0 ≤ R := le_trans (abs_nonneg _) (le_max_left _ _)
      have hxR : x ∈ Q3 R := by
        intro j
        rw [Set.mem_Icc, ← abs_le]
        fin_cases j
        · exact le_max_left _ _
        · exact le_trans (le_max_left _ _) (le_max_right _ _)
        · exact le_trans (le_max_right _ _) (le_max_right _ _)
      obtain ⟨T0, hT0⟩ := hcauchy_unif R hR (ε / 2) (half_pos hε)
      refine ⟨Nat.ceil (max 0 T0), fun m hm n hn => ?_⟩
      rw [Real.dist_eq]
      have hm' : T0 ≤ (m : ℝ) :=
        (le_max_right 0 T0).trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hm))
      have hn' : T0 ≤ (n : ℝ) :=
        (le_max_right 0 T0).trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr hn))
      exact (hT0 m n hm' hn' x hxR).trans_lt (half_lt_self hε)
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hseq
    refine ⟨l, ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    let R := max (|x 0|) (max (|x 1|) (|x 2|))
    have hR : 0 ≤ R := le_trans (abs_nonneg _) (le_max_left _ _)
    have hxR : x ∈ Q3 R := by
      intro j; rw [Set.mem_Icc, ← abs_le]
      fin_cases j
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    obtain ⟨T0, hT0⟩ := hcauchy_unif R hR (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hl (ε / 2) (half_pos hε)
    refine ⟨max T0 N, fun T hT => ?_⟩
    let M : ℕ := max N (Nat.ceil (max 0 T0))
    have hM1 : N ≤ M := le_max_left _ _
    have hM2 : T0 ≤ (M : ℝ) :=
      (le_max_right 0 T0).trans ((Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _)))
    have hd1 : dist (g (x + T • e3 0)) (g (x + (M : ℝ) • e3 0)) ≤ ε / 2 := by
      rw [Real.dist_eq]; exact hT0 T M ((le_max_left _ _).trans hT) hM2 x hxR
    have hd2 : dist (g (x + (M : ℝ) • e3 0)) l < ε / 2 := hN M hM1
    exact (dist_triangle _ _ _).trans_lt (by linarith)
  let g_lim (x : Space) : ℝ := (hex_lim x).choose
  have hg_tendsto (x : Space) : Tendsto (fun T : ℝ => g (x + T • e3 0)) atTop (𝓝 (g_lim x)) :=
    (hex_lim x).choose_spec
  refine ⟨g_lim, ?_, ?_, ?_⟩
  · -- g_lim is L-Lipschitz
    intro x y
    have hlim : Tendsto (fun T : ℝ => |g (y + T • e3 0) - g (x + T • e3 0)|) atTop
        (𝓝 |g_lim y - g_lim x|) :=
      ((hg_tendsto y).sub (hg_tendsto x)).abs
    refine le_of_tendsto hlim (Eventually.of_forall fun T => ?_)
    have h := hlip (x + T • e3 0) (y + T • e3 0)
    simpa [add_sub_add_right_eq_sub] using h
  · -- HasDerivAt of f_lim along e3 i
    intro x
    rw [hasDerivAt_iff_tendsto_slope_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    let δ : ℝ := ε / (2 * (L + 1))
    refine ⟨δ, by dsimp [δ]; positivity, fun h hh_ne hh_lt => ?_⟩
    rw [Real.dist_eq, sub_zero] at hh_lt
    have hbound : |(f_lim (x + h • e3 i) - f_lim x) - h * g_lim x| ≤ L * h ^ 2 := by
      have hf1 : Tendsto (fun T : ℝ => f (x + h • e3 i + T • e3 0)) atTop (𝓝 (f_lim (x + h • e3 i))) := by
        rw [Metric.tendsto_atTop]
        intro η hη
        let y := x + h • e3 i
        let R := max (|y 0|) (max (|y 1|) (|y 2|))
        obtain ⟨T0, hT0⟩ := hconv R (le_trans (abs_nonneg _) (le_max_left _ _)) (η / 2) (half_pos hη)
        refine ⟨T0, fun T hT => ?_⟩
        rw [Real.dist_eq]
        have hyR : y ∈ Q3 R := by
          intro j; rw [Set.mem_Icc, ← abs_le]
          fin_cases j
          · exact le_max_left _ _
          · exact le_trans (le_max_left _ _) (le_max_right _ _)
          · exact le_trans (le_max_right _ _) (le_max_right _ _)
        exact (hT0 T hT y hyR).trans_lt (half_lt_self hη)
      have hf0 : Tendsto (fun T : ℝ => f (x + T • e3 0)) atTop (𝓝 (f_lim x)) := by
        rw [Metric.tendsto_atTop]
        intro η hη
        let R := max (|x 0|) (max (|x 1|) (|x 2|))
        obtain ⟨T0, hT0⟩ := hconv R (le_trans (abs_nonneg _) (le_max_left _ _)) (η / 2) (half_pos hη)
        refine ⟨T0, fun T hT => ?_⟩
        rw [Real.dist_eq]
        have hxR : x ∈ Q3 R := by
          intro j; rw [Set.mem_Icc, ← abs_le]
          fin_cases j
          · exact le_max_left _ _
          · exact le_trans (le_max_left _ _) (le_max_right _ _)
          · exact le_trans (le_max_right _ _) (le_max_right _ _)
        exact (hT0 T hT x hxR).trans_lt (half_lt_self hη)
      have hlim := ((hf1.sub hf0).sub ((tendsto_const_nhds (x := h)).mul (hg_tendsto x))).abs
      refine le_of_tendsto hlim (Eventually.of_forall fun T => ?_)
      have ht := taylor_lip_bound hL (hline T x) (hlip_line T x) 0 h
      simpa using ht
    rw [Real.dist_eq, smul_eq_mul]
    have hdiv : |h⁻¹ * (f_lim (x + (0 + h) • e3 i) - f_lim (x + (0 : ℝ) • e3 i)) - g_lim x| =
        |(f_lim (x + h • e3 i) - f_lim x) - h * g_lim x| / |h| := by
      simp only [zero_add, zero_smul, add_zero]
      rw [← abs_div]
      congr 1
      have hh0 : h ≠ 0 := hh_ne
      field_simp [hh0]
    rw [hdiv]
    have hne : 0 < |h| := abs_pos.mpr hh_ne
    calc |(f_lim (x + h • e3 i) - f_lim x) - h * g_lim x| / |h|
        ≤ (L * h ^ 2) / |h| := div_le_div_of_nonneg_right hbound hne.le
      _ = L * |h| := by rw [← sq_abs h]; field_simp [hne.ne']
      _ ≤ L * δ := mul_le_mul_of_nonneg_left hh_lt.le hL
      _ < ε := by
          dsimp [δ]
          have h1 : L / (L + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
          have h2 : L * (ε / (2 * (L + 1))) = (ε / 2) * (L / (L + 1)) := by field_simp
          rw [h2]; nlinarith
  · -- Uniform convergence of g to g_lim on Q3 R
    intro R hR ε hε
    obtain ⟨T0, hT0⟩ := hcauchy_unif R hR ε hε
    refine ⟨T0, fun T hT x hx => ?_⟩
    have hlim : Tendsto (fun S : ℝ => |g (x + T • e3 0) - g (x + S • e3 0)|) atTop
        (𝓝 |g (x + T • e3 0) - g_lim x|) :=
      (tendsto_const_nhds.sub (hg_tendsto x)).abs
    refine le_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop T0] with S hS
    exact hT0 T S hT hS x hx

private theorem hasFDerivAt_of_lip_partials2 {f : Plane2 → ℝ} {g0 g1 : Plane2 → ℝ} {L : ℝ}
    (hL : 0 ≤ L)
    (hd0 : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 0)) (g0 y) 0)
    (hd1 : ∀ y, HasDerivAt (fun s : ℝ => f (y + s • e2 1)) (g1 y) 0)
    (hlip0 : ∀ y z, |g0 z - g0 y| ≤ L * ‖z - y‖)
    (hlip1 : ∀ y z, |g1 z - g1 y| ≤ L * ‖z - y‖) (y : Plane2) :
    HasFDerivAt f (g0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
      g1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) y := by
  let A : Plane2 →L[ℝ] ℝ :=
    g0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
    g1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)
  have hA (h : Plane2) : A h = g0 y * h 0 + g1 y * h 1 := by
    simp [A]
  have hline0 (p : Plane2) (s : ℝ) :
      HasDerivAt (fun r : ℝ => f (p + r • e2 0)) (g0 (p + s • e2 0)) s := by
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have h1' : HasDerivAt (fun r : ℝ => f (p + s • e2 0 + r • e2 0))
        (g0 (p + s • e2 0)) ((fun r => r - s) s) := by simpa only [sub_self] using hd0 (p + s • e2 0)
    have hcomp := HasDerivAt.comp (h := fun r => r - s) s h1' hsub
    simp only [mul_one] at hcomp
    have hfun : (fun r : ℝ => f (p + s • e2 0 + (r - s) • e2 0)) =
        fun r => f (p + r • e2 0) := by ext r; congr 1; module
    exact hfun ▸ hcomp
  have hline1 (p : Plane2) (s : ℝ) :
      HasDerivAt (fun r : ℝ => f (p + r • e2 1)) (g1 (p + s • e2 1)) s := by
    have hsub : HasDerivAt (fun r : ℝ => r - s) 1 s := by
      simpa using (hasDerivAt_id s).sub_const s
    have h1' : HasDerivAt (fun r : ℝ => f (p + s • e2 1 + r • e2 1))
        (g1 (p + s • e2 1)) ((fun r => r - s) s) := by simpa only [sub_self] using hd1 (p + s • e2 1)
    have hcomp := HasDerivAt.comp (h := fun r => r - s) s h1' hsub
    simp only [mul_one] at hcomp
    have hfun : (fun r : ℝ => f (p + s • e2 1 + (r - s) • e2 1)) =
        fun r => f (p + r • e2 1) := by ext r; congr 1; module
    exact hfun ▸ hcomp
  have herr (h : Plane2) : |f (y + h) - f y - A h| ≤ 3 * L * ‖h‖ ^ 2 := by
    let p := y + h 0 • e2 0
    have hp1 : p + h 1 • e2 1 = y + h := by
      ext i; fin_cases i <;> simp [p, e2]
    have hb0 : |f p - f y - h 0 * g0 y| ≤ L * (h 0) ^ 2 := by
      have hlip_s (s t : ℝ) : |g0 (y + t • e2 0) - g0 (y + s • e2 0)| ≤ L * |t - s| := by
        have := hlip0 (y + s • e2 0) (y + t • e2 0)
        have hsub : (y + t • e2 0) - (y + s • e2 0) = (t - s) • e2 0 := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, show ‖e2 0‖ = 1 by simp [e2], mul_one] at this
        exact this
      simpa [p] using taylor_lip_bound hL (hline0 y) hlip_s 0 (h 0)
    have hb1 : |f (y + h) - f p - h 1 * g1 p| ≤ L * (h 1) ^ 2 := by
      have hlip_s (s t : ℝ) : |g1 (p + t • e2 1) - g1 (p + s • e2 1)| ≤ L * |t - s| := by
        have := hlip1 (p + s • e2 1) (p + t • e2 1)
        have hsub : (p + t • e2 1) - (p + s • e2 1) = (t - s) • e2 1 := by module
        rw [hsub, norm_smul, Real.norm_eq_abs, show ‖e2 1‖ = 1 by simp [e2], mul_one] at this
        exact this
      simpa [hp1] using taylor_lip_bound hL (hline1 p) hlip_s 0 (h 1)
    have hgp : |g1 p - g1 y| ≤ L * |h 0| := by
      have := hlip1 y p
      have hsub : p - y = h 0 • e2 0 := by dsimp [p]; module
      rw [hsub, norm_smul, Real.norm_eq_abs, show ‖e2 0‖ = 1 by simp [e2], mul_one] at this
      exact this
    have hsplit : f (y + h) - f y - A h =
        (f (y + h) - f p - h 1 * g1 p) + h 1 * (g1 p - g1 y) + (f p - f y - h 0 * g0 y) := by
      rw [hA]; ring
    have hc0 : |h 0| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le h 0
    have hc1 : |h 1| ≤ ‖h‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le h 1
    have hsq0 : (h 0) ^ 2 ≤ ‖h‖ ^ 2 := by rw [← sq_abs (h 0)]; nlinarith [abs_nonneg (h 0), norm_nonneg h]
    have hsq1 : (h 1) ^ 2 ≤ ‖h‖ ^ 2 := by rw [← sq_abs (h 1)]; nlinarith [abs_nonneg (h 1), norm_nonneg h]
    have hmid : |h 1 * (g1 p - g1 y)| ≤ L * ‖h‖ ^ 2 := by
      rw [abs_mul]
      calc |h 1| * |g1 p - g1 y| ≤ |h 1| * (L * |h 0|) :=
            mul_le_mul_of_nonneg_left hgp (abs_nonneg _)
        _ = L * (|h 1| * |h 0|) := by ring
        _ ≤ L * (‖h‖ * ‖h‖) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hc1 hc0 (abs_nonneg _) (norm_nonneg _)) hL
        _ = L * ‖h‖ ^ 2 := by ring
    rw [hsplit]
    have ha1 := abs_add_le (f (y + h) - f p - h 1 * g1 p + h 1 * (g1 p - g1 y))
      (f p - f y - h 0 * g0 y)
    have ha2 := abs_add_le (f (y + h) - f p - h 1 * g1 p) (h 1 * (g1 p - g1 y))
    nlinarith
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨c / (3 * L + 1), by positivity, fun h hh => ?_⟩
  rw [dist_zero_right] at hh
  rw [Real.norm_eq_abs]
  calc |f (y + h) - f y - A h| ≤ 3 * L * ‖h‖ ^ 2 := herr h
    _ = (3 * L * ‖h‖) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have h1 : 3 * L * ‖h‖ ≤ 3 * L * (c / (3 * L + 1)) :=
          mul_le_mul_of_nonneg_left hh.le (by positivity)
        have h2 : (3 * L) / (3 * L + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
        have h3 : 3 * L * (c / (3 * L + 1)) = c * ((3 * L) / (3 * L + 1)) := by ring
        rw [h3] at h1
        exact h1.trans (mul_le_of_le_one_right hc.le h2)

theorem exists_limit_profile {u : Space → ℝ} (hu : IsBoundedSol u)
    (hpos : ∀ x, 0 < pd3 u 0 x)
    {C1 C2 C3 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hC3 : 0 ≤ C3)
    (hu1 : ∀ x, |u x| ≤ 1)
    (hpd1 : ∀ x i, |pd3 u i x| ≤ C1)
    (hpd2 : ∀ x i j, |pd32 u i j x| ≤ C2)
    (hpd3_lip : ∀ x y i j, |pd32 u i j y - pd32 u i j x| ≤ C3 * ‖y - x‖) :
    ∃ u_plus : Plane2 → ℝ,
      ContDiff ℝ 2 u_plus ∧
      (∀ y, |u_plus y| ≤ 1) ∧
      (∀ y, (Δ u_plus y) + u_plus y - (u_plus y) ^ 3 = 0) ∧
      (∀ y i, |pd2 u_plus i y| ≤ C1) ∧
      (∀ y i j, |pd22 u_plus i j y| ≤ C2) ∧
      (∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R,
        |u (x + T • e3 0) - u_plus (proj2 x)| ≤ ε ∧
        |pd3 u 0 (x + T • e3 0)| ≤ ε ∧
        (∀ i : Fin 2, |pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)| ≤ ε) ∧
        (∀ k : Fin 3, |pd32 u k 0 (x + T • e3 0)| ≤ ε) ∧
        (∀ i j : Fin 2, |pd32 u i.succ j.succ (x + T • e3 0) - pd22 u_plus i j (proj2 x)| ≤ ε)) := by
  have hu_lip (x y : Space) : |u y - u x| ≤ (3 * C1) * ‖y - x‖ := by
    have hstep (p : Space) (i : Fin 3) (t : ℝ) : |u (p + t • e3 i) - u p| ≤ C1 * |t| := by
      let g (s : ℝ) : ℝ := u (p + s • e3 i)
      have hgd (s : ℝ) : HasDerivAt g (pd3 u i (p + s • e3 i)) s :=
        ((hu.regular.of_le (by norm_num)).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s
          (by simpa using (((hasDerivAt_id s).smul_const (e3 i)).const_add p))
      by_cases ht : t = 0
      · simp [ht]
      · have hcont : Continuous g := continuous_iff_continuousAt.mpr fun s => (hgd s).continuousAt
        rcases lt_or_gt_of_ne ht with hneg | hpos'
        · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => pd3 u i (p + s • e3 i))
            hneg hcont.continuousOn (fun s _ => hgd s)
          have hgt : g 0 - g t = (0 - t) * pd3 u i (p + c • e3 i) := by
            have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hneg))).mp hc; linarith
          have : |g t - g 0| = |t| * |pd3 u i (p + c • e3 i)| := by
            rw [show g t - g 0 = -(g 0 - g t) by ring, abs_neg, hgt, abs_mul, zero_sub, abs_neg]
          simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left (hpd1 _ i) (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
        · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => pd3 u i (p + s • e3 i))
            hpos' hcont.continuousOn (fun s _ => hgd s)
          have hgt : g t - g 0 = (t - 0) * pd3 u i (p + c • e3 i) := by
            have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hpos'))).mp hc; linarith
          have : |g t - g 0| = |t| * |pd3 u i (p + c • e3 i)| := by
            rw [hgt, abs_mul, sub_zero]
          simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left (hpd1 _ i) (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
    let d := y - x
    let p1 := x + d 0 • e3 0
    let p2 := p1 + d 1 • e3 1
    have hp3 : p2 + d 2 • e3 2 = y := by ext j; fin_cases j <;> simp [p2, p1, d, e3]
    have hc (i : Fin 3) : |d i| ≤ ‖y - x‖ := by
      simpa [d, Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) i
    have htri : |u y - u x| ≤ |u y - u p2| + |u p2 - u p1| + |u p1 - u x| := by
      have : u y - u x = (u y - u p2) + (u p2 - u p1) + (u p1 - u x) := by ring
      rw [this]
      have ha1 := abs_add_le (u y - u p2 + (u p2 - u p1)) (u p1 - u x)
      have ha2 := abs_add_le (u y - u p2) (u p2 - u p1)
      linarith
    have h0 := hstep x 0 (d 0)
    have h1 := hstep p1 1 (d 1)
    have h2 := hstep p2 2 (d 2)
    rw [hp3] at h2
    have hb0 : C1 * |d 0| ≤ C1 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 0) hC1
    have hb1 : C1 * |d 1| ≤ C1 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 1) hC1
    have hb2 : C1 * |d 2| ≤ C1 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 2) hC1
    linarith
  have hpd1_lip (i : Fin 3) (x y : Space) : |pd3 u i y - pd3 u i x| ≤ (3 * C2) * ‖y - x‖ := by
    have h1c : ContDiff ℝ 1 (pd3 u i) :=
      (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hstep (p : Space) (j : Fin 3) (t : ℝ) :
        |pd3 u i (p + t • e3 j) - pd3 u i p| ≤ C2 * |t| := by
      let g (s : ℝ) : ℝ := pd3 u i (p + s • e3 j)
      have hgd (s : ℝ) : HasDerivAt g (pd32 u i j (p + s • e3 j)) s :=
        (h1c.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt s
          (by simpa using (((hasDerivAt_id s).smul_const (e3 j)).const_add p))
      by_cases ht : t = 0
      · simp [ht]
      · have hcont : Continuous g := continuous_iff_continuousAt.mpr fun s => (hgd s).continuousAt
        rcases lt_or_gt_of_ne ht with hneg | hpos'
        · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => pd32 u i j (p + s • e3 j))
            hneg hcont.continuousOn (fun s _ => hgd s)
          have hgt : g 0 - g t = (0 - t) * pd32 u i j (p + c • e3 j) := by
            have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hneg))).mp hc; linarith
          have : |g t - g 0| = |t| * |pd32 u i j (p + c • e3 j)| := by
            rw [show g t - g 0 = -(g 0 - g t) by ring, abs_neg, hgt, abs_mul, zero_sub, abs_neg]
          simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left (hpd2 _ i j) (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
        · obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope g (fun s => pd32 u i j (p + s • e3 j))
            hpos' hcont.continuousOn (fun s _ => hgd s)
          have hgt : g t - g 0 = (t - 0) * pd32 u i j (p + c • e3 j) := by
            have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hpos'))).mp hc; linarith
          have : |g t - g 0| = |t| * |pd32 u i j (p + c • e3 j)| := by
            rw [hgt, abs_mul, sub_zero]
          simpa [g] using this.le.trans (mul_le_mul_of_nonneg_left (hpd2 _ i j) (abs_nonneg t)) |>.trans_eq (mul_comm _ _)
    let d := y - x
    let p1 := x + d 0 • e3 0
    let p2 := p1 + d 1 • e3 1
    have hp3 : p2 + d 2 • e3 2 = y := by ext j; fin_cases j <;> simp [p2, p1, d, e3]
    have hc (j : Fin 3) : |d j| ≤ ‖y - x‖ := by
      simpa [d, Real.norm_eq_abs] using PiLp.norm_apply_le (y - x) j
    have htri : |pd3 u i y - pd3 u i x| ≤
        |pd3 u i y - pd3 u i p2| + |pd3 u i p2 - pd3 u i p1| + |pd3 u i p1 - pd3 u i x| := by
      have : pd3 u i y - pd3 u i x =
          (pd3 u i y - pd3 u i p2) + (pd3 u i p2 - pd3 u i p1) + (pd3 u i p1 - pd3 u i x) := by ring
      rw [this]
      have ha1 := abs_add_le (pd3 u i y - pd3 u i p2 + (pd3 u i p2 - pd3 u i p1)) (pd3 u i p1 - pd3 u i x)
      have ha2 := abs_add_le (pd3 u i y - pd3 u i p2) (pd3 u i p2 - pd3 u i p1)
      linarith
    have h0 := hstep x 0 (d 0)
    have h1 := hstep p1 1 (d 1)
    have h2 := hstep p2 2 (d 2)
    rw [hp3] at h2
    have hb0 : C2 * |d 0| ≤ C2 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 0) hC2
    have hb1 : C2 * |d 1| ≤ C2 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 1) hC2
    have hb2 : C2 * |d 2| ≤ C2 * ‖y - x‖ := mul_le_mul_of_nonneg_left (hc 2) hC2
    linarith
  let u_plus (y : Plane2) : ℝ := ⨆ t : ℝ, u (mk3 t y)
  have hmono_line (y : Plane2) : Monotone (fun t : ℝ => u (mk3 t y)) := by
    apply StrictMono.monotone
    apply strictMono_of_deriv_pos
    intro t
    have h1 : HasDerivAt (fun s : ℝ => u (mk3 0 y + s • e3 0)) (pd3 u 0 (mk3 t y)) t := by
      have hlin : HasDerivAt (fun s : ℝ => mk3 0 y + s • e3 0) (e3 0) t := by
        simpa using ((hasDerivAt_id t).smul_const (e3 0)).const_add (mk3 0 y)
      have h := ((hu.regular.of_le (by norm_num)).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hlin
      exact h.congr_deriv (by unfold pd3; rw [mk3_add_e0, zero_add])
    have heq : (fun s : ℝ => u (mk3 0 y + s • e3 0)) = fun s => u (mk3 s y) := by
      ext s; rw [mk3_add_e0, zero_add]
    rw [heq] at h1
    rw [h1.deriv]
    exact hpos _
  have hbdd_line (y : Plane2) : BddAbove (range fun t : ℝ => u (mk3 t y)) :=
    ⟨1, by rintro _ ⟨t, rfl⟩; exact (abs_le.mp (hu1 _)).2⟩
  have htendsto_pt (x : Space) :
      Tendsto (fun T : ℝ => u (x + T • e3 0)) atTop (𝓝 (u_plus (proj2 x))) := by
    have h1 := tendsto_atTop_ciSup (hmono_line (proj2 x)) (hbdd_line (proj2 x))
    have hcomp := h1.comp (tendsto_atTop_add_const_left atTop (x 0) tendsto_id)
    refine hcomp.congr fun T => ?_
    dsimp [Function.comp_def]
    conv_rhs => rw [← mk3_proj2 x, mk3_add_e0]
  have hu_plus_abs (y : Plane2) : |u_plus y| ≤ 1 := by
    have hlim := (htendsto_pt (mk3 0 y)).abs
    rw [proj2_mk3] at hlim
    exact le_of_tendsto hlim (Eventually.of_forall fun T => hu1 _)
  have hu_plus_lip (y z : Plane2) : |u_plus z - u_plus y| ≤ (3 * C1) * ‖z - y‖ := by
    have h1 := htendsto_pt (mk3 0 y)
    have h2 := htendsto_pt (mk3 0 z)
    rw [proj2_mk3] at h1 h2
    refine le_of_tendsto (h2.sub h1).abs (Eventually.of_forall fun T => ?_)
    have h := hu_lip (mk3 0 y + T • e3 0) (mk3 0 z + T • e3 0)
    have hnorm : ‖(mk3 0 z + T • e3 0) - (mk3 0 y + T • e3 0)‖ = ‖z - y‖ := by
      rw [add_sub_add_right_eq_sub]
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simp [Fin.sum_univ_three, Fin.sum_univ_two, mk3]
    rwa [hnorm] at h
  have hconv0 (R : ℝ) (hR : 0 ≤ R) (ε : ℝ) (hε : 0 < ε) :
      ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |u (x + T • e3 0) - u_plus (proj2 x)| ≤ ε := by
    let δ : ℝ := ε / (9 * C1 + 1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hcov : Q3 R ⊆ ⋃ p ∈ Q3 R, ball p δ := fun x hx =>
      mem_biUnion hx (mem_ball_self hδ)
    obtain ⟨s, _, hs_fin, hs_cov⟩ := (isCompact_Q3 R).elim_finite_subcover_image
      (fun p _ => isOpen_ball) hcov
    have hTp (p : Space) : ∃ T_p : ℝ, ∀ T : ℝ, T_p ≤ T →
        |u (p + T • e3 0) - u_plus (proj2 p)| ≤ ε / 3 := by
      obtain ⟨T_p, hT_p⟩ := Metric.tendsto_atTop.mp (htendsto_pt p) (ε / 3) (by positivity)
      exact ⟨T_p, fun T hT => by rw [← Real.dist_eq]; exact (hT_p T hT).le⟩
    let sf : Finset Space := hs_fin.toFinset
    have hsf_ne : sf.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have h0 : (0 : Space) ∈ Q3 R := fun i => ⟨by simp; linarith, by simp; linarith⟩
      obtain ⟨p, hp_s, _⟩ := mem_iUnion₂.mp (hs_cov h0)
      have hp_sf : p ∈ sf := hs_fin.mem_toFinset.mpr hp_s
      simp [hne] at hp_sf
    let T0 : ℝ := sf.sup' hsf_ne (fun p => (hTp p).choose)
    refine ⟨T0, fun T hT x hx => ?_⟩
    obtain ⟨p, hp_s, hxp⟩ := mem_iUnion₂.mp (hs_cov hx)
    have hp_sf : p ∈ sf := hs_fin.mem_toFinset.mpr hp_s
    rw [mem_ball, dist_eq_norm] at hxp
    have hpT : (hTp p).choose ≤ T := le_trans (Finset.le_sup' (fun q => (hTp q).choose) hp_sf) hT
    have hmid : |u (p + T • e3 0) - u_plus (proj2 p)| ≤ ε / 3 := (hTp p).choose_spec T hpT
    have hleft : |u (x + T • e3 0) - u (p + T • e3 0)| ≤ 3 * C1 * δ := by
      have h := hu_lip (p + T • e3 0) (x + T • e3 0)
      rw [add_sub_add_right_eq_sub] at h
      exact h.trans (mul_le_mul_of_nonneg_left hxp.le (by positivity))
    have hright : |u_plus (proj2 p) - u_plus (proj2 x)| ≤ 3 * C1 * δ := by
      have h := hu_plus_lip (proj2 x) (proj2 p)
      rw [norm_sub_rev] at h
      exact h.trans (mul_le_mul_of_nonneg_left ((norm_proj2_sub_le x p).trans hxp.le) (by positivity))
    have h6C1δ : 6 * C1 * δ ≤ 2 * ε / 3 := by
      have h1 : 9 * C1 / (9 * C1 + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      have h2 : 6 * C1 * δ = (2 * ε / 3) * (9 * C1 / (9 * C1 + 1)) := by dsimp [δ]; ring
      rw [h2]
      exact mul_le_of_le_one_right (by positivity) h1
    have hsplit : u (x + T • e3 0) - u_plus (proj2 x) =
        (u (x + T • e3 0) - u (p + T • e3 0)) + (u (p + T • e3 0) - u_plus (proj2 p)) +
        (u_plus (proj2 p) - u_plus (proj2 x)) := by ring
    rw [hsplit]
    have ha1 := abs_add_le (u (x + T • e3 0) - u (p + T • e3 0) + (u (p + T • e3 0) - u_plus (proj2 p)))
      (u_plus (proj2 p) - u_plus (proj2 x))
    have ha2 := abs_add_le (u (x + T • e3 0) - u (p + T • e3 0)) (u (p + T • e3 0) - u_plus (proj2 p))
    linarith
  have hd1_all (i : Fin 3) :
      ∃ g_lim : Space → ℝ,
        (∀ x y, |g_lim y - g_lim x| ≤ (3 * C2) * ‖y - x‖) ∧
        (∀ x, HasDerivAt (fun s : ℝ => u_plus (proj2 (x + s • e3 i))) (g_lim x) 0) ∧
        (∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
          ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |pd3 u i (x + T • e3 0) - g_lim x| ≤ ε) := by
    refine uniform_deriv_limit_of_shift (f := u) (g := pd3 u i) (f_lim := fun x => u_plus (proj2 x))
      (by positivity : 0 ≤ 3 * C2) i ?_ (hpd1_lip i) hconv0
    intro x
    have hlin : HasDerivAt (fun s : ℝ => x + s • e3 i) (e3 i) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e3 i)).const_add x
    have h := ((hu.regular.of_le (by norm_num)).differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 hlin
    exact h.congr_deriv (by unfold pd3; simp)
  let g1_lim (i : Fin 3) : Space → ℝ := (hd1_all i).choose
  have hg1_lip (i : Fin 3) : ∀ x y, |g1_lim i y - g1_lim i x| ≤ (3 * C2) * ‖y - x‖ :=
    (hd1_all i).choose_spec.1
  have hg1_deriv (i : Fin 3) : ∀ x, HasDerivAt (fun s : ℝ => u_plus (proj2 (x + s • e3 i))) (g1_lim i x) 0 :=
    (hd1_all i).choose_spec.2.1
  have hg1_conv (i : Fin 3) : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |pd3 u i (x + T • e3 0) - g1_lim i x| ≤ ε :=
    (hd1_all i).choose_spec.2.2
  have hg1_0 (x : Space) : g1_lim 0 x = 0 := by
    have h1 := hg1_deriv 0 x
    have hconst : (fun s : ℝ => u_plus (proj2 (x + s • e3 0))) = fun _ => u_plus (proj2 x) := by
      ext s; congr 1; ext j; fin_cases j <;> simp [proj2, e3]
    rw [hconst] at h1
    exact h1.unique (hasDerivAt_const 0 _)
  have hg1_indep (i : Fin 3) (x : Space) : g1_lim i x = g1_lim i (mk3 0 (proj2 x)) := by
    have h1 := hg1_deriv i x
    have h2 := hg1_deriv i (mk3 0 (proj2 x))
    have heq : (fun s : ℝ => u_plus (proj2 (x + s • e3 i))) =
        fun s => u_plus (proj2 (mk3 0 (proj2 x) + s • e3 i)) := by
      ext s
      apply congrArg u_plus
      ext j; fin_cases j <;> fin_cases i <;> simp [proj2, mk3, e3]
    rw [heq] at h1
    exact h1.unique h2
  have hd2_all (i j : Fin 3) :
      ∃ h_lim : Space → ℝ,
        (∀ x y, |h_lim y - h_lim x| ≤ C3 * ‖y - x‖) ∧
        (∀ x, HasDerivAt (fun s : ℝ => g1_lim i (x + s • e3 j)) (h_lim x) 0) ∧
        (∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
          ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |pd32 u i j (x + T • e3 0) - h_lim x| ≤ ε) := by
    refine uniform_deriv_limit_of_shift (f := pd3 u i) (g := pd32 u i j) (f_lim := g1_lim i)
      hC3 j ?_ (fun x y => hpd3_lip x y i j) (hg1_conv i)
    intro x
    have h1c : ContDiff ℝ 1 (pd3 u i) :=
      (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hlin : HasDerivAt (fun s : ℝ => x + s • e3 j) (e3 j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (e3 j)).const_add x
    have h := (h1c.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 hlin
    exact h.congr_deriv (by unfold pd32 pd3; simp)
  let h2_lim (i j : Fin 3) : Space → ℝ := (hd2_all i j).choose
  have hh2_lip (i j : Fin 3) : ∀ x y, |h2_lim i j y - h2_lim i j x| ≤ C3 * ‖y - x‖ :=
    (hd2_all i j).choose_spec.1
  have hh2_deriv (i j : Fin 3) : ∀ x, HasDerivAt (fun s : ℝ => g1_lim i (x + s • e3 j)) (h2_lim i j x) 0 :=
    (hd2_all i j).choose_spec.2.1
  have hh2_conv (i j : Fin 3) : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε →
      ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R, |pd32 u i j (x + T • e3 0) - h2_lim i j x| ≤ ε :=
    (hd2_all i j).choose_spec.2.2
  have hh2_j0 (i : Fin 3) (x : Space) : h2_lim i 0 x = 0 := by
    have h1 := hh2_deriv i 0 x
    have hconst : (fun s : ℝ => g1_lim i (x + s • e3 0)) = fun _ => g1_lim i x := by
      ext s
      rw [hg1_indep i (x + s • e3 0), hg1_indep i x]
      apply congrArg (g1_lim i); apply congrArg (mk3 0)
      ext k; fin_cases k <;> simp [proj2, e3]
    rw [hconst] at h1
    exact h1.unique (hasDerivAt_const 0 _)
  have hh2_indep (i j : Fin 3) (x : Space) : h2_lim i j x = h2_lim i j (mk3 0 (proj2 x)) := by
    have h1 := hh2_deriv i j x
    have h2 := hh2_deriv i j (mk3 0 (proj2 x))
    have heq : (fun s : ℝ => g1_lim i (x + s • e3 j)) =
        fun s => g1_lim i (mk3 0 (proj2 x) + s • e3 j) := by
      ext s
      rw [hg1_indep i (x + s • e3 j), hg1_indep i (mk3 0 (proj2 x) + s • e3 j)]
      apply congrArg (g1_lim i); apply congrArg (mk3 0)
      ext k; fin_cases k <;> fin_cases j <;> simp [proj2, mk3, e3]
    rw [heq] at h1
    exact h1.unique h2
  let g2 (i : Fin 2) (y : Plane2) : ℝ := g1_lim i.succ (mk3 0 y)
  let h2 (i j : Fin 2) (y : Plane2) : ℝ := h2_lim i.succ j.succ (mk3 0 y)
  have hmk3_norm (y z : Plane2) : ‖mk3 0 z - mk3 0 y‖ = ‖z - y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1; simp [Fin.sum_univ_three, Fin.sum_univ_two, mk3]
  have hg2_lip (i : Fin 2) (y z : Plane2) : |g2 i z - g2 i y| ≤ (3 * C2) * ‖z - y‖ := by
    dsimp [g2]; rw [← hmk3_norm]; exact hg1_lip i.succ _ _
  have hh2_lip2 (i j : Fin 2) (y z : Plane2) : |h2 i j z - h2 i j y| ≤ C3 * ‖z - y‖ := by
    dsimp [h2]; rw [← hmk3_norm]; exact hh2_lip i.succ j.succ _ _
  have hu_plus_hasDeriv (i : Fin 2) (y : Plane2) :
      HasDerivAt (fun s : ℝ => u_plus (y + s • e2 i)) (g2 i y) 0 := by
    have h := hg1_deriv i.succ (mk3 0 y)
    have heq : (fun s : ℝ => u_plus (proj2 (mk3 0 y + s • e3 i.succ))) =
        fun s => u_plus (y + s • e2 i) := by
      ext s; rw [← mk3_add_e2, proj2_mk3]
    rwa [heq] at h
  have hg2_hasDeriv (i j : Fin 2) (y : Plane2) :
      HasDerivAt (fun s : ℝ => g2 i (y + s • e2 j)) (h2 i j y) 0 := by
    have h := hh2_deriv i.succ j.succ (mk3 0 y)
    have heq : (fun s : ℝ => g1_lim i.succ (mk3 0 y + s • e3 j.succ)) =
        fun s => g2 i (y + s • e2 j) := by
      ext s; dsimp [g2]; rw [← mk3_add_e2]
    rwa [heq] at h
  have hu_plus_fderiv (y : Plane2) :
      HasFDerivAt u_plus (g2 0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        g2 1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) y :=
    hasFDerivAt_of_lip_partials2 (by positivity) (hu_plus_hasDeriv 0) (hu_plus_hasDeriv 1)
      (hg2_lip 0) (hg2_lip 1) y
  have hg2_fderiv (i : Fin 2) (y : Plane2) :
      HasFDerivAt (g2 i) (h2 i 0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        h2 i 1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) y :=
    hasFDerivAt_of_lip_partials2 hC3 (hg2_hasDeriv i 0) (hg2_hasDeriv i 1)
      (hh2_lip2 i 0) (hh2_lip2 i 1) y
  have hpd2_eq (i : Fin 2) (y : Plane2) : pd2 u_plus i y = g2 i y := by
    unfold pd2
    rw [(hu_plus_fderiv y).fderiv]
    fin_cases i <;> simp [e2]
  have hpd22_eq (i j : Fin 2) (y : Plane2) : pd22 u_plus i j y = h2 i j y := by
    unfold pd22
    have heq : pd2 u_plus i = g2 i := funext (hpd2_eq i)
    rw [heq]
    unfold pd2
    rw [(hg2_fderiv i y).fderiv]
    fin_cases j <;> simp [e2]
  have hh2_cont (i j : Fin 2) : Continuous (h2 i j) := by
    rw [Metric.continuous_iff]
    intro y ε hε
    refine ⟨ε / (C3 + 1), by positivity, fun z hz => ?_⟩
    rw [Real.dist_eq]
    have h1 := hh2_lip2 i j y z
    rw [← dist_eq_norm] at h1
    calc |h2 i j z - h2 i j y| ≤ C3 * dist z y := h1
      _ ≤ C3 * (ε / (C3 + 1)) := mul_le_mul_of_nonneg_left hz.le hC3
      _ < ε := by
          have : C3 / (C3 + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
          have h2' : C3 * (ε / (C3 + 1)) = ε * (C3 / (C3 + 1)) := by ring
          rw [h2']; nlinarith
  have hg2_c1 (i : Fin 2) : ContDiff ℝ 1 (g2 i) := by
    rw [contDiff_one_iff_fderiv]
    refine ⟨fun y => (hg2_fderiv i y).differentiableAt, ?_⟩
    have heq : fderiv ℝ (g2 i) = fun y =>
        h2 i 0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        h2 i 1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) :=
      funext fun y => (hg2_fderiv i y).fderiv
    rw [heq]
    exact ((hh2_cont i 0).smul continuous_const).add ((hh2_cont i 1).smul continuous_const)
  have hu_plus_c2 : ContDiff ℝ 2 u_plus := by
    rw [show (2 : WithTop ℕ∞) = (1 : WithTop ℕ∞) + 1 by norm_num, contDiff_succ_iff_fderiv]
    refine ⟨fun y => (hu_plus_fderiv y).differentiableAt, by simp, ?_⟩
    have heq : fderiv ℝ u_plus = fun y =>
        g2 0 y • EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2) +
        g2 1 y • EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2) :=
      funext fun y => (hu_plus_fderiv y).fderiv
    rw [heq]
    exact ((hg2_c1 0).smul contDiff_const).add ((hg2_c1 1).smul contDiff_const)
  have hpd2_bound (y : Plane2) (i : Fin 2) : |pd2 u_plus i y| ≤ C1 := by
    rw [hpd2_eq]
    by_contra! hgt
    let ε := (|g2 i y| - C1) / 2
    let x := mk3 0 y
    let R := max (|x 0|) (max (|x 1|) (|x 2|))
    obtain ⟨T0, hT0⟩ := hg1_conv i.succ R (le_trans (abs_nonneg _) (le_max_left _ _)) ε (by dsimp [ε]; linarith)
    have hxR : x ∈ Q3 R := by
      intro k; rw [Set.mem_Icc, ← abs_le]
      fin_cases k
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hclose := hT0 T0 le_rfl x hxR
    have htri : |g2 i y| ≤ |pd3 u i.succ (x + T0 • e3 0)| + |pd3 u i.succ (x + T0 • e3 0) - g2 i y| := by
      have : g2 i y = pd3 u i.succ (x + T0 • e3 0) - (pd3 u i.succ (x + T0 • e3 0) - g2 i y) := by ring
      conv_lhs => rw [this]
      exact abs_sub _ _
    have hb := hpd1 (x + T0 • e3 0) i.succ
    dsimp [g2, x, ε] at htri hclose ⊢
    linarith
  have hpd22_bound (y : Plane2) (i j : Fin 2) : |pd22 u_plus i j y| ≤ C2 := by
    rw [hpd22_eq]
    by_contra! hgt
    let ε := (|h2 i j y| - C2) / 2
    let x := mk3 0 y
    let R := max (|x 0|) (max (|x 1|) (|x 2|))
    obtain ⟨T0, hT0⟩ := hh2_conv i.succ j.succ R (le_trans (abs_nonneg _) (le_max_left _ _)) ε (by dsimp [ε]; linarith)
    have hxR : x ∈ Q3 R := by
      intro k; rw [Set.mem_Icc, ← abs_le]
      fin_cases k
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hclose := hT0 T0 le_rfl x hxR
    have htri : |h2 i j y| ≤ |pd32 u i.succ j.succ (x + T0 • e3 0)| +
        |pd32 u i.succ j.succ (x + T0 • e3 0) - h2 i j y| := by
      have : h2 i j y = pd32 u i.succ j.succ (x + T0 • e3 0) -
          (pd32 u i.succ j.succ (x + T0 • e3 0) - h2 i j y) := by ring
      conv_lhs => rw [this]
      exact abs_sub _ _
    have hb := hpd2 (x + T0 • e3 0) i.succ j.succ
    dsimp [h2, x, ε] at htri hclose ⊢
    linarith
  have hpde2 (y : Plane2) : (Δ u_plus y) + u_plus y - (u_plus y) ^ 3 = 0 := by
    have hlap2 : (Δ u_plus) y = pd22 u_plus 0 0 y + pd22 u_plus 1 1 y := by
      let b := EuclideanSpace.basisFun (Fin 2) ℝ
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u_plus b]
      dsimp only
      rw [Fin.sum_univ_two]
      have hterm (i : Fin 2) : iteratedFDeriv ℝ 2 u_plus y ![b i, b i] = pd22 u_plus i i y := by
        have hb : b i = e2 i := by ext j; simp [b, e2, EuclideanSpace.basisFun_apply]
        have hF : ContDiff ℝ 1 (fderiv ℝ u_plus) := hu_plus_c2.fderiv_right (by norm_num)
        rw [iteratedFDeriv_two_apply, hb]
        unfold pd22 pd2
        rw [fderiv_clm_apply (hF.differentiable one_ne_zero y) (differentiableAt_const (e2 i))]
        simp
      rw [hterm 0, hterm 1]
    have hlap3 (x : Space) : (Δ u) x = pd32 u 0 0 x + pd32 u 1 1 x + pd32 u 2 2 x := by
      let b := EuclideanSpace.basisFun (Fin 3) ℝ
      rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
      dsimp only
      rw [Fin.sum_univ_three]
      have hterm (i : Fin 3) : iteratedFDeriv ℝ 2 u x ![b i, b i] = pd32 u i i x := by
        have hb : b i = e3 i := by ext j; simp [b, e3, EuclideanSpace.basisFun_apply]
        have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.regular.fderiv_right (by norm_num)
        rw [iteratedFDeriv_two_apply, hb]
        unfold pd32 pd3
        rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const (e3 i))]
        simp
      rw [hterm 0, hterm 1, hterm 2]
    rw [hlap2, hpd22_eq 0 0 y, hpd22_eq 1 1 y]
    let x := mk3 0 y
    let R := max (|x 0|) (max (|x 1|) (|x 2|))
    have hR : 0 ≤ R := le_trans (abs_nonneg _) (le_max_left _ _)
    have hxR : x ∈ Q3 R := by
      intro k; rw [Set.mem_Icc, ← abs_le]
      fin_cases k
      · exact le_max_left _ _
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hsmall : ∀ ε : ℝ, 0 < ε → |h2 0 0 y + h2 1 1 y + u_plus y - u_plus y ^ 3| ≤ ε := by
      intro ε hε
      obtain ⟨T0, hT0⟩ := hconv0 R hR (ε / 16) (by positivity)
      obtain ⟨T1, hT1⟩ := hh2_conv 0 0 R hR (ε / 16) (by positivity)
      obtain ⟨T2, hT2⟩ := hh2_conv 1 1 R hR (ε / 16) (by positivity)
      obtain ⟨T3, hT3⟩ := hh2_conv 2 2 R hR (ε / 16) (by positivity)
      let T := max (max T0 T1) (max T2 T3)
      have ha0 := hT0 T (le_trans (le_max_left _ _) (le_max_left _ _)) x hxR
      have ha1 := hT1 T (le_trans (le_max_right _ _) (le_max_left _ _)) x hxR
      have ha2 := hT2 T (le_trans (le_max_left _ _) (le_max_right _ _)) x hxR
      have ha3 := hT3 T (le_trans (le_max_right _ _) (le_max_right _ _)) x hxR
      rw [proj2_mk3] at ha0
      rw [hh2_j0 0 x, sub_zero] at ha1
      have hsol := hu.solution (x + T • e3 0)
      rw [hlap3] at hsol
      have hcub : |u (x + T • e3 0) ^ 3 - u_plus y ^ 3| ≤ 3 * (ε / 16) := by
        have hfac : u (x + T • e3 0) ^ 3 - u_plus y ^ 3 =
            (u (x + T • e3 0) - u_plus y) *
              (u (x + T • e3 0) ^ 2 + u (x + T • e3 0) * u_plus y + u_plus y ^ 2) := by ring
        rw [hfac, abs_mul]
        have h1 := hu1 (x + T • e3 0)
        have h2' := hu_plus_abs y
        have h3 : |u (x + T • e3 0) ^ 2 + u (x + T • e3 0) * u_plus y + u_plus y ^ 2| ≤ 3 := by
          have hb1 : u (x + T • e3 0) ^ 2 ≤ 1 := by
            rw [← sq_abs (u (x + T • e3 0))]; nlinarith [abs_nonneg (u (x + T • e3 0))]
          have hb2 : u_plus y ^ 2 ≤ 1 := by
            rw [← sq_abs (u_plus y)]; nlinarith [abs_nonneg (u_plus y)]
          have hb3 : |u (x + T • e3 0) * u_plus y| ≤ 1 := by
            rw [abs_mul]; nlinarith [abs_nonneg (u (x + T • e3 0)), abs_nonneg (u_plus y)]
          rw [abs_le]; constructor <;> linarith [abs_le.mp hb3, sq_nonneg (u (x + T • e3 0)), sq_nonneg (u_plus y)]
        nlinarith [abs_nonneg (u (x + T • e3 0) - u_plus y),
          abs_nonneg (u (x + T • e3 0) ^ 2 + u (x + T • e3 0) * u_plus y + u_plus y ^ 2)]
      have hdiff : h2 0 0 y + h2 1 1 y + u_plus y - u_plus y ^ 3 =
          -(pd32 u 0 0 (x + T • e3 0)) -
          (pd32 u 1 1 (x + T • e3 0) - h2 0 0 y) -
          (pd32 u 2 2 (x + T • e3 0) - h2 1 1 y) -
          (u (x + T • e3 0) - u_plus y) +
          (u (x + T • e3 0) ^ 3 - u_plus y ^ 3) := by
        dsimp [h2, x]
        linarith
      rw [hdiff]
      have habs : ∀ a b c d e : ℝ, |a - b - c - d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
        intro a b c d e
        have h1 := abs_add_le (a - b - c - d) e
        have h2 := abs_sub (a - b - c) d
        have h3 := abs_sub (a - b) c
        have h4 := abs_sub a b
        linarith
      have hbound := habs (-(pd32 u 0 0 (x + T • e3 0))) (pd32 u 1 1 (x + T • e3 0) - h2 0 0 y)
        (pd32 u 2 2 (x + T • e3 0) - h2 1 1 y) (u (x + T • e3 0) - u_plus y)
        (u (x + T • e3 0) ^ 3 - u_plus y ^ 3)
      rw [abs_neg] at hbound
      dsimp [h2, x] at hbound ha2 ha3 ⊢
      linarith
    by_contra hne
    have hpos_val : 0 < |h2 0 0 y + h2 1 1 y + u_plus y - u_plus y ^ 3| := abs_pos.mpr hne
    have := hsmall (|h2 0 0 y + h2 1 1 y + u_plus y - u_plus y ^ 3| / 2) (half_pos hpos_val)
    linarith
  refine ⟨u_plus, hu_plus_c2, hu_plus_abs, hpde2, hpd2_bound, hpd22_bound, ?_⟩
  intro R hR ε hε
  obtain ⟨T_u, hT_u⟩ := hconv0 R hR ε hε
  obtain ⟨T_g0, hT_g0⟩ := hg1_conv 0 R hR ε hε
  obtain ⟨T_g1, hT_g1⟩ := hg1_conv 1 R hR ε hε
  obtain ⟨T_g2, hT_g2⟩ := hg1_conv 2 R hR ε hε
  obtain ⟨T_h00, hT_h00⟩ := hh2_conv 0 0 R hR ε hε
  obtain ⟨T_h10, hT_h10⟩ := hh2_conv 1 0 R hR ε hε
  obtain ⟨T_h20, hT_h20⟩ := hh2_conv 2 0 R hR ε hε
  obtain ⟨T_h11, hT_h11⟩ := hh2_conv 1 1 R hR ε hε
  obtain ⟨T_h12, hT_h12⟩ := hh2_conv 1 2 R hR ε hε
  obtain ⟨T_h21, hT_h21⟩ := hh2_conv 2 1 R hR ε hε
  obtain ⟨T_h22, hT_h22⟩ := hh2_conv 2 2 R hR ε hε
  let T0 := max (max (max T_u T_g0) (max T_g1 T_g2))
    (max (max (max T_h00 T_h10) (max T_h20 T_h11)) (max (max T_h12 T_h21) T_h22))
  refine ⟨T0, fun T hT x hx => ?_⟩
  have hTu : T_u ≤ T := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTg0 : T_g0 ≤ T := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hT
  have hTg1 : T_g1 ≤ T := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hT
  have hTg2 : T_g2 ≤ T := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hT
  have hTh00 : T_h00 ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_right _ _)) hT
  have hTh10 : T_h10 ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) (le_max_right _ _)) hT
  have hTh20 : T_h20 ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_right _ _)) hT
  have hTh11 : T_h11 ≤ T := le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) (le_max_right _ _)) hT
  have hTh12 : T_h12 ≤ T := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _) |>.trans (le_max_right _ _)) hT
  have hTh21 : T_h21 ≤ T := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _) |>.trans (le_max_right _ _)) hT
  have hTh22 : T_h22 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _) |>.trans (le_max_right _ _)) hT
  refine ⟨hT_u T hTu x hx, ?_, ?_, ?_, ?_⟩
  · simpa [hg1_0 x] using hT_g0 T hTg0 x hx
  · intro i
    rw [hpd2_eq i (proj2 x)]
    dsimp [g2]
    rw [← hg1_indep i.succ x]
    fin_cases i
    · exact hT_g1 T hTg1 x hx
    · exact hT_g2 T hTg2 x hx
  · intro k
    fin_cases k
    · simpa [hh2_j0 0 x] using hT_h00 T hTh00 x hx
    · simpa [hh2_j0 1 x] using hT_h10 T hTh10 x hx
    · simpa [hh2_j0 2 x] using hT_h20 T hTh20 x hx
  · intro i j
    rw [hpd22_eq i j (proj2 x)]
    dsimp [h2]
    rw [← hh2_indep i.succ j.succ x]
    fin_cases i <;> fin_cases j
    · exact hT_h11 T hTh11 x hx
    · exact hT_h12 T hTh12 x hx
    · exact hT_h21 T hTh21 x hx
    · exact hT_h22 T hTh22 x hx

end Mod2

namespace Mod3
open InnerProductSpace MeasureTheory Filter Set Metric
open scoped Topology Laplacian
private theorem continuous_mk3 : Continuous (fun p : ℝ × Plane2 => mk3 p.1 p.2) := by
  refine (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp ?_
  rw [continuous_pi_iff]
  intro k; fin_cases k
  · exact continuous_fst
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp continuous_snd
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp continuous_snd

private theorem continuous_proj2 : Continuous proj2 := by
  refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
  rw [continuous_pi_iff]
  intro k; fin_cases k
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3)).continuous
  · exact (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous

private theorem partial_comm3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x : Space) (i j : Fin 3) :
    pd32 u i j x = pd32 u j i x := by
  have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hd (a b : Fin 3) : pd32 u a b x = (fderiv ℝ (fderiv ℝ u) x (e3 b)) (e3 a) := by
    unfold pd32 pd3
    rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const (e3 a))]
    simp
  rw [hd i j, hd j i]
  exact (hu.contDiffAt.isSymmSndFDerivAt (by simp)) (e3 j) (e3 i)

private theorem laplacian_sum3 {u : Space → ℝ} (hu : ContDiff ℝ 2 u) (x : Space) :
    (Δ u) x = pd32 u 0 0 x + pd32 u 1 1 x + pd32 u 2 2 x := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis u b]
  dsimp only
  rw [Fin.sum_univ_three]
  have ht (i : Fin 3) : iteratedFDeriv ℝ 2 u x ![b i, b i] = pd32 u i i x := by
    have hb : b i = e3 i := by ext j; simp [b, e3, EuclideanSpace.basisFun_apply]
    have hF : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
    rw [iteratedFDeriv_two_apply, hb]
    unfold pd32 pd3
    rw [fderiv_clm_apply (hF.differentiable one_ne_zero x) (differentiableAt_const (e3 i))]
    simp
  rw [ht 0, ht 1, ht 2]

private noncomputable def cut3D (R : ℝ) (x : Space) : ℝ :=
  cut1 R (x 0) * cut1 R (x 1) * cut1 R (x 2)

private theorem contDiff_cut3D (R : ℝ) : ContDiff ℝ 1 (cut3D R) := by
  have hc (i : Fin 3) : ContDiff ℝ 1 (fun x : Space => cut1 R (x i)) :=
    (contDiff_cut1 R).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  exact ((hc 0).mul (hc 1)).mul (hc 2)

private theorem cut3D_bounds (R : ℝ) (x : Space) : 0 ≤ cut3D R x ∧ cut3D R x ≤ 1 := by
  have h0 := cut1_bounds R (x 0)
  have h1 := cut1_bounds R (x 1)
  have h2 := cut1_bounds R (x 2)
  exact ⟨mul_nonneg (mul_nonneg h0.1 h1.1) h2.1,
    mul_le_one₀ (mul_le_one₀ h0.2 h1.1 h1.2) h2.1 h2.2⟩

private theorem cut3D_one {R : ℝ} {x : Space} (hx : x ∈ Q3 (R - 1)) : cut3D R x = 1 := by
  unfold cut3D
  rw [cut1_one (hx 0), cut1_one (hx 1), cut1_one (hx 2), mul_one, mul_one]

private theorem cut3D_zero_of_coord {R : ℝ} {x : Space} {i : Fin 3} (hi : R ≤ |x i|) :
    cut3D R x = 0 := by
  unfold cut3D
  fin_cases i
  · rw [cut1_zero (s := x 0) (by simpa using hi), zero_mul, zero_mul]
  · rw [cut1_zero (s := x 1) (by simpa using hi), mul_zero, zero_mul]
  · rw [cut1_zero (s := x 2) (by simpa using hi), mul_zero]

private theorem pd3_cut3D_abs_le (R : ℝ) (i : Fin 3) (x : Space) : |pd3 (cut3D R) i x| ≤ 3 := by
  have hline := line_deriv3 (contDiff_cut3D R) x (e3 i) 0
  simp only [zero_smul, add_zero] at hline
  have hcoord (j : Fin 3) (s : ℝ) : (x + s • e3 i) j = x j + if j = i then s else 0 := by
    simp [e3, eq_comm]
  have hterm (j : Fin 3) : HasDerivAt (fun s : ℝ => cut1 R ((x + s • e3 i) j))
      (if j = i then deriv (cut1 R) (x j) else 0) 0 := by
    simp_rw [hcoord j]
    by_cases hji : j = i
    · subst hji
      simp only [↓reduceIte]
      have ha : HasDerivAt (fun s : ℝ => x j + s) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (x j)
      have hb : HasDerivAt (cut1 R) (deriv (cut1 R) (x j)) (x j + 0) := by
        simpa using ((contDiff_cut1 R).differentiable one_ne_zero (x j)).hasDerivAt
      have hc := hb.comp 0 ha
      rw [mul_one] at hc; exact hc
    · simp only [hji, ↓reduceIte, add_zero]
      exact hasDerivAt_const 0 _
  have h3 := ((hterm 0).fun_mul (hterm 1)).fun_mul (hterm 2)
  have huq := hline.unique h3
  change pd3 (cut3D R) i x = _ at huq
  rw [huq]
  have hb0 := cut1_bounds R (x 0)
  have hb1 := cut1_bounds R (x 1)
  have hb2 := cut1_bounds R (x 2)
  have hd0 := deriv_cut1_abs_le R (x 0)
  have hd1 := deriv_cut1_abs_le R (x 1)
  have hd2 := deriv_cut1_abs_le R (x 2)
  fin_cases i <;> simp [e3]
  · rw [abs_of_nonneg hb1.1, abs_of_nonneg hb2.1]
    have h12 : cut1 R (x 1) * cut1 R (x 2) ≤ 1 := mul_le_one₀ hb1.2 hb2.1 hb2.2
    nlinarith [abs_nonneg (deriv (cut1 R) (x 0))]
  · rw [abs_of_nonneg hb0.1, abs_of_nonneg hb2.1]
    have h02 : cut1 R (x 0) * cut1 R (x 2) ≤ 1 := mul_le_one₀ hb0.2 hb2.1 hb2.2
    nlinarith [abs_nonneg (deriv (cut1 R) (x 1))]
  · rw [abs_of_nonneg hb0.1, abs_of_nonneg hb1.1]
    have h01 : cut1 R (x 0) * cut1 R (x 1) ≤ 1 := mul_le_one₀ hb0.2 hb1.1 hb1.2
    nlinarith [abs_nonneg (deriv (cut1 R) (x 2))]

private theorem pd3_cut3D_zero_of_mem {R : ℝ} {x : Space} (hx : x ∈ Q3 (R - 1)) (i : Fin 3) :
    pd3 (cut3D R) i x = 0 := by
  have hline := line_deriv3 (contDiff_cut3D R) x (e3 i) 0
  simp only [zero_smul, add_zero] at hline
  have hcoord (j : Fin 3) (s : ℝ) : (x + s • e3 i) j = x j + if j = i then s else 0 := by
    simp [e3, eq_comm]
  have hterm (j : Fin 3) : HasDerivAt (fun s : ℝ => cut1 R ((x + s • e3 i) j)) 0 0 := by
    simp_rw [hcoord j]
    by_cases hji : j = i
    · subst hji
      simp only [↓reduceIte]
      have ha : HasDerivAt (fun s : ℝ => x j + s) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (x j)
      have hb : HasDerivAt (cut1 R) (deriv (cut1 R) (x j)) (x j + 0) := by
        simpa using ((contDiff_cut1 R).differentiable one_ne_zero (x j)).hasDerivAt
      have hc := hb.comp 0 ha
      rw [deriv_cut1_zero_inner (hx j), zero_mul] at hc
      exact hc
    · simp only [hji, ↓reduceIte, add_zero]
      exact hasDerivAt_const 0 _
  have h3 := ((hterm 0).fun_mul (hterm 1)).fun_mul (hterm 2)
  have huq := hline.unique h3
  change pd3 (cut3D R) i x = _ at huq
  rw [huq]; ring

private theorem measurableSet_Q3 (R : ℝ) : MeasurableSet (Q3 R) := by
  have heq : Q3 R = ⋂ i : Fin 3, (fun x : Space => x i) ⁻¹' Icc (-R) R := by
    ext x; simp [Q3]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

private theorem measurableSet_Q2 (R : ℝ) : MeasurableSet (Q2 R) := by
  have heq : Q2 R = ⋂ i : Fin 2, (fun y : Plane2 => y i) ⁻¹' Icc (-R) R := by
    ext y; simp [Q2]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    measurableSet_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable

private theorem isCompact_Q3_c (R : ℝ) : IsCompact (Q3 R) := by
  have h1 : Q3 R = (EuclideanSpace.equiv (Fin 3) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 3 => Icc (-R) R) := by
    ext x
    constructor
    · intro hx; exact ⟨fun i => x i, fun i _ => hx i, by ext i; simp⟩
    · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
  rw [h1]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image
    (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous

private theorem isCompact_Q2_c (R : ℝ) : IsCompact (Q2 R) := by
  have h1 : Q2 R = (EuclideanSpace.equiv (Fin 2) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 2 => Icc (-R) R) := by
    ext y
    constructor
    · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
    · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
  rw [h1]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous

private theorem volume_Q3 {R : ℝ} (hR : 0 ≤ R) :
    volume (Q3 R) = ENNReal.ofReal ((2 * R) ^ 3) := by
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  have hpre : (WithLp.toLp 2 : (Fin 3 → ℝ) → Space) ⁻¹' Q3 R =
      Set.pi Set.univ (fun _ : Fin 3 => Icc (-R) R) := by
    ext f
    constructor
    · intro h i _; exact h i
    · intro h i; exact h i (Set.mem_univ i)
  rw [← hmp.measure_preimage (measurableSet_Q3 R).nullMeasurableSet, hpre,
    volume_pi_pi (fun _ : Fin 3 => Icc (-R) R)]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by linarith)]
  congr 2; ring

private theorem setIntegral_Q3_deriv_eq_zero {R : ℝ} (hR : 0 ≤ R) (j : Fin 3)
    {F G : Space → ℝ} (hGc : Continuous G)
    (hd : ∀ x, HasDerivAt (fun s : ℝ => F (x + s • e3 j)) (G x) 0)
    (hbdy : ∀ x, |x j| = R → F x = 0) :
    (∫ x in Q3 R, G x) = 0 := by
  let e1 : Space ≃ᵐ (Fin 3 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e2 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j
  let e : Space ≃ᵐ ℝ × (Fin 2 → ℝ) := e1.trans e2
  have hmp : MeasurePreserving e volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) j)
  let S2 : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ : Fin 2 => Icc (-R) R)
  have hS2 : MeasurableSet S2 := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hpre : e ⁻¹' (Icc (-R) R ×ˢ S2) = Q3 R := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, S2, Set.mem_univ_pi, Q3, e, e1, e2,
      MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply]
    constructor
    · rintro ⟨hj, hrest⟩ i
      by_cases hij : i = j
      · subst hij; exact hj
      · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
        exact hrest k
    · intro hx
      exact ⟨hx j, fun k => hx (j.succAbove k)⟩
  have hchg : (∫ x in Q3 R, G x) = ∫ p in Icc (-R) R ×ˢ S2, G (e.symm p) := by
    have h1 : (∫ x in Q3 R, G x) = ∫ x in e ⁻¹' (Icc (-R) R ×ˢ S2), (G ∘ e.symm) (e x) := by
      rw [hpre]
      apply setIntegral_congr_fun (measurableSet_Q3 R)
      intro x _; simp
    rw [h1, hmp.setIntegral_preimage_emb e.measurableEmbedding (G ∘ e.symm) (Icc (-R) R ×ˢ S2)]
    rfl
  rw [hchg]
  have hint_prod : IntegrableOn (fun p : ℝ × (Fin 2 → ℝ) => G (e.symm p)) (Icc (-R) R ×ˢ S2) volume := by
    have hcomp : IntegrableOn (G ∘ e.symm ∘ e) (e ⁻¹' (Icc (-R) R ×ˢ S2)) volume := by
      rw [hpre]
      exact (hGc.continuousOn.integrableOn_compact (isCompact_Q3_c R)).congr_fun
        (fun x _ => by simp) (measurableSet_Q3 R)
    exact (hmp.integrableOn_comp_preimage e.measurableEmbedding).mp hcomp
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint_prod,
    integral_integral_swap (by rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hint_prod)]
  have hslice (y : Fin 2 → ℝ) : (∫ t in Icc (-R) R, G (e.symm (t, y))) = 0 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    let γ (t : ℝ) : Space := e.symm (t, y)
    have hγ_add (t s : ℝ) : γ (t + s) = γ t + s • e3 j := by
      ext k
      have hk (u : ℝ) : (γ u) k = j.insertNth (α := fun _ => ℝ) u y k := by
        simp [γ, e, e1, e2, MeasurableEquiv.piFinSuccAbove_symm_apply]
      rw [hk (t + s), PiLp.add_apply, hk t, PiLp.smul_apply, smul_eq_mul]
      by_cases hkj : k = j
      · subst hkj; simp [e3]
      · obtain ⟨m, rfl⟩ := Fin.exists_succAbove_eq hkj
        simp [e3, Fin.succAbove_ne]
    have hγ_deriv (t : ℝ) : HasDerivAt (fun u : ℝ => F (γ u)) (G (γ t)) t := by
      have h1 := hd (γ t)
      have hsub : HasDerivAt (fun u : ℝ => u - t) 1 t := by
        simpa using (hasDerivAt_id t).sub_const t
      have h1' : HasDerivAt (fun u : ℝ => F (γ t + u • e3 j)) (G (γ t)) ((fun u => u - t) t) := by
        simpa only [sub_self] using h1
      have hcomp := HasDerivAt.comp (h := fun u => u - t) t h1' hsub
      simp only [mul_one] at hcomp
      have hfun : (fun u : ℝ => F (γ t + (u - t) • e3 j)) = fun u => F (γ u) := by
        ext u; rw [← hγ_add, add_sub_cancel]
      exact hfun ▸ hcomp
    have hγ_cont : Continuous (fun t : ℝ => G (γ t)) := by
      have hγc : Continuous γ := by
        have hlin : Continuous (fun t : ℝ => γ 0 + t • e3 j) :=
          continuous_const.add (continuous_id.smul continuous_const)
        exact hlin.congr fun t => by rw [← hγ_add, zero_add]
      exact hGc.comp hγc
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hγ_deriv t)
      (hγ_cont.intervalIntegrable (-R) R)]
    have hγj (u : ℝ) : (γ u) j = u := by
      simp [γ, e, e1, e2, MeasurableEquiv.piFinSuccAbove_symm_apply]
    have hR1 : F (γ R) = 0 := hbdy (γ R) (by rw [hγj, abs_of_nonneg hR])
    have hR2 : F (γ (-R)) = 0 := hbdy (γ (-R)) (by rw [hγj, abs_neg, abs_of_nonneg hR])
    rw [hR1, hR2, sub_self]
  simp only [hslice, integral_zero]

private theorem setIntegral_Q3_proj2 {R : ℝ} (hR : 0 ≤ R) {g : Plane2 → ℝ} (hg : Continuous g) :
    (∫ x in Q3 R, g (proj2 x)) = 2 * R * ∫ y in Q2 R, g y := by
  let e1 : Space ≃ᵐ (Fin 3 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e2 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e3m : (Fin 2 → ℝ) ≃ᵐ Plane2 := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  let e : Space ≃ᵐ ℝ × Plane2 := (e1.trans e2).trans (MeasurableEquiv.refl ℝ |>.prodCongr e3m)
  have hmp : MeasurePreserving e volume volume :=
    ((PiLp.volume_preserving_ofLp (Fin 3)).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2)))
  have he1 (x : Space) : (e x).1 = x 0 := rfl
  have he2 (x : Space) : (e x).2 = proj2 x := by
    ext k; fin_cases k <;> rfl
  have hpre : e ⁻¹' (Icc (-R) R ×ˢ Q2 R) = Q3 R := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, Q2, Q3, he1, he2]
    constructor
    · rintro ⟨h0, hrest⟩ i
      fin_cases i
      · exact h0
      · simpa [proj2] using hrest 0
      · simpa [proj2] using hrest 1
    · intro hx
      refine ⟨hx 0, fun k => ?_⟩
      fin_cases k
      · simpa [proj2] using hx 1
      · simpa [proj2] using hx 2
  have heq : (∫ x in Q3 R, g (proj2 x)) = ∫ x in e ⁻¹' (Icc (-R) R ×ˢ Q2 R), (fun p : ℝ × Plane2 => g p.2) (e x) := by
    rw [hpre]
    apply setIntegral_congr_fun (measurableSet_Q3 R)
    intro x _
    simp [he2 x]
  rw [heq, hmp.setIntegral_preimage_emb e.measurableEmbedding (fun p : ℝ × Plane2 => g p.2) (Icc (-R) R ×ˢ Q2 R)]
  have hint : IntegrableOn (fun p : ℝ × Plane2 => g p.2) (Icc (-R) R ×ˢ Q2 R) volume :=
    (hg.comp continuous_snd).continuousOn.integrableOn_compact (isCompact_Icc.prod (isCompact_Q2_c R))
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]
  dsimp only
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R),
    smul_eq_mul]
  ring

private theorem hasDerivAt_integral_param_upper
    {a : ℝ} {g : ℝ → ℝ} {g' : ℝ} {F F' : ℝ → ℝ → ℝ}
    (hg : HasDerivAt g g' 0)
    (hF_cont : Continuous (Function.uncurry F))
    (hF'_cont : Continuous (Function.uncurry F'))
    (hF_deriv : ∀ r s, HasDerivAt (F r) (F' r s) s) :
    HasDerivAt (fun s : ℝ => ∫ r in a..g s, F r s)
      (F (g 0) 0 * g' + ∫ r in a..g 0, F' r 0) 0 := by
  let b := g 0
  have hpart1 : HasDerivAt (fun s : ℝ => ∫ r in a..b, F r s) (∫ r in a..b, F' r 0) 0 := by
    let K : Set (ℝ × ℝ) := uIcc a b ×ˢ Icc (-1) 1
    have hK : IsCompact K := isCompact_uIcc.prod isCompact_Icc
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hF'_cont.continuousOn
    have hS : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    have hF_meas (s : ℝ) : AEStronglyMeasurable (fun r => F r s) (volume.restrict (uIoc a b)) :=
      (hF_cont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    have hF0_int : IntervalIntegrable (fun r => F r 0) volume a b :=
      (hF_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
    have hF'_meas : AEStronglyMeasurable (fun r => F' r 0) (volume.restrict (uIoc a b)) :=
      (hF'_cont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    have hres := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun s r => F r s) (F' := fun s r => F' r s) (bound := fun _ => M)
      hS (Eventually.of_forall hF_meas) hF0_int hF'_meas
      (ae_of_all _ fun r hr s hs => hM (r, s) ⟨uIoc_subset_uIcc hr, hs⟩)
      intervalIntegrable_const
      (ae_of_all _ fun r _ s _ => hF_deriv r s)
    exact hres.2
  have hpart2 : HasDerivAt (fun s : ℝ => ∫ r in b..g s, F r s) (F b 0 * g') 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have hg_slope : Tendsto (fun s : ℝ => s⁻¹ * (g s - b)) (𝓝[≠] (0 : ℝ)) (𝓝 g') := by
      have h := hasDerivAt_iff_tendsto_slope_zero.mp hg
      simpa [b, smul_eq_mul] using h
    have hM_ev : ∀ᶠ s in 𝓝[≠] (0 : ℝ), |s⁻¹ * (g s - b)| ≤ |g'| + 1 ∧
        |F b 0 * (s⁻¹ * (g s - b)) - F b 0 * g'| < ε / 2 := by
      have h1 := hg_slope (Metric.ball_mem_nhds g' one_pos)
      have h2 := ((tendsto_const_nhds (x := F b 0)).mul hg_slope)
        (Metric.ball_mem_nhds (F b 0 * g') (half_pos hε))
      filter_upwards [h1, h2] with s hs1 hs2
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hs1 hs2
      refine ⟨?_, hs2⟩
      have := abs_sub_abs_le_abs_sub (s⁻¹ * (g s - b)) g'
      linarith
    let η : ℝ := ε / (2 * (|g'| + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    have hF_at : ContinuousAt (Function.uncurry F) (b, 0) := hF_cont.continuousAt
    obtain ⟨δ1, hδ1, hF_close⟩ := Metric.continuousAt_iff.mp hF_at η hη
    obtain ⟨δ2, hδ2, hg_close⟩ := Metric.continuousAt_iff.mp hg.continuousAt δ1 hδ1
    obtain ⟨δ3, hδ3, hM_ball⟩ := Metric.mem_nhdsWithin_iff.mp hM_ev
    refine ⟨min (min δ1 δ2) δ3, lt_min (lt_min hδ1 hδ2) hδ3, fun s hs_ne hs_lt => ?_⟩
    rw [Real.dist_eq, sub_zero] at hs_lt
    have hs1 : |s| < δ1 := lt_of_lt_of_le hs_lt (le_trans (min_le_left _ _) (min_le_left _ _))
    have hs2 : |s| < δ2 := lt_of_lt_of_le hs_lt (le_trans (min_le_left _ _) (min_le_right _ _))
    have hs3 : |s| < δ3 := lt_of_lt_of_le hs_lt (min_le_right _ _)
    have hM_s := hM_ball ⟨by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact hs3, hs_ne⟩
    have hgs_close : |g s - b| < δ1 := by
      have := hg_close (by rw [Real.dist_eq, sub_zero]; exact hs2)
      rwa [Real.dist_eq] at this
    rw [Real.dist_eq, smul_eq_mul, zero_add, intervalIntegral.integral_same, sub_zero]
    have hsplit : (∫ r in b..g s, F r s) =
        F b 0 * (g s - b) + ∫ r in b..g s, (F r s - F b 0) := by
      have hconst : (∫ _r in b..g s, F b 0) = F b 0 * (g s - b) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
      have hsub := intervalIntegral.integral_sub
        ((hF_cont.comp (continuous_id.prodMk (continuous_const (y := s)))).intervalIntegrable (μ := volume) b (g s))
        (intervalIntegrable_const (μ := volume) (c := F b 0))
      dsimp only [Function.comp_def, Function.uncurry, id_eq] at hsub
      linarith
    rw [hsplit, mul_add]
    have hrem : |s⁻¹ * ∫ r in b..g s, (F r s - F b 0)| ≤ η * |s⁻¹ * (g s - b)| := by
      have hint_le : ‖∫ r in b..g s, (F r s - F b 0)‖ ≤ η * |g s - b| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro r hr
        rw [Real.norm_eq_abs]
        have hrb : |r - b| ≤ |g s - b| := by
          have hmem := Set.uIoc_subset_uIcc hr
          rw [Set.mem_uIcc] at hmem
          rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
          · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
        have hdist : dist (r, s) (b, 0) < δ1 := by
          rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
          exact max_lt (lt_of_le_of_lt hrb hgs_close) hs1
        exact (hF_close hdist).le
      rw [Real.norm_eq_abs] at hint_le
      rw [abs_mul, abs_mul]
      calc |s⁻¹| * |∫ r in b..g s, (F r s - F b 0)|
          ≤ |s⁻¹| * (η * |g s - b|) := mul_le_mul_of_nonneg_left hint_le (abs_nonneg _)
        _ = η * (|s⁻¹| * |g s - b|) := by ring
    have hrem_lt : |s⁻¹ * ∫ r in b..g s, (F r s - F b 0)| ≤ ε / 2 := by
      calc _ ≤ η * |s⁻¹ * (g s - b)| := hrem
        _ ≤ η * (|g'| + 1) := mul_le_mul_of_nonneg_left hM_s.1 hη.le
        _ = ε / 2 := by dsimp [η]; field_simp
    have htri : |s⁻¹ * (F b 0 * (g s - b)) + s⁻¹ * (∫ r in b..g s, (F r s - F b 0)) - F b 0 * g'| ≤
        |F b 0 * (s⁻¹ * (g s - b)) - F b 0 * g'| + |s⁻¹ * (∫ r in b..g s, (F r s - F b 0))| := by
      have hre : s⁻¹ * (F b 0 * (g s - b)) + s⁻¹ * (∫ r in b..g s, (F r s - F b 0)) - F b 0 * g' =
          (F b 0 * (s⁻¹ * (g s - b)) - F b 0 * g') + s⁻¹ * (∫ r in b..g s, (F r s - F b 0)) := by ring
      rw [hre]; exact abs_add_le _ _
    linarith [htri, hM_s.2, hrem_lt]
  have hsum := hpart2.fun_add hpart1
  have heq : (fun s : ℝ => (∫ r in b..g s, F r s) + ∫ r in a..b, F r s) =
      fun s => ∫ r in a..g s, F r s := by
    ext s
    rw [add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hF_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
      ((hF_cont.comp (continuous_id.prodMk continuous_const)).intervalIntegrable b (g s))
  rwa [heq] at hsum

private theorem implicit_tau_props {u : Space → ℝ} (hu : IsBoundedSol u)
    (hpos : ∀ x, 0 < pd3 u 0 x) {v : Space → ℝ} (hv_c1 : ContDiff ℝ 1 v)
    {T : ℝ} (hT : 0 < T)
    (hv_lo : ∀ x, u x ≤ v x) (hv_hi : ∀ x, v x ≤ u (x + T • e3 0)) :
    ∃ τ : Space → ℝ,
      (∀ x, τ x ∈ Icc (x 0) (x 0 + T)) ∧
      (∀ x, u (mk3 (τ x) (proj2 x)) = v x) ∧
      Continuous τ ∧
      (∀ (j : Fin 3) (x : Space),
        HasDerivAt (fun s : ℝ => τ (x + s • e3 j))
          (if j = 0 then pd3 v 0 x / pd3 u 0 (mk3 (τ x) (proj2 x))
           else (pd3 v j x - pd3 u j (mk3 (τ x) (proj2 x))) / pd3 u 0 (mk3 (τ x) (proj2 x))) 0) := by
  have hline_mono (y : Plane2) : StrictMono (fun s : ℝ => u (mk3 s y)) := by
    apply strictMono_of_deriv_pos
    intro s
    have h := line_deriv3 (hu.regular.of_le (by norm_num)) (mk3 0 y) (e3 0) s
    have heq : (fun r : ℝ => u (mk3 0 y + r • e3 0)) = fun r => u (mk3 r y) := by
      ext r; rw [mk3_add_e0, zero_add]
    rw [heq, mk3_add_e0, zero_add] at h
    rw [h.deriv]
    exact hpos _
  have hτ_ex (x : Space) : ∃ t ∈ Icc (x 0) (x 0 + T), u (mk3 t (proj2 x)) = v x := by
    have hcont : ContinuousOn (fun s : ℝ => u (mk3 s (proj2 x))) (Icc (x 0) (x 0 + T)) :=
      (hu.regular.continuous.comp (continuous_mk3.comp (continuous_id.prodMk continuous_const))).continuousOn
    have hlo : u (mk3 (x 0) (proj2 x)) ≤ v x := by rw [mk3_proj2]; exact hv_lo x
    have hhi : v x ≤ u (mk3 (x 0 + T) (proj2 x)) := by
      have hT' : mk3 (x 0 + T) (proj2 x) = x + T • e3 0 := by rw [← mk3_add_e0, mk3_proj2]
      rw [hT']; exact hv_hi x
    exact intermediate_value_Icc (by linarith) hcont ⟨hlo, hhi⟩
  let τ (x : Space) : ℝ := (hτ_ex x).choose
  have hτ_mem (x : Space) : τ x ∈ Icc (x 0) (x 0 + T) := (hτ_ex x).choose_spec.1
  have hτ_eq (x : Space) : u (mk3 (τ x) (proj2 x)) = v x := (hτ_ex x).choose_spec.2
  have hτ_cont : Continuous τ := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hlt : u (mk3 (τ x - ε) (proj2 x)) < v x := by
      rw [← hτ_eq x]; exact hline_mono (proj2 x) (by linarith)
    have hgt : v x < u (mk3 (τ x + ε) (proj2 x)) := by
      rw [← hτ_eq x]; exact hline_mono (proj2 x) (by linarith)
    have hmk_cont (c : ℝ) : Continuous (fun z : Space => u (mk3 c (proj2 z))) :=
      hu.regular.continuous.comp (continuous_mk3.comp (continuous_const.prodMk continuous_proj2))
    have hev1 : ∀ᶠ z in 𝓝 x, u (mk3 (τ x - ε) (proj2 z)) < v z :=
      (hmk_cont (τ x - ε)).continuousAt.eventually_lt hv_c1.continuous.continuousAt hlt
    have hev2 : ∀ᶠ z in 𝓝 x, v z < u (mk3 (τ x + ε) (proj2 z)) :=
      hv_c1.continuous.continuousAt.eventually_lt (hmk_cont (τ x + ε)).continuousAt hgt
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
    refine ⟨δ, hδ, fun z hz => ?_⟩
    obtain ⟨h1, h2⟩ := hball hz
    rw [← hτ_eq z] at h1 h2
    have hlo : τ x - ε < τ z := (hline_mono (proj2 z)).lt_iff_lt.mp h1
    have hhi : τ z < τ x + ε := (hline_mono (proj2 z)).lt_iff_lt.mp h2
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith, by linarith⟩
  refine ⟨τ, hτ_mem, hτ_eq, hτ_cont, fun j x => ?_⟩
  let p : Space := mk3 (τ x) (proj2 x)
  let dτ : ℝ := if j = 0 then pd3 v 0 x / pd3 u 0 p else (pd3 v j x - pd3 u j p) / pd3 u 0 p
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hmvt (s : ℝ) : ∃ c ∈ uIcc (τ x) (τ (x + s • e3 j)),
      v (x + s • e3 j) - u (mk3 (τ x) (proj2 (x + s • e3 j))) =
      (τ (x + s • e3 j) - τ x) * pd3 u 0 (mk3 c (proj2 (x + s • e3 j))) := by
    let g (r : ℝ) : ℝ := u (mk3 r (proj2 (x + s • e3 j)))
    have hgd (r : ℝ) : HasDerivAt g (pd3 u 0 (mk3 r (proj2 (x + s • e3 j)))) r := by
      have h := line_deriv3 (hu.regular.of_le (by norm_num)) (mk3 0 (proj2 (x + s • e3 j))) (e3 0) r
      have heq : (fun q : ℝ => u (mk3 0 (proj2 (x + s • e3 j)) + q • e3 0)) = g := by
        ext q; dsimp [g]; rw [mk3_add_e0, zero_add]
      rw [heq, mk3_add_e0, zero_add] at h
      exact h
    rw [← hτ_eq (x + s • e3 j)]
    by_cases heq : τ (x + s • e3 j) = τ x
    · exact ⟨τ x, left_mem_uIcc, by simp [heq]⟩
    · have hgc : Continuous g := continuous_iff_continuousAt.mpr fun r => (hgd r).continuousAt
      rcases lt_or_gt_of_ne heq with hlt | hgt
      · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
          (fun r => pd3 u 0 (mk3 r (proj2 (x + s • e3 j)))) hlt hgc.continuousOn (fun r _ => hgd r)
        refine ⟨c, by rw [uIcc_of_ge hlt.le]; exact Ioo_subset_Icc_self hc, ?_⟩
        have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hlt))).mp hslope
        dsimp [g] at this; linarith
      · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g
          (fun r => pd3 u 0 (mk3 r (proj2 (x + s • e3 j)))) hgt hgc.continuousOn (fun r _ => hgd r)
        refine ⟨c, by rw [uIcc_of_le hgt.le]; exact Ioo_subset_Icc_self hc, ?_⟩
        have := (eq_div_iff (sub_ne_zero.mpr (ne_of_gt hgt))).mp hslope
        dsimp [g] at this; linarith
  let c_of (s : ℝ) : ℝ := (hmvt s).choose
  have hc_mem (s : ℝ) : c_of s ∈ uIcc (τ x) (τ (x + s • e3 j)) := (hmvt s).choose_spec.1
  have hc_eq (s : ℝ) : v (x + s • e3 j) - u (mk3 (τ x) (proj2 (x + s • e3 j))) =
      (τ (x + s • e3 j) - τ x) * pd3 u 0 (mk3 (c_of s) (proj2 (x + s • e3 j))) :=
    (hmvt s).choose_spec.2
  have hlin_lim : Tendsto (fun s : ℝ => x + s • e3 j) (𝓝[≠] (0 : ℝ)) (𝓝 x) := by
    have hc : Continuous (fun s : ℝ => x + s • e3 j) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hτ_lim : Tendsto (fun s : ℝ => τ (x + s • e3 j)) (𝓝[≠] (0 : ℝ)) (𝓝 (τ x)) :=
    (hτ_cont.tendsto x).comp hlin_lim
  have hc_lim : Tendsto c_of (𝓝[≠] (0 : ℝ)) (𝓝 (τ x)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hball⟩ := Metric.tendsto_nhdsWithin_nhds.mp hτ_lim ε hε
    refine ⟨δ, hδ, fun s hs_ne hs_lt => ?_⟩
    have hτ_close := hball hs_ne hs_lt
    rw [Real.dist_eq] at hτ_close ⊢
    have hcm := hc_mem s
    rw [Set.mem_uIcc] at hcm
    rcases hcm with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_lt] at hτ_close ⊢; exact ⟨by linarith, by linarith⟩
    · rw [abs_lt] at hτ_close ⊢; exact ⟨by linarith, by linarith⟩
  have hden_lim : Tendsto (fun s : ℝ => pd3 u 0 (mk3 (c_of s) (proj2 (x + s • e3 j))))
      (𝓝[≠] (0 : ℝ)) (𝓝 (pd3 u 0 p)) := by
    have hpd0_cont : Continuous (pd3 u 0) :=
      ((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hmk_lim : Tendsto (fun s : ℝ => mk3 (c_of s) (proj2 (x + s • e3 j)))
        (𝓝[≠] (0 : ℝ)) (𝓝 p) :=
      (continuous_mk3.tendsto (τ x, proj2 x)).comp
        (hc_lim.prodMk_nhds ((continuous_proj2.tendsto x).comp hlin_lim))
    exact (hpd0_cont.tendsto p).comp hmk_lim
  have hv_slope : Tendsto (fun s : ℝ => s⁻¹ * (v (x + s • e3 j) - v x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (pd3 v j x)) := by
    have h := hasDerivAt_iff_tendsto_slope_zero.mp (line_deriv3 hv_c1 x (e3 j) 0)
    simpa [pd3, smul_eq_mul] using h
  have hu_slope : Tendsto (fun s : ℝ => s⁻¹ * (u (mk3 (τ x) (proj2 (x + s • e3 j))) - v x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (if j = 0 then 0 else pd3 u j p)) := by
    rw [← hτ_eq x]
    fin_cases j
    · simp only [Fin.zero_eta, ↓reduceIte]
      have hconst : (fun s : ℝ => s⁻¹ * (u (mk3 (τ x) (proj2 (x + s • e3 0))) -
          u (mk3 (τ x) (proj2 x)))) = fun _ => 0 := by
        ext s
        have hp : proj2 (x + s • e3 0) = proj2 x := by ext k; fin_cases k <;> simp [proj2, e3]
        rw [hp, sub_self, mul_zero]
      rw [hconst]; exact tendsto_const_nhds
    · simp only [Fin.mk_one, Fin.reduceEq, ↓reduceIte]
      have heq (s : ℝ) : u (mk3 (τ x) (proj2 (x + s • e3 1))) = u (p + s • e3 1) := by
        congr 1; ext k; fin_cases k <;> simp [mk3, proj2, p, e3]
      simp_rw [heq]
      have h := hasDerivAt_iff_tendsto_slope_zero.mp
        (line_deriv3 (hu.regular.of_le (by norm_num)) p (e3 1) 0)
      simpa [pd3, smul_eq_mul, p] using h
    · simp only [Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte]
      have heq (s : ℝ) : u (mk3 (τ x) (proj2 (x + s • e3 2))) = u (p + s • e3 2) := by
        congr 1; ext k; fin_cases k <;> simp [mk3, proj2, p, e3]
      simp_rw [heq]
      have h := hasDerivAt_iff_tendsto_slope_zero.mp
        (line_deriv3 (hu.regular.of_le (by norm_num)) p (e3 2) 0)
      simpa [pd3, smul_eq_mul, p] using h
  have hquot : Tendsto (fun s : ℝ =>
      (s⁻¹ * (v (x + s • e3 j) - v x) - s⁻¹ * (u (mk3 (τ x) (proj2 (x + s • e3 j))) - v x)) /
        pd3 u 0 (mk3 (c_of s) (proj2 (x + s • e3 j))))
      (𝓝[≠] (0 : ℝ)) (𝓝 dτ) := by
    have h := (hv_slope.sub hu_slope).div hden_lim (hpos p).ne'
    have hlim : (pd3 v j x - if j = 0 then 0 else pd3 u j p) / pd3 u 0 p = dτ := by
      dsimp [dτ]; split_ifs with h0
      · subst h0; simp
      · rfl
    rwa [hlim] at h
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s _
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  have hne : pd3 u 0 (mk3 (c_of s) (proj2 (x + s • e3 j))) ≠ 0 := (hpos _).ne'
  have hnum : s⁻¹ * (v (x + s • e3 j) - v x) -
      s⁻¹ * (u (mk3 (τ x) (proj2 (x + s • e3 j))) - v x) =
      s⁻¹ * (v (x + s • e3 j) - u (mk3 (τ x) (proj2 (x + s • e3 j)))) := by ring
  rw [hnum, hc_eq s]
  field_simp [hne]

private theorem continuous_param_interval_integral {τ : Space → ℝ} (hτ_cont : Continuous τ)
    (F : ℝ → Space → ℝ) (hFc : Continuous (Function.uncurry F)) :
    Continuous (fun x : Space => ∫ s in x 0..τ x, F s x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [Metric.continuousAt_iff]
  intro ε hε
  let K : Set (ℝ × Space) :=
    Icc (min (x 0) (τ x) - 1) (max (x 0) (τ x) + 1) ×ˢ closedBall x 1
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall x 1)
  obtain ⟨MF, hMF⟩ := hK.exists_bound_of_continuousOn hFc.continuousOn
  have hMF0 : 0 ≤ MF := (norm_nonneg _).trans (hMF (x 0, x)
    ⟨⟨by linarith [min_le_left (x 0) (τ x)], by linarith [le_max_left (x 0) (τ x)]⟩,
      mem_closedBall_self zero_le_one⟩)
  have hF_unif : ∃ δ1 > 0, ∀ z ∈ closedBall x δ1, ∀ s ∈ uIcc (x 0) (τ x),
      |F s z - F s x| ≤ ε / (3 * (|τ x - x 0| + 1)) := by
    have huc := (isCompact_uIcc (a := x 0) (b := τ x) |>.prod (isCompact_closedBall x 1)).uniformContinuousOn_of_continuous
      hFc.continuousOn
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨δ, hδ, huc'⟩ := huc (ε / (3 * (|τ x - x 0| + 1))) (by positivity)
    refine ⟨min 1 (δ / 2), lt_min one_pos (half_pos hδ), fun z hz s hs => ?_⟩
    have hz1 : z ∈ closedBall x 1 := closedBall_subset_closedBall (min_le_left _ _) hz
    have hdist : dist (s, z) (s, x) < δ := by
      rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
      exact lt_of_le_of_lt (mem_closedBall.mp hz) (lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ))
    have hres := huc' (s, z) ⟨hs, hz1⟩ (s, x) ⟨hs, mem_closedBall_self zero_le_one⟩ hdist
    simpa [Real.dist_eq] using hres.le
  obtain ⟨δ1, hδ1, hF_close⟩ := hF_unif
  let η : ℝ := min 1 (ε / (3 * (MF + 1)))
  have hη : 0 < η := lt_min one_pos (by positivity)
  obtain ⟨δ2, hδ2, hτ_close⟩ := Metric.continuousAt_iff.mp hτ_cont.continuousAt η hη
  refine ⟨min (min δ1 δ2) (min 1 η), lt_min (lt_min hδ1 hδ2) (lt_min one_pos hη), fun z hz => ?_⟩
  have hz_d1 : z ∈ closedBall x δ1 :=
    mem_closedBall.mpr (le_trans (le_trans (le_of_lt hz) (min_le_left _ _)) (min_le_left _ _))
  have hz_1 : z ∈ closedBall x 1 :=
    mem_closedBall.mpr (le_trans (le_trans (le_of_lt hz) (min_le_right _ _)) (min_le_left _ _))
  have hz_x0 : |z 0 - x 0| < η := by
    have hc : |z 0 - x 0| ≤ dist z x := by
      rw [dist_eq_norm]; simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (z - x) 0
    exact lt_of_le_of_lt hc (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hz_τ : |τ z - τ x| < η := by
    have := hτ_close (lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _)))
    rwa [Real.dist_eq] at this
  have hF_int (a b : ℝ) (y : Space) : IntervalIntegrable (fun s => F s y) volume a b :=
    (hFc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  have hsplit : (∫ s in z 0..τ z, F s z) - (∫ s in x 0..τ x, F s x) =
      (∫ s in z 0..x 0, F s z) + (∫ s in x 0..τ x, (F s z - F s x)) + (∫ s in τ x..τ z, F s z) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hF_int (z 0) (x 0) z) (hF_int (x 0) (τ x) z)
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hF_int (z 0) (τ x) z) (hF_int (τ x) (τ z) z)
    have h3 := intervalIntegral.integral_sub (hF_int (x 0) (τ x) z) (hF_int (x 0) (τ x) x)
    linarith
  have hI1 : |∫ s in z 0..x 0, F s z| ≤ MF * |x 0 - z 0| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hmem := Set.uIoc_subset_uIcc hs
    rw [Set.mem_uIcc] at hmem
    have hsK : (s, z) ∈ K := by
      refine ⟨⟨?_, ?_⟩, hz_1⟩
      · have hlt1 : |z 0 - x 0| < 1 := lt_of_lt_of_le hz_x0 (min_le_left _ _)
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [(abs_lt.mp hlt1).1, min_le_left (x 0) (τ x)]
      · have hlt1 : |z 0 - x 0| < 1 := lt_of_lt_of_le hz_x0 (min_le_left _ _)
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [(abs_lt.mp hlt1).2, le_max_left (x 0) (τ x)]
    exact hMF (s, z) hsK
  have hI3 : |∫ s in τ x..τ z, F s z| ≤ MF * |τ z - τ x| := by
    rw [← Real.norm_eq_abs]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro s hs
    have hmem := Set.uIoc_subset_uIcc hs
    rw [Set.mem_uIcc] at hmem
    have hsK : (s, z) ∈ K := by
      refine ⟨⟨?_, ?_⟩, hz_1⟩
      · have hlt1 : |τ z - τ x| < 1 := lt_of_lt_of_le hz_τ (min_le_left _ _)
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [(abs_lt.mp hlt1).1, min_le_right (x 0) (τ x)]
      · have hlt1 : |τ z - τ x| < 1 := lt_of_lt_of_le hz_τ (min_le_left _ _)
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith [(abs_lt.mp hlt1).2, le_max_right (x 0) (τ x)]
    exact hMF (s, z) hsK
  have hI2 : |∫ s in x 0..τ x, (F s z - F s x)| ≤ ε / 3 := by
    rw [← Real.norm_eq_abs]
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x 0) (b := τ x) (f := fun s => F s z - F s x) (C := ε / (3 * (|τ x - x 0| + 1)))
      (fun s hs => by rw [Real.norm_eq_abs]; exact hF_close z hz_d1 s (Set.uIoc_subset_uIcc hs))
    calc _ ≤ ε / (3 * (|τ x - x 0| + 1)) * |τ x - x 0| := hle
      _ ≤ ε / (3 * (|τ x - x 0| + 1)) * (|τ x - x 0| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε / 3 := by field_simp
  have hMFη : MF * η < ε / 3 := by
    have hle : η ≤ ε / (3 * (MF + 1)) := min_le_right _ _
    have h1 : MF / (MF + 1) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    have h2 : MF * (ε / (3 * (MF + 1))) = (ε / 3) * (MF / (MF + 1)) := by field_simp
    calc MF * η ≤ MF * (ε / (3 * (MF + 1))) := mul_le_mul_of_nonneg_left hle hMF0
      _ = (ε / 3) * (MF / (MF + 1)) := h2
      _ < ε / 3 := by nlinarith
  rw [Real.dist_eq, hsplit]
  have ha1 := abs_add_le ((∫ s in z 0..x 0, F s z) + ∫ s in x 0..τ x, (F s z - F s x))
    (∫ s in τ x..τ z, F s z)
  have ha2 := abs_add_le (∫ s in z 0..x 0, F s z) (∫ s in x 0..τ x, (F s z - F s x))
  rw [abs_sub_comm (x 0) (z 0)] at hI1
  have hI1' : |∫ s in z 0..x 0, F s z| ≤ MF * η := hI1.trans (mul_le_mul_of_nonneg_left hz_x0.le hMF0)
  have hI3' : |∫ s in τ x..τ z, F s z| ≤ MF * η := hI3.trans (mul_le_mul_of_nonneg_left hz_τ.le hMF0)
  linarith

private theorem calibration_step_T {u : Space → ℝ} (hu : IsBoundedSol u)
    (hpos : ∀ x, 0 < pd3 u 0 x)
    {C1 : ℝ} (hu1 : ∀ x, |u x| ≤ 1) (hpd1 : ∀ x i, |pd3 u i x| ≤ C1)
    {R T : ℝ} (hR : 2 ≤ R) (hT : 0 < T) :
    (∫ x in Q3 R, e3_en u x) ≤
      (∫ x in Q3 (R - 1), e3_en u (x + T • e3 0)) +
        24 * ((3 / 2) * (C1 + 6) ^ 2 + 1 / 4) * R ^ 2 := by
  let M0 : ℝ := (3 / 2) * (C1 + 6) ^ 2 + 1 / 4
  have hM0_nn : 0 ≤ M0 := by dsimp [M0]; positivity
  let η (x : Space) : ℝ := cut3D R x
  let v (x : Space) : ℝ := (1 - η x) * u x + η x * u (x + T • e3 0)
  have hv_c1 : ContDiff ℝ 1 v :=
    ((contDiff_const.sub (contDiff_cut3D R)).mul (hu.regular.of_le (by norm_num))).add
      ((contDiff_cut3D R).mul ((hu.regular.of_le (by norm_num)).comp (contDiff_id.add contDiff_const)))
  have hline_mono (y : Plane2) : StrictMono (fun s : ℝ => u (mk3 s y)) := by
    apply strictMono_of_deriv_pos
    intro s
    have h := line_deriv3 (hu.regular.of_le (by norm_num)) (mk3 0 y) (e3 0) s
    have heq : (fun r : ℝ => u (mk3 0 y + r • e3 0)) = fun r => u (mk3 r y) := by
      ext r; rw [mk3_add_e0, zero_add]
    rw [heq, mk3_add_e0, zero_add] at h
    rw [h.deriv]
    exact hpos _
  have hu_le_T (x : Space) : u x ≤ u (x + T • e3 0) := by
    conv_lhs => rw [← mk3_proj2 x]
    conv_rhs => rw [← mk3_proj2 x, mk3_add_e0]
    exact (hline_mono (proj2 x)).monotone (by linarith)
  have hv_lo (x : Space) : u x ≤ v x := by
    have hηb := cut3D_bounds R x
    have := hu_le_T x
    dsimp [v, η]; nlinarith [hηb.1, hηb.2]
  have hv_hi (x : Space) : v x ≤ u (x + T • e3 0) := by
    have hηb := cut3D_bounds R x
    have := hu_le_T x
    dsimp [v, η]; nlinarith [hηb.1, hηb.2]
  obtain ⟨τ, _, hτ_eq, hτ_cont, hτ_deriv⟩ :=
    implicit_tau_props hu hpos hv_c1 hT hv_lo hv_hi
  have hτ_zero_of_η (x : Space) (hη0 : η x = 0) : τ x = x 0 := by
    apply (hline_mono (proj2 x)).injective
    dsimp only
    rw [hτ_eq x, mk3_proj2]
    simp [v, hη0]
  let p (x : Space) : Space := mk3 (τ x) (proj2 x)
  let Ψ (j : Fin 3) (x : Space) : ℝ :=
    -∫ s in x 0..τ x, pd3 u j (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x))
  let dΨ0 (x : Space) : ℝ := (pd3 u 0 x) ^ 2 - pd3 u 0 (p x) * pd3 v 0 x
  let dΨ1 (x : Space) : ℝ :=
    -pd3 u 1 (p x) * pd3 v 1 x + (pd3 u 1 (p x)) ^ 2 -
      ∫ s in x 0..τ x, (pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x)))
  let dΨ2 (x : Space) : ℝ :=
    -pd3 u 2 (p x) * pd3 v 2 x + (pd3 u 2 (p x)) ^ 2 -
      ∫ s in x 0..τ x, (pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x)))
  have hpd1_cont (k : Fin 3) : Continuous (pd3 u k) :=
    ((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpd2_cont (k l : Fin 3) : Continuous (pd32 u k l) :=
    (((hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hv1_cont (k : Fin 3) : Continuous (pd3 v k) :=
    (hv_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hp_cont : Continuous p := continuous_mk3.comp (hτ_cont.prodMk continuous_proj2)
  have hΨ0_deriv (x : Space) : HasDerivAt (fun r : ℝ => Ψ 0 (x + r • e3 0)) (dΨ0 x) 0 := by
    let f (s : ℝ) : ℝ := pd3 u 0 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x))
    have hf_cont : Continuous f := by
      have hmk : Continuous (fun s : ℝ => mk3 s (proj2 x)) :=
        continuous_mk3.comp (continuous_id.prodMk continuous_const)
      exact ((hpd1_cont 0).comp hmk).mul ((hpd1_cont 0).comp hmk)
    have heq : (fun r : ℝ => Ψ 0 (x + r • e3 0)) =
        fun r => -((∫ s in (0 : ℝ)..τ (x + r • e3 0), f s) - ∫ s in (0 : ℝ)..(x 0 + r), f s) := by
      ext r
      have hp : proj2 (x + r • e3 0) = proj2 x := by ext k; fin_cases k <;> simp [proj2, e3]
      have hx0 : (x + r • e3 0) 0 = x 0 + r := by simp [e3]
      change -(∫ s in (x + r • e3 0) 0..τ (x + r • e3 0),
          pd3 u 0 (mk3 s (proj2 (x + r • e3 0))) * pd3 u 0 (mk3 s (proj2 (x + r • e3 0)))) = _
      rw [hp, hx0]
      congr 1
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hf_cont.intervalIntegrable (μ := volume) 0 (x 0 + r))
        (hf_cont.intervalIntegrable (μ := volume) (x 0 + r) (τ (x + r • e3 0)))
      dsimp [f]; linarith
    rw [heq]
    have hA : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..τ (x + r • e3 0), f s)
        (f (τ x) * (pd3 v 0 x / pd3 u 0 (p x))) 0 := by
      have hFTC := intervalIntegral.integral_hasDerivAt_right (hf_cont.intervalIntegrable 0 (τ x))
        (hf_cont.stronglyMeasurableAtFilter volume (𝓝 (τ x))) hf_cont.continuousAt
      have hτ0 := hτ_deriv 0 x
      simp only [↓reduceIte] at hτ0
      have hτ_at : τ (x + (0 : ℝ) • e3 0) = τ x := by simp
      have hcomp := (hτ_at ▸ hFTC).comp 0 hτ0
      refine hcomp.congr_deriv ?_
      rw [hτ_at]
    have hB : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..(x 0 + r), f s) (f (x 0)) 0 := by
      have hFTC := intervalIntegral.integral_hasDerivAt_right (hf_cont.intervalIntegrable 0 (x 0))
        (hf_cont.stronglyMeasurableAtFilter volume (𝓝 (x 0))) hf_cont.continuousAt
      have hlin : HasDerivAt (fun r : ℝ => x 0 + r) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
      have hcomp := (by simpa using hFTC : HasDerivAt _ _ (x 0 + 0)).comp 0 hlin
      exact hcomp.congr_deriv (by ring)
    refine (hA.fun_sub hB).neg.congr_deriv ?_
    dsimp [f, dΨ0, p]
    have hne : pd3 u 0 (mk3 (τ x) (proj2 x)) ≠ 0 := (hpos _).ne'
    rw [mk3_proj2]
    field_simp [hne]
    ring
  have hΨ1_deriv (x : Space) : HasDerivAt (fun r : ℝ => Ψ 1 (x + r • e3 1)) (dΨ1 x) 0 := by
    let F (s r : ℝ) : ℝ :=
      pd3 u 1 (mk3 s (proj2 (x + r • e3 1))) * pd3 u 0 (mk3 s (proj2 (x + r • e3 1)))
    let F' (s r : ℝ) : ℝ :=
      pd32 u 1 1 (mk3 s (proj2 (x + r • e3 1))) * pd3 u 0 (mk3 s (proj2 (x + r • e3 1))) +
      pd3 u 1 (mk3 s (proj2 (x + r • e3 1))) * pd32 u 0 1 (mk3 s (proj2 (x + r • e3 1)))
    have hmk_cont : Continuous (fun q : ℝ × ℝ => mk3 q.1 (proj2 (x + q.2 • e3 1))) :=
      continuous_mk3.comp (continuous_fst.prodMk
        (continuous_proj2.comp (continuous_const.add (continuous_snd.smul continuous_const))))
    have hF_cont : Continuous (Function.uncurry F) :=
      ((hpd1_cont 1).comp hmk_cont).mul ((hpd1_cont 0).comp hmk_cont)
    have hF'_cont : Continuous (Function.uncurry F') :=
      (((hpd2_cont 1 1).comp hmk_cont).mul ((hpd1_cont 0).comp hmk_cont)).add
        (((hpd1_cont 1).comp hmk_cont).mul ((hpd2_cont 0 1).comp hmk_cont))
    have hF_deriv (s r : ℝ) : HasDerivAt (F s) (F' s r) r := by
      have hline (k : Fin 3) : HasDerivAt (fun q : ℝ => pd3 u k (mk3 s (proj2 (x + q • e3 1))))
          (pd32 u k 1 (mk3 s (proj2 (x + r • e3 1)))) r := by
        have h1c : ContDiff ℝ 1 (pd3 u k) :=
          (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
        have hl := line_deriv3 h1c (mk3 s (proj2 x)) (e3 1) r
        have heq : (fun q : ℝ => pd3 u k (mk3 s (proj2 x) + q • e3 1)) =
            fun q => pd3 u k (mk3 s (proj2 (x + q • e3 1))) := by
          ext q; congr 1; ext m; fin_cases m <;> simp [mk3, proj2, e3]
        rw [heq] at hl
        refine hl.congr_deriv ?_
        unfold pd32 pd3
        exact congrArg (fun z => fderiv ℝ (pd3 u k) z (e3 1)) (by ext m; fin_cases m <;> simp [mk3, proj2, e3])
      exact (hline 1).fun_mul (hline 0)
    have hleib := hasDerivAt_integral_param_upper (a := x 0) (g := fun r => τ (x + r • e3 1))
      (hτ_deriv 1 x) hF_cont hF'_cont hF_deriv
    have heq : (fun r : ℝ => -(∫ s in x 0..τ (x + r • e3 1), F s r)) =
        fun r => Ψ 1 (x + r • e3 1) := by
      ext r
      have hx0 : (x + r • e3 1) 0 = x 0 := by simp [e3]
      change -(∫ s in x 0..τ (x + r • e3 1), F s r) =
        -(∫ s in (x + r • e3 1) 0..τ (x + r • e3 1), F s r)
      rw [hx0]
    rw [← heq]
    refine hleib.neg.congr_deriv ?_
    dsimp [F, F', dΨ1, p]
    simp only [Fin.reduceEq, ↓reduceIte, zero_smul, add_zero]
    have hne : pd3 u 0 (mk3 (τ x) (proj2 x)) ≠ 0 := (hpos _).ne'
    field_simp [hne]
    ring
  have hΨ2_deriv (x : Space) : HasDerivAt (fun r : ℝ => Ψ 2 (x + r • e3 2)) (dΨ2 x) 0 := by
    let F (s r : ℝ) : ℝ :=
      pd3 u 2 (mk3 s (proj2 (x + r • e3 2))) * pd3 u 0 (mk3 s (proj2 (x + r • e3 2)))
    let F' (s r : ℝ) : ℝ :=
      pd32 u 2 2 (mk3 s (proj2 (x + r • e3 2))) * pd3 u 0 (mk3 s (proj2 (x + r • e3 2))) +
      pd3 u 2 (mk3 s (proj2 (x + r • e3 2))) * pd32 u 0 2 (mk3 s (proj2 (x + r • e3 2)))
    have hmk_cont : Continuous (fun q : ℝ × ℝ => mk3 q.1 (proj2 (x + q.2 • e3 2))) :=
      continuous_mk3.comp (continuous_fst.prodMk
        (continuous_proj2.comp (continuous_const.add (continuous_snd.smul continuous_const))))
    have hF_cont : Continuous (Function.uncurry F) :=
      ((hpd1_cont 2).comp hmk_cont).mul ((hpd1_cont 0).comp hmk_cont)
    have hF'_cont : Continuous (Function.uncurry F') :=
      (((hpd2_cont 2 2).comp hmk_cont).mul ((hpd1_cont 0).comp hmk_cont)).add
        (((hpd1_cont 2).comp hmk_cont).mul ((hpd2_cont 0 2).comp hmk_cont))
    have hF_deriv (s r : ℝ) : HasDerivAt (F s) (F' s r) r := by
      have hline (k : Fin 3) : HasDerivAt (fun q : ℝ => pd3 u k (mk3 s (proj2 (x + q • e3 2))))
          (pd32 u k 2 (mk3 s (proj2 (x + r • e3 2)))) r := by
        have h1c : ContDiff ℝ 1 (pd3 u k) :=
          (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
        have hl := line_deriv3 h1c (mk3 s (proj2 x)) (e3 2) r
        have heq : (fun q : ℝ => pd3 u k (mk3 s (proj2 x) + q • e3 2)) =
            fun q => pd3 u k (mk3 s (proj2 (x + q • e3 2))) := by
          ext q; congr 1; ext m; fin_cases m <;> simp [mk3, proj2, e3]
        rw [heq] at hl
        refine hl.congr_deriv ?_
        unfold pd32 pd3
        exact congrArg (fun z => fderiv ℝ (pd3 u k) z (e3 2)) (by ext m; fin_cases m <;> simp [mk3, proj2, e3])
      exact (hline 2).fun_mul (hline 0)
    have hleib := hasDerivAt_integral_param_upper (a := x 0) (g := fun r => τ (x + r • e3 2))
      (hτ_deriv 2 x) hF_cont hF'_cont hF_deriv
    have heq : (fun r : ℝ => -(∫ s in x 0..τ (x + r • e3 2), F s r)) =
        fun r => Ψ 2 (x + r • e3 2) := by
      ext r
      have hx0 : (x + r • e3 2) 0 = x 0 := by simp [e3]
      change -(∫ s in x 0..τ (x + r • e3 2), F s r) =
        -(∫ s in (x + r • e3 2) 0..τ (x + r • e3 2), F s r)
      rw [hx0]
    rw [← heq]
    refine hleib.neg.congr_deriv ?_
    dsimp [F, F', dΨ2, p]
    simp only [Fin.reduceEq, ↓reduceIte, zero_smul, add_zero]
    have hne : pd3 u 0 (mk3 (τ x) (proj2 x)) ≠ 0 := (hpos _).ne'
    field_simp [hne]
    ring
  have hcalib (x : Space) : e3_en u x ≤ e3_en v x + (dΨ0 x + dΨ1 x + dΨ2 x) := by
    let H (s : ℝ) : ℝ :=
      (1 / 2) * (pd3 u 0 (mk3 s (proj2 x))) ^ 2 -
      (1 / 2) * (pd3 u 1 (mk3 s (proj2 x))) ^ 2 -
      (1 / 2) * (pd3 u 2 (mk3 s (proj2 x))) ^ 2 -
      Wpot (u (mk3 s (proj2 x)))
    let H' (s : ℝ) : ℝ :=
      -(pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x)) +
        pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x)))
    have hH_deriv (s : ℝ) : HasDerivAt H (H' s) s := by
      have hpd_d (k : Fin 3) : HasDerivAt (fun r : ℝ => pd3 u k (mk3 r (proj2 x)))
          (pd32 u k 0 (mk3 s (proj2 x))) s := by
        have h1c : ContDiff ℝ 1 (pd3 u k) :=
          (hu.regular.fderiv_right (by norm_num)).clm_apply contDiff_const
        have hl := line_deriv3 h1c (mk3 0 (proj2 x)) (e3 0) s
        have heq : (fun r : ℝ => pd3 u k (mk3 0 (proj2 x) + r • e3 0)) =
            fun r => pd3 u k (mk3 r (proj2 x)) := by ext r; rw [mk3_add_e0, zero_add]
        rw [heq, mk3_add_e0, zero_add] at hl; exact hl
      have hu_d : HasDerivAt (fun r : ℝ => u (mk3 r (proj2 x)))
          (pd3 u 0 (mk3 s (proj2 x))) s := by
        have hl := line_deriv3 (hu.regular.of_le (by norm_num)) (mk3 0 (proj2 x)) (e3 0) s
        have heq : (fun r : ℝ => u (mk3 0 (proj2 x) + r • e3 0)) =
            fun r => u (mk3 r (proj2 x)) := by ext r; rw [mk3_add_e0, zero_add]
        rw [heq, mk3_add_e0, zero_add] at hl; exact hl
      have hW_d : HasDerivAt (fun r : ℝ => Wpot (u (mk3 r (proj2 x))))
          ((u (mk3 s (proj2 x)) ^ 3 - u (mk3 s (proj2 x))) * pd3 u 0 (mk3 s (proj2 x))) s := by
        have hW1 : HasDerivAt Wpot (u (mk3 s (proj2 x)) ^ 3 - u (mk3 s (proj2 x)))
            (u (mk3 s (proj2 x))) := by
          unfold Wpot
          have h1 := ((hasDerivAt_const (u (mk3 s (proj2 x))) (1 : ℝ)).fun_sub
            (hasDerivAt_pow 2 (u (mk3 s (proj2 x))))).fun_pow 2 |>.div_const 4
          refine h1.congr_deriv ?_
          norm_num; ring
        exact hW1.comp s hu_d
      have hcomb := ((((hpd_d 0).fun_pow 2).const_mul (1 / 2 : ℝ)).fun_sub
        (((hpd_d 1).fun_pow 2).const_mul (1 / 2 : ℝ))).fun_sub
        (((hpd_d 2).fun_pow 2).const_mul (1 / 2 : ℝ)) |>.fun_sub hW_d
      refine hcomb.congr_deriv ?_
      have hpde := hu.solution (mk3 s (proj2 x))
      rw [laplacian_sum3 hu.regular] at hpde
      have h00 : pd32 u 0 0 (mk3 s (proj2 x)) =
          u (mk3 s (proj2 x)) ^ 3 - u (mk3 s (proj2 x)) -
            pd32 u 1 1 (mk3 s (proj2 x)) - pd32 u 2 2 (mk3 s (proj2 x)) := by linarith
      have hsym1 := partial_comm3 hu.regular (mk3 s (proj2 x)) 1 0
      have hsym2 := partial_comm3 hu.regular (mk3 s (proj2 x)) 2 0
      dsimp [H']
      rw [h00, hsym1, hsym2]
      norm_num; ring
    have hmk : Continuous (fun s : ℝ => mk3 s (proj2 x)) :=
      continuous_mk3.comp (continuous_id.prodMk continuous_const)
    have hc1 : Continuous (fun s => pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x))) :=
      (((hpd2_cont 1 1).comp hmk).mul ((hpd1_cont 0).comp hmk)).add
        (((hpd1_cont 1).comp hmk).mul ((hpd2_cont 0 1).comp hmk))
    have hc2 : Continuous (fun s => pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
        pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x))) :=
      (((hpd2_cont 2 2).comp hmk).mul ((hpd1_cont 0).comp hmk)).add
        (((hpd1_cont 2).comp hmk).mul ((hpd2_cont 0 2).comp hmk))
    have hH'_cont : Continuous H' := (hc1.add hc2).neg.congr fun s => by dsimp [H']; ring
    have hFTC_H : (∫ s in x 0..τ x, H' s) = H (τ x) - H (x 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hH_deriv s)
        (hH'_cont.intervalIntegrable _ _)
    have hint_sum :
        -(∫ s in x 0..τ x, (pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
          pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x)))) -
        (∫ s in x 0..τ x, (pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
          pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x)))) = H (τ x) - H (x 0) := by
      have hadd := intervalIntegral.integral_add
        (hc1.intervalIntegrable (μ := volume) (x 0) (τ x))
        (hc2.intervalIntegrable (μ := volume) (x 0) (τ x))
      have hneg := intervalIntegral.integral_neg (μ := volume) (a := x 0) (b := τ x)
        (f := fun s => (pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
          pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x))) +
          (pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
          pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x))))
      have heq_H' : (∫ s in x 0..τ x, H' s) =
          -(∫ s in x 0..τ x, ((pd32 u 1 1 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
            pd3 u 1 (mk3 s (proj2 x)) * pd32 u 0 1 (mk3 s (proj2 x))) +
            (pd32 u 2 2 (mk3 s (proj2 x)) * pd3 u 0 (mk3 s (proj2 x)) +
            pd3 u 2 (mk3 s (proj2 x)) * pd32 u 0 2 (mk3 s (proj2 x))))) := by
        rw [← hneg]
        apply intervalIntegral.integral_congr
        intro s _; dsimp [H']; ring
      linarith [hFTC_H, heq_H', hadd]
    have hW_eq : Wpot (u (p x)) = Wpot (v x) := congrArg Wpot (hτ_eq x)
    have hsq_sum : e3_en v x - e3_en u x + (dΨ0 x + dΨ1 x + dΨ2 x) =
        (1 / 2) * ((pd3 v 0 x - pd3 u 0 (p x)) ^ 2 +
          (pd3 v 1 x - pd3 u 1 (p x)) ^ 2 + (pd3 v 2 x - pd3 u 2 (p x)) ^ 2) := by
      dsimp [e3_en, dΨ0, dΨ1, dΨ2]
      simp only [Fin.sum_univ_three]
      dsimp [H, p] at hint_sum hW_eq ⊢
      rw [mk3_proj2] at hint_sum
      linarith
    nlinarith [sq_nonneg (pd3 v 0 x - pd3 u 0 (p x)),
      sq_nonneg (pd3 v 1 x - pd3 u 1 (p x)),
      sq_nonneg (pd3 v 2 x - pd3 u 2 (p x))]
  have hdΨ0_cont : Continuous dΨ0 :=
    ((hpd1_cont 0).pow 2).sub (((hpd1_cont 0).comp hp_cont).mul (hv1_cont 0))
  have hmk_pair : Continuous (fun q : ℝ × Space => mk3 q.1 (proj2 q.2)) :=
    continuous_mk3.comp (continuous_fst.prodMk (continuous_proj2.comp continuous_snd))
  have hdΨ1_cont : Continuous dΨ1 := by
    have hFc : Continuous (fun q : ℝ × Space =>
        pd32 u 1 1 (mk3 q.1 (proj2 q.2)) * pd3 u 0 (mk3 q.1 (proj2 q.2)) +
        pd3 u 1 (mk3 q.1 (proj2 q.2)) * pd32 u 0 1 (mk3 q.1 (proj2 q.2))) :=
      (((hpd2_cont 1 1).comp hmk_pair).mul ((hpd1_cont 0).comp hmk_pair)).add
        (((hpd1_cont 1).comp hmk_pair).mul ((hpd2_cont 0 1).comp hmk_pair))
    exact ((((hpd1_cont 1).comp hp_cont).neg.mul (hv1_cont 1)).add
      (((hpd1_cont 1).comp hp_cont).pow 2)).sub (continuous_param_interval_integral hτ_cont _ hFc)
  have hdΨ2_cont : Continuous dΨ2 := by
    have hFc : Continuous (fun q : ℝ × Space =>
        pd32 u 2 2 (mk3 q.1 (proj2 q.2)) * pd3 u 0 (mk3 q.1 (proj2 q.2)) +
        pd3 u 2 (mk3 q.1 (proj2 q.2)) * pd32 u 0 2 (mk3 q.1 (proj2 q.2))) :=
      (((hpd2_cont 2 2).comp hmk_pair).mul ((hpd1_cont 0).comp hmk_pair)).add
        (((hpd1_cont 2).comp hmk_pair).mul ((hpd2_cont 0 2).comp hmk_pair))
    exact ((((hpd1_cont 2).comp hp_cont).neg.mul (hv1_cont 2)).add
      (((hpd1_cont 2).comp hp_cont).pow 2)).sub (continuous_param_interval_integral hτ_cont _ hFc)
  have hΨ_bdy (j : Fin 3) (x : Space) (hx : |x j| = R) : Ψ j x = 0 := by
    have hη0 : η x = 0 := cut3D_zero_of_coord (le_of_eq hx.symm)
    have hτ0 : τ x = x 0 := hτ_zero_of_η x hη0
    dsimp [Ψ]; rw [hτ0, intervalIntegral.integral_same, neg_zero]
  have hdiv0 : (∫ x in Q3 R, dΨ0 x) = 0 :=
    setIntegral_Q3_deriv_eq_zero (by linarith) 0 hdΨ0_cont hΨ0_deriv (hΨ_bdy 0)
  have hdiv1 : (∫ x in Q3 R, dΨ1 x) = 0 :=
    setIntegral_Q3_deriv_eq_zero (by linarith) 1 hdΨ1_cont hΨ1_deriv (hΨ_bdy 1)
  have hdiv2 : (∫ x in Q3 R, dΨ2 x) = 0 :=
    setIntegral_Q3_deriv_eq_zero (by linarith) 2 hdΨ2_cont hΨ2_deriv (hΨ_bdy 2)
  have heu_cont : Continuous (e3_en u) := by
    unfold e3_en Wpot
    exact (continuous_const.mul (continuous_finset_sum _ fun k _ => (hpd1_cont k).pow 2)).add
      (((continuous_const.sub (hu.regular.continuous.pow 2)).pow 2).div_const 4)
  have hev_cont : Continuous (e3_en v) := by
    unfold e3_en Wpot
    exact (continuous_const.mul (continuous_finset_sum _ fun k _ => (hv1_cont k).pow 2)).add
      (((continuous_const.sub (hv_c1.continuous.pow 2)).pow 2).div_const 4)
  have hInt_eu : IntegrableOn (e3_en u) (Q3 R) volume :=
    heu_cont.continuousOn.integrableOn_compact (isCompact_Q3_c R)
  have hInt_ev : IntegrableOn (e3_en v) (Q3 R) volume :=
    hev_cont.continuousOn.integrableOn_compact (isCompact_Q3_c R)
  have hInt_d0 : IntegrableOn dΨ0 (Q3 R) volume :=
    hdΨ0_cont.continuousOn.integrableOn_compact (isCompact_Q3_c R)
  have hInt_d1 : IntegrableOn dΨ1 (Q3 R) volume :=
    hdΨ1_cont.continuousOn.integrableOn_compact (isCompact_Q3_c R)
  have hInt_d2 : IntegrableOn dΨ2 (Q3 R) volume :=
    hdΨ2_cont.continuousOn.integrableOn_compact (isCompact_Q3_c R)
  have hle_ev : (∫ x in Q3 R, e3_en u x) ≤ ∫ x in Q3 R, e3_en v x := by
    have hmono := setIntegral_mono_on hInt_eu
      (hInt_ev.add ((hInt_d0.add hInt_d1).add hInt_d2)) (measurableSet_Q3 R)
      (fun x _ => hcalib x)
    simp only [Pi.add_apply] at hmono
    have hadd1 : (∫ x in Q3 R, e3_en v x + (dΨ0 x + dΨ1 x + dΨ2 x)) =
        (∫ x in Q3 R, e3_en v x) + ∫ x in Q3 R, (dΨ0 x + dΨ1 x + dΨ2 x) :=
      integral_add hInt_ev ((hInt_d0.add hInt_d1).add hInt_d2)
    have hadd2 : (∫ x in Q3 R, (dΨ0 x + dΨ1 x + dΨ2 x)) =
        (∫ x in Q3 R, (dΨ0 x + dΨ1 x)) + ∫ x in Q3 R, dΨ2 x :=
      integral_add (hInt_d0.add hInt_d1) hInt_d2
    have hadd3 : (∫ x in Q3 R, (dΨ0 x + dΨ1 x)) =
        (∫ x in Q3 R, dΨ0 x) + ∫ x in Q3 R, dΨ1 x :=
      integral_add hInt_d0 hInt_d1
    linarith [hmono, hadd1, hadd2, hadd3, hdiv0, hdiv1, hdiv2]
  have hsub_Q : Q3 (R - 1) ⊆ Q3 R := fun x hx i =>
    ⟨by linarith [(hx i).1], by linarith [(hx i).2]⟩
  have hsplit_ev : (∫ x in Q3 R, e3_en v x) =
      (∫ x in Q3 (R - 1), e3_en v x) + ∫ x in Q3 R \ Q3 (R - 1), e3_en v x := by
    have hunion : Q3 (R - 1) ∪ (Q3 R \ Q3 (R - 1)) = Q3 R := union_sdiff_cancel hsub_Q
    conv_lhs => rw [← hunion]
    exact setIntegral_union disjoint_sdiff_self_right
      ((measurableSet_Q3 R).diff (measurableSet_Q3 (R - 1)))
      (hInt_ev.mono_set hsub_Q) (hInt_ev.mono_set sdiff_subset)
  have hv_pd (i : Fin 3) (x : Space) :
      pd3 v i x = (1 - η x) * pd3 u i x + η x * pd3 u i (x + T • e3 0) +
        pd3 η i x * (u (x + T • e3 0) - u x) := by
    have h1 := line_deriv3 hv_c1 x (e3 i) 0
    have hηd := line_deriv3 (contDiff_cut3D R) x (e3 i) 0
    have hud := line_deriv3 (hu.regular.of_le (by norm_num)) x (e3 i) 0
    have huTd : HasDerivAt (fun s : ℝ => u (x + s • e3 i + T • e3 0))
        (pd3 u i (x + T • e3 0)) 0 := by
      have hl := line_deriv3 (hu.regular.of_le (by norm_num)) (x + T • e3 0) (e3 i) 0
      have heq : (fun s : ℝ => u (x + T • e3 0 + s • e3 i)) =
          fun s => u (x + s • e3 i + T • e3 0) := by ext s; congr 1; module
      rw [heq] at hl; simpa [pd3] using hl
    have h2 := (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub hηd).fun_mul hud).fun_add
      (hηd.fun_mul huTd)
    have huq := h1.unique h2
    simp only [zero_smul, add_zero] at huq
    change pd3 v i x = _ at huq
    rw [huq]; unfold pd3; ring
  have hev_inner : (∫ x in Q3 (R - 1), e3_en v x) =
      ∫ x in Q3 (R - 1), e3_en u (x + T • e3 0) := by
    apply setIntegral_congr_fun (measurableSet_Q3 (R - 1))
    intro x hx
    have hη1 : η x = 1 := cut3D_one hx
    have hηd0 (i : Fin 3) : pd3 η i x = 0 := pd3_cut3D_zero_of_mem hx i
    have hv_eq : v x = u (x + T • e3 0) := by dsimp [v]; rw [hη1]; ring
    have hv_pd_eq (i : Fin 3) : pd3 v i x = pd3 u i (x + T • e3 0) := by
      rw [hv_pd i x, hη1, hηd0 i]; ring
    unfold e3_en
    rw [hv_eq]
    congr 2
    apply Finset.sum_congr rfl
    intro i _; rw [hv_pd_eq i]
  have hev_le_M0 (x : Space) : e3_en v x ≤ M0 := by
    have hηb := cut3D_bounds R x
    have hv1 : |v x| ≤ 1 := by
      have h1 := abs_le.mp (hu1 x)
      have h2 := abs_le.mp (hu1 (x + T • e3 0))
      rw [abs_le]; dsimp [v]
      exact ⟨by nlinarith [hηb.1, hηb.2], by nlinarith [hηb.1, hηb.2]⟩
    have hW : Wpot (v x) ≤ 1 / 4 := by
      unfold Wpot
      have hsq : v x ^ 2 ≤ 1 := by rw [← sq_abs (v x)]; nlinarith [abs_nonneg (v x)]
      have h0 : 0 ≤ 1 - v x ^ 2 := by linarith
      have h1 : 1 - v x ^ 2 ≤ 1 := by linarith [sq_nonneg (v x)]
      nlinarith
    have hpd_le (i : Fin 3) : |pd3 v i x| ≤ C1 + 6 := by
      rw [hv_pd i x]
      have ha : |(1 - η x) * pd3 u i x + η x * pd3 u i (x + T • e3 0)| ≤ C1 := by
        have h1 := abs_le.mp (hpd1 x i)
        have h2 := abs_le.mp (hpd1 (x + T • e3 0) i)
        rw [abs_le]; exact ⟨by nlinarith [hηb.1, hηb.2], by nlinarith [hηb.1, hηb.2]⟩
      have hb : |pd3 η i x * (u (x + T • e3 0) - u x)| ≤ 6 := by
        rw [abs_mul]
        have h1 : |pd3 η i x| ≤ 3 := pd3_cut3D_abs_le R i x
        have h2 : |u (x + T • e3 0) - u x| ≤ 2 :=
          (abs_sub _ _).trans (by linarith [hu1 (x + T • e3 0), hu1 x])
        nlinarith [abs_nonneg (pd3 η i x), abs_nonneg (u (x + T • e3 0) - u x)]
      exact (abs_add_le _ _).trans (by linarith)
    have hsq_le (i : Fin 3) : (pd3 v i x) ^ 2 ≤ (C1 + 6) ^ 2 := by
      rw [← sq_abs (pd3 v i x)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hpd_le i) 2
    unfold e3_en
    rw [Fin.sum_univ_three]
    dsimp [M0]
    linarith [hsq_le 0, hsq_le 1, hsq_le 2, hW]
  have hvol_shell : (volume (Q3 R \ Q3 (R - 1))).toReal ≤ 24 * R ^ 2 := by
    have hR1 : 0 ≤ R - 1 := by linarith
    have hfin : volume (Q3 (R - 1)) ≠ ⊤ := by
      rw [volume_Q3 hR1]; exact ENNReal.ofReal_ne_top
    rw [measure_diff hsub_Q (measurableSet_Q3 (R - 1)).nullMeasurableSet hfin,
      volume_Q3 (by linarith), volume_Q3 hR1,
      ← ENNReal.ofReal_sub _ (by positivity),
      ENNReal.toReal_ofReal (by nlinarith)]
    nlinarith
  have hev_outer : (∫ x in Q3 R \ Q3 (R - 1), e3_en v x) ≤ 24 * M0 * R ^ 2 := by
    have hfin_shell : volume (Q3 R \ Q3 (R - 1)) < ⊤ :=
      (measure_mono sdiff_subset).trans_lt (by rw [volume_Q3 (by linarith)]; exact ENNReal.ofReal_lt_top)
    have hmono := setIntegral_mono_on (hInt_ev.mono_set sdiff_subset)
      (integrableOn_const (C := M0) (hs := hfin_shell.ne))
      ((measurableSet_Q3 R).diff (measurableSet_Q3 (R - 1))) (fun x _ => hev_le_M0 x)
    rw [setIntegral_const, smul_eq_mul] at hmono
    calc _ ≤ volume.real (Q3 R \ Q3 (R - 1)) * M0 := hmono
      _ ≤ (24 * R ^ 2) * M0 := mul_le_mul_of_nonneg_right hvol_shell hM0_nn
      _ = 24 * M0 * R ^ 2 := by ring
  dsimp [M0] at hev_outer
  linarith [hle_ev, hsplit_ev, hev_inner, hev_outer]

theorem cube_calibration_bound {u : Space → ℝ} (hu : IsBoundedSol u)
    (hpos : ∀ x, 0 < pd3 u 0 x)
    {C1 : ℝ} (hC1 : 0 ≤ C1) (hu1 : ∀ x, |u x| ≤ 1) (hpd1 : ∀ x i, |pd3 u i x| ≤ C1)
    {u_plus : Plane2 → ℝ} (hu_plus_c2 : ContDiff ℝ 2 u_plus)
    (hconv : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R,
      |u (x + T • e3 0) - u_plus (proj2 x)| ≤ ε ∧
      |pd3 u 0 (x + T • e3 0)| ≤ ε ∧
      (∀ i : Fin 2, |pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)| ≤ ε)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, 2 ≤ R →
      (∫ x in Q3 R, e3_en u x) ≤ 2 * R * (∫ y in Q2 R, e2_en u_plus y) + M * R ^ 2 := by
  let M0 : ℝ := (3 / 2) * (C1 + 6) ^ 2 + 1 / 4
  have hM0_nn : 0 ≤ M0 := by dsimp [M0]; positivity
  refine ⟨24 * M0, by positivity, fun R hR => ?_⟩
  suffices hε : ∀ ε : ℝ, 0 < ε →
      (∫ x in Q3 R, e3_en u x) ≤ 2 * R * (∫ y in Q2 R, e2_en u_plus y) + 24 * M0 * R ^ 2 + ε by
    by_contra! hgt
    have := hε (((∫ x in Q3 R, e3_en u x) - (2 * R * (∫ y in Q2 R, e2_en u_plus y) + 24 * M0 * R ^ 2)) / 2)
      (by linarith)
    linarith
  intro ε hε
  have hR1_pos : 0 < R - 1 := by linarith
  let V : ℝ := (2 * (R - 1)) ^ 3
  have hV_pos : 0 < V := by dsimp [V]; positivity
  let δ : ℝ := min 1 (ε / (V * (2 * C1 + 10)))
  have hδ : 0 < δ := lt_min one_pos (by dsimp [V]; positivity)
  obtain ⟨T0, hT0⟩ := hconv (R - 1) (by linarith) δ hδ
  let T : ℝ := max 1 T0
  have hT_pos : 0 < T := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hT_ge : T0 ≤ T := le_max_right _ _
  have hdiff_en (x : Space) (hx : x ∈ Q3 (R - 1)) :
      e3_en u (x + T • e3 0) ≤ e2_en u_plus (proj2 x) + ε / V := by
    obtain ⟨hu_c, hg0_c, hgi_c⟩ := hT0 T hT_ge x hx
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ * (2 * C1 + 10) ≤ ε / V := by
      have h1 : δ ≤ ε / (V * (2 * C1 + 10)) := min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ 2 * C1 + 10)
      have h3 : ε / (V * (2 * C1 + 10)) * (2 * C1 + 10) = ε / V := by field_simp
      linarith
    have hpd2_le (i : Fin 2) : |pd2 u_plus i (proj2 x)| ≤ C1 + 1 := by
      have h1 := hpd1 (x + T • e3 0) i.succ
      have h2 := hgi_c i
      have htri : |pd2 u_plus i (proj2 x)| ≤
          |pd3 u i.succ (x + T • e3 0)| + |pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)| := by
        have : pd2 u_plus i (proj2 x) =
            pd3 u i.succ (x + T • e3 0) - (pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)) := by ring
        conv_lhs => rw [this]
        exact abs_sub _ _
      linarith
    have hsq0 : (pd3 u 0 (x + T • e3 0)) ^ 2 ≤ δ := by
      rw [← sq_abs]; nlinarith [abs_nonneg (pd3 u 0 (x + T • e3 0))]
    have hsqi (i : Fin 2) :
        (pd3 u i.succ (x + T • e3 0)) ^ 2 - (pd2 u_plus i (proj2 x)) ^ 2 ≤ (2 * C1 + 1) * δ := by
      have hfac : (pd3 u i.succ (x + T • e3 0)) ^ 2 - (pd2 u_plus i (proj2 x)) ^ 2 =
          (pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)) *
            (pd3 u i.succ (x + T • e3 0) + pd2 u_plus i (proj2 x)) := by ring
      have hsum : |pd3 u i.succ (x + T • e3 0) + pd2 u_plus i (proj2 x)| ≤ 2 * C1 + 1 :=
        (abs_add_le _ _).trans (by linarith [hpd1 (x + T • e3 0) i.succ, hpd2_le i])
      calc _ ≤ |(pd3 u i.succ (x + T • e3 0)) ^ 2 - (pd2 u_plus i (proj2 x)) ^ 2| := le_abs_self _
        _ = |pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)| *
              |pd3 u i.succ (x + T • e3 0) + pd2 u_plus i (proj2 x)| := by rw [hfac, abs_mul]
        _ ≤ δ * (2 * C1 + 1) := mul_le_mul (hgi_c i) hsum (abs_nonneg _) hδ.le
        _ = (2 * C1 + 1) * δ := by ring
    have hW_diff : Wpot (u (x + T • e3 0)) - Wpot (u_plus (proj2 x)) ≤ 7 * δ := by
      have huT : |u (x + T • e3 0)| ≤ 1 := hu1 _
      have huP : |u_plus (proj2 x)| ≤ 2 := by
        have : |u_plus (proj2 x)| ≤ |u (x + T • e3 0)| + |u (x + T • e3 0) - u_plus (proj2 x)| := by
          have : u_plus (proj2 x) = u (x + T • e3 0) - (u (x + T • e3 0) - u_plus (proj2 x)) := by ring
          conv_lhs => rw [this]
          exact abs_sub _ _
        linarith
      have hfac : Wpot (u (x + T • e3 0)) - Wpot (u_plus (proj2 x)) =
          (u (x + T • e3 0) - u_plus (proj2 x)) *
            ((u (x + T • e3 0) + u_plus (proj2 x)) * (u (x + T • e3 0) ^ 2 + u_plus (proj2 x) ^ 2 - 2) / 4) := by
        unfold Wpot; ring
      have h1 : |u (x + T • e3 0) + u_plus (proj2 x)| ≤ 3 :=
        (abs_add_le _ _).trans (by linarith)
      have h2 : |u (x + T • e3 0) ^ 2 + u_plus (proj2 x) ^ 2 - 2| ≤ 7 := by
        have hs1 : u (x + T • e3 0) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (u (x + T • e3 0))]
        have hs2 : u_plus (proj2 x) ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (u_plus (proj2 x))]
        rw [abs_le]; constructor <;> linarith [sq_nonneg (u (x + T • e3 0)), sq_nonneg (u_plus (proj2 x))]
      have h3 : |(u (x + T • e3 0) + u_plus (proj2 x)) *
          (u (x + T • e3 0) ^ 2 + u_plus (proj2 x) ^ 2 - 2) / 4| ≤ 7 := by
        rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        nlinarith [abs_nonneg (u (x + T • e3 0) + u_plus (proj2 x)),
          abs_nonneg (u (x + T • e3 0) ^ 2 + u_plus (proj2 x) ^ 2 - 2)]
      calc _ ≤ |Wpot (u (x + T • e3 0)) - Wpot (u_plus (proj2 x))| := le_abs_self _
        _ = |u (x + T • e3 0) - u_plus (proj2 x)| *
              |(u (x + T • e3 0) + u_plus (proj2 x)) * (u (x + T • e3 0) ^ 2 + u_plus (proj2 x) ^ 2 - 2) / 4| := by
            rw [hfac, abs_mul]
        _ ≤ δ * 7 := mul_le_mul hu_c h3 (abs_nonneg _) hδ.le
        _ = 7 * δ := by ring
    unfold e3_en e2_en
    rw [Fin.sum_univ_three, Fin.sum_univ_two]
    have h1 := hsqi 0
    have h2 := hsqi 1
    simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at h1 h2
    linarith [hsq0, h1, h2, hW_diff, hδ2]
  have he2_cont : Continuous (e2_en u_plus) := by
    unfold e2_en Wpot
    have hpd2_c (i : Fin 2) : Continuous (pd2 u_plus i) :=
      ((hu_plus_c2.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (continuous_const.mul (continuous_finset_sum _ fun k _ => (hpd2_c k).pow 2)).add
      (((continuous_const.sub (hu_plus_c2.continuous.pow 2)).pow 2).div_const 4)
  have heuT_cont : Continuous (fun x : Space => e3_en u (x + T • e3 0)) := by
    unfold e3_en Wpot
    have hpd1_c (i : Fin 3) : Continuous (pd3 u i) :=
      ((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact ((continuous_const.mul (continuous_finset_sum _ fun k _ => (hpd1_c k).pow 2)).add
      (((continuous_const.sub (hu.regular.continuous.pow 2)).pow 2).div_const 4)).comp
      (continuous_id.add continuous_const)
  have hInt_lhs : IntegrableOn (fun x => e3_en u (x + T • e3 0)) (Q3 (R - 1)) volume :=
    heuT_cont.continuousOn.integrableOn_compact (isCompact_Q3_c (R - 1))
  have hInt_rhs : IntegrableOn (fun x => e2_en u_plus (proj2 x)) (Q3 (R - 1)) volume :=
    (he2_cont.comp continuous_proj2).continuousOn.integrableOn_compact (isCompact_Q3_c (R - 1))
  have hInt_c : IntegrableOn (fun _ : Space => ε / V) (Q3 (R - 1)) volume :=
    integrableOn_const (by rw [volume_Q3 (by linarith)]; exact ENNReal.ofReal_ne_top)
  have hmono_T := setIntegral_mono_on hInt_lhs (hInt_rhs.add hInt_c)
    (measurableSet_Q3 (R - 1)) hdiff_en
  simp only [Pi.add_apply] at hmono_T
  rw [integral_add hInt_rhs hInt_c, setIntegral_const, smul_eq_mul,
    Measure.real, volume_Q3 (by linarith), ENNReal.toReal_ofReal (by positivity),
    show (2 * (R - 1)) ^ 3 * (ε / V) = ε by dsimp [V]; field_simp,
    setIntegral_Q3_proj2 (by linarith) he2_cont] at hmono_T
  have he2_nn (y : Plane2) : 0 ≤ e2_en u_plus y := by
    unfold e2_en Wpot
    have : 0 ≤ ∑ i : Fin 2, (pd2 u_plus i y) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hQ2_sub : Q2 (R - 1) ⊆ Q2 R := fun y hy i => ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
  have hQ2_mono : (∫ y in Q2 (R - 1), e2_en u_plus y) ≤ ∫ y in Q2 R, e2_en u_plus y :=
    setIntegral_mono_set (he2_cont.continuousOn.integrableOn_compact (isCompact_Q2_c R))
      (ae_of_all _ he2_nn) (Eventually.of_forall hQ2_sub)
  have hQ2_nn : 0 ≤ ∫ y in Q2 R, e2_en u_plus y :=
    setIntegral_nonneg (measurableSet_Q2 R) fun y _ => he2_nn y
  have hscale : 2 * (R - 1) * (∫ y in Q2 (R - 1), e2_en u_plus y) ≤
      2 * R * (∫ y in Q2 R, e2_en u_plus y) := by
    calc 2 * (R - 1) * (∫ y in Q2 (R - 1), e2_en u_plus y)
        ≤ 2 * (R - 1) * (∫ y in Q2 R, e2_en u_plus y) :=
          mul_le_mul_of_nonneg_left hQ2_mono (by linarith)
      _ ≤ 2 * R * (∫ y in Q2 R, e2_en u_plus y) :=
          mul_le_mul_of_nonneg_right (by linarith) hQ2_nn
  dsimp [M0]
  linarith [calibration_step_T hu hpos hu1 hpd1 hR hT_pos, hmono_T, hscale]

end Mod3

namespace Mod4a
open InnerProductSpace MeasureTheory Filter Set Metric
open scoped Topology Laplacian Gradient
private theorem integral_split3 {f : Space → ℝ} (hf : Integrable f) :
    (∫ x : Space, f x) = ∫ t : ℝ, ∫ y : Plane2, f (mk3 t y) := by
  let e1 : Space ≃ᵐ (Fin 3 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm
  let e2m : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e3m : (Fin 2 → ℝ) ≃ᵐ Plane2 := MeasurableEquiv.toLp 2 (Fin 2 → ℝ)
  let e : Space ≃ᵐ ℝ × Plane2 := (e1.trans e2m).trans ((MeasurableEquiv.refl ℝ).prodCongr e3m)
  have hmp : MeasurePreserving e volume volume :=
    ((PiLp.volume_preserving_ofLp (Fin 3)).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)).trans
      ((MeasurePreserving.id volume).prod (PiLp.volume_preserving_toLp (Fin 2)))
  have he_symm (p : ℝ × Plane2) : e.symm p = mk3 p.1 p.2 := by
    ext k; fin_cases k <;> rfl
  have hint : Integrable (fun p : ℝ × Plane2 => f (mk3 p.1 p.2)) := by
    have h1 := (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    exact h1.congr (ae_of_all _ fun p => by simp [he_symm])
  rw [← hmp.symm.integral_comp e.symm.measurableEmbedding]
  have heq : (fun p : ℝ × Plane2 => f (e.symm p)) = fun p => f (mk3 p.1 p.2) := funext fun p => by rw [he_symm]
  rw [heq, Measure.volume_eq_prod, integral_prod _ hint]

private theorem stability_3d {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hpos : ∀ x, 0 < pd3 u 0 x)
    (hweak3 : ∀ (e : Space) (η : Space → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x : Space, inner ℝ (∇ (fun z => fderiv ℝ u z e) x) (∇ η x)) +
        (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x e)) = 0)
    {Φ : Space → ℝ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ) :
    0 ≤ ∫ x : Space, (‖∇ Φ x‖ ^ 2 + (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2) := by
  let v (x : Space) : ℝ := pd3 u 0 x
  have hv_c1 : ContDiff ℝ 1 v := (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  let η (x : Space) : ℝ := (Φ x) ^ 2 / v x
  have hη_c1 : ContDiff ℝ 1 η := (hΦ.pow 2).div hv_c1 fun x => (hpos x).ne'
  have hη_supp : HasCompactSupport η := by
    apply hΦc.mono'
    intro x hx; apply subset_closure; intro h0; exact hx (by simp [η, h0])
  have hw := hweak3 (e3 0) η hη_c1 hη_supp
  change (∫ x : Space, inner ℝ (∇ v x) (∇ η x)) +
    (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * v x)) = 0 at hw
  have hpd_η (i : Fin 3) (x : Space) :
      pd3 η i x = (2 * Φ x / v x) * pd3 Φ i x - ((Φ x) ^ 2 / (v x) ^ 2) * pd3 v i x := by
    have hΦl : HasDerivAt (fun s : ℝ => Φ (x + s • e3 i)) (pd3 Φ i x) 0 := by
      simpa [pd3] using line_deriv3 hΦ x (e3 i) 0
    have hvl : HasDerivAt (fun s : ℝ => v (x + s • e3 i)) (pd3 v i x) 0 := by
      simpa [pd3] using line_deriv3 hv_c1 x (e3 i) 0
    have hηl : HasDerivAt (fun s : ℝ => η (x + s • e3 i)) (pd3 η i x) 0 := by
      simpa [pd3] using line_deriv3 hη_c1 x (e3 i) 0
    have hdiv := (hΦl.fun_pow 2).fun_div hvl (by simpa using (hpos x).ne')
    have huq := hηl.unique hdiv
    simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at huq
    rw [huq]
    have hvne : v x ≠ 0 := (hpos x).ne'
    field_simp [hvne]
  have hpicone (x : Space) :
      ‖∇ Φ x‖ ^ 2 - inner ℝ (∇ v x) (∇ η x) =
        ∑ i : Fin 3, (pd3 Φ i x - (Φ x / v x) * pd3 v i x) ^ 2 := by
    rw [norm_grad3_sq, inner_grad3_eq, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpd_η i x]; ring
  have hpot (x : Space) : η x * ((3 * (u x) ^ 2 - 1) * v x) = (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2 := by
    have hvne : v x ≠ 0 := (hpos x).ne'
    dsimp [η]; field_simp [hvne]
  have hgrad_cont {f : Space → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
    (toDual ℝ Space).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hgrad_supp {f : Space → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (∇ f) :=
    hf.mono' fun x hx => support_fderiv_subset ℝ fun he => hx (by simp [gradient, he])
  have hInt1 : Integrable (fun x : Space => ‖∇ Φ x‖ ^ 2) :=
    ((hgrad_cont hΦ).norm.pow 2).integrable_of_hasCompactSupport
      ((hgrad_supp hΦc).mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
  have hInt2 : Integrable (fun x : Space => (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2) :=
    (((continuous_const.mul (hu.continuous.pow 2)).sub continuous_const).mul
      (hΦ.continuous.pow 2)).integrable_of_hasCompactSupport
      (hΦc.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
  have hInt3 : Integrable (fun x : Space => inner ℝ (∇ v x) (∇ η x)) :=
    ((hgrad_cont hv_c1).inner (hgrad_cont hη_c1)).integrable_of_hasCompactSupport
      ((hgrad_supp hη_supp).mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
  have hrew : (∫ x : Space, (‖∇ Φ x‖ ^ 2 + (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2)) =
      ∫ x : Space, ∑ i : Fin 3, (pd3 Φ i x - (Φ x / v x) * pd3 v i x) ^ 2 := by
    rw [integral_add hInt1 hInt2]
    have hsub := integral_sub hInt1 hInt3
    have hpot_int : (∫ x : Space, (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2) =
        -∫ x : Space, inner ℝ (∇ v x) (∇ η x) := by
      have : (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * v x)) =
          ∫ x : Space, (3 * (u x) ^ 2 - 1) * (Φ x) ^ 2 :=
        integral_congr_ae (ae_of_all _ hpot)
      linarith [hw]
    rw [hpot_int, ← sub_eq_add_neg, ← hsub]
    exact integral_congr_ae (ae_of_all _ hpicone)
  rw [hrew]
  exact integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem stability_2d {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hpos : ∀ x, 0 < pd3 u 0 x)
    (hweak3 : ∀ (e : Space) (η : Space → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x : Space, inner ℝ (∇ (fun z => fderiv ℝ u z e) x) (∇ η x)) +
        (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x e)) = 0)
    {u_plus : Plane2 → ℝ} (hu_plus_c : Continuous u_plus)
    (hconv : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R,
      |u (x + T • e3 0) - u_plus (proj2 x)| ≤ ε)
    {φ : Plane2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) := by
  obtain ⟨Rφ, hRφ⟩ := hφc.isBounded.subset_closedBall (0 : Plane2)
  let R0 : ℝ := max 1 Rφ
  have hφ_zero_out (y : Plane2) (hy : y ∉ Q2 R0) : φ y = 0 := by
    by_contra hne
    have hmem : y ∈ closedBall (0 : Plane2) Rφ := hRφ (subset_tsupport φ hne)
    rw [mem_closedBall, dist_zero_right] at hmem
    apply hy; intro i; rw [Set.mem_Icc, ← abs_le]
    have := PiLp.norm_apply_le y i
    rw [Real.norm_eq_abs] at this
    exact this.trans (hmem.trans (le_max_right 1 Rφ))
  have hstep_L (L : ℝ) (hL : 2 ≤ L) :
      0 ≤ (18 / (2 * (L - 1))) * (∫ y : Plane2, (φ y) ^ 2) +
        ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) := by
    let ψ (s : ℝ) : ℝ := cut1 L s
    let Φ0 (x : Space) : ℝ := ψ (x 0) * φ (proj2 x)
    have hΦ0_c1 : ContDiff ℝ 1 Φ0 :=
      ((contDiff_cut1 L).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff).mul
        (hφ.comp contDiff_proj2)
    have hΦ0_supp_Q : tsupport Φ0 ⊆ Q3 (max L R0) := by
      have hsub : Function.support Φ0 ⊆ Q3 (max L R0) := by
        intro x hx
        rw [Function.mem_support] at hx
        intro i; fin_cases i
        · rw [Set.mem_Icc, ← abs_le]
          by_contra! hgt
          have h0 : ψ (x 0) = 0 := cut1_zero (le_trans (le_max_left L R0) hgt.le)
          exact hx (by simp [Φ0, h0])
        · have hy : proj2 x ∈ Q2 R0 := by
            by_contra hnot; exact hx (by simp [Φ0, hφ_zero_out (proj2 x) hnot])
          have h0 : x 1 ∈ Icc (-R0) R0 := hy 0
          change x 1 ∈ Icc (-max L R0) (max L R0)
          exact ⟨by linarith [h0.1, le_max_right L R0], by linarith [h0.2, le_max_right L R0]⟩
        · have hy : proj2 x ∈ Q2 R0 := by
            by_contra hnot; exact hx (by simp [Φ0, hφ_zero_out (proj2 x) hnot])
          have h1 : x 2 ∈ Icc (-R0) R0 := hy 1
          change x 2 ∈ Icc (-max L R0) (max L R0)
          exact ⟨by linarith [h1.1, le_max_right L R0], by linarith [h1.2, le_max_right L R0]⟩
      exact closure_minimal hsub (isCompact_Q3 (max L R0)).isClosed
    have hΦ0_supp : HasCompactSupport Φ0 :=
      (isCompact_Q3 (max L R0)).of_isClosed_subset (isClosed_tsupport Φ0) hΦ0_supp_Q
    have hT_ineq (T : ℝ) :
        0 ≤ ∫ x : Space, (‖∇ Φ0 x‖ ^ 2 + (3 * (u (x + T • e3 0)) ^ 2 - 1) * (Φ0 x) ^ 2) := by
      let ΦT (x : Space) : ℝ := Φ0 (x - T • e3 0)
      have hΦT_c1 : ContDiff ℝ 1 ΦT := hΦ0_c1.comp (contDiff_id.sub contDiff_const)
      have hΦT_supp : HasCompactSupport ΦT :=
        hΦ0_supp.comp_homeomorph (Homeomorph.subRight (T • e3 0))
      have hstab := stability_3d hu hpos hweak3 hΦT_c1 hΦT_supp
      have hgrad_shift (x : Space) : ∇ ΦT (x + T • e3 0) = ∇ Φ0 x := by
        have hfd : fderiv ℝ ΦT (x + T • e3 0) = fderiv ℝ Φ0 x := by
          have ha : HasFDerivAt Φ0 (fderiv ℝ Φ0 x) (x + T • e3 0 - T • e3 0) := by
            simpa only [add_sub_cancel_right] using (hΦ0_c1.differentiable one_ne_zero x).hasFDerivAt
          have hb : HasFDerivAt (fun z : Space => z - T • e3 0) (ContinuousLinearMap.id ℝ Space) (x + T • e3 0) :=
            (hasFDerivAt_id (x + T • e3 0)).sub_const (T • e3 0)
          simpa only [ΦT, Function.comp_def, ContinuousLinearMap.comp_id] using (ha.comp (x + T • e3 0) hb).fderiv
        unfold gradient; rw [hfd]
      have hst' : 0 ≤ ∫ x : Space,
          (‖∇ ΦT (x + T • e3 0)‖ ^ 2 + (3 * (u (x + T • e3 0)) ^ 2 - 1) * (ΦT (x + T • e3 0)) ^ 2) := by
        have hshift := integral_add_right_eq_self (μ := volume)
          (fun x : Space => ‖∇ ΦT x‖ ^ 2 + (3 * (u x) ^ 2 - 1) * (ΦT x) ^ 2) (T • e3 0)
        linarith
      refine hst'.trans_eq (integral_congr_ae (ae_of_all _ fun x => ?_))
      dsimp only
      rw [hgrad_shift x]; simp [ΦT]
    have hlim_T : 0 ≤ ∫ x : Space, (‖∇ Φ0 x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2) := by
      have hgrad_cont : Continuous (∇ Φ0) :=
        (toDual ℝ Space).symm.continuous.comp (hΦ0_c1.continuous_fderiv one_ne_zero)
      have hgrad_supp : HasCompactSupport (∇ Φ0) :=
        hΦ0_supp.mono' fun x hx => support_fderiv_subset ℝ fun he => hx (by simp [gradient, he])
      have hI1 : Integrable (fun x : Space => ‖∇ Φ0 x‖ ^ 2) :=
        (hgrad_cont.norm.pow 2).integrable_of_hasCompactSupport
          (hgrad_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
      have hΦ0_sq_int : Integrable (fun x : Space => (Φ0 x) ^ 2) :=
        (hΦ0_c1.continuous.pow 2).integrable_of_hasCompactSupport
          (hΦ0_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
      have hI2 : Integrable (fun x : Space => (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2) :=
        (((continuous_const.mul ((hu_plus_c.comp contDiff_proj2.continuous).pow 2)).sub continuous_const).mul
          (hΦ0_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hΦ0_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
      suffices hε : ∀ ε : ℝ, 0 < ε →
          -ε ≤ ∫ x : Space, (‖∇ Φ0 x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2) by
        by_contra! hneg
        have := hε (-(∫ x : Space, (‖∇ Φ0 x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2)) / 2)
          (by linarith)
        linarith
      intro ε hε
      let K : Set Space := Q3 (max L R0)
      obtain ⟨Mu, hMu⟩ := (isCompact_Q3 (max L R0)).exists_bound_of_continuousOn
        (hu_plus_c.comp contDiff_proj2.continuous).continuousOn
      have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans
        (hMu 0 fun i => by
          simp only [PiLp.zero_apply, Set.mem_Icc]
          exact ⟨by linarith [le_max_left L R0], by linarith [le_max_left L R0]⟩)
      let J : ℝ := ∫ x : Space, (Φ0 x) ^ 2
      have hJ0 : 0 ≤ J := integral_nonneg fun x => sq_nonneg _
      let δ : ℝ := min 1 (ε / (3 * (2 * Mu + 1) * (J + 1)))
      have hδ : 0 < δ := lt_min one_pos (by positivity)
      obtain ⟨T, hT⟩ := hconv (max L R0) (by linarith [le_max_left L R0]) δ hδ
      have hT_self := hT T le_rfl
      have hdiff_pt (x : Space) :
          (3 * (u (x + T • e3 0)) ^ 2 - 1) * (Φ0 x) ^ 2 -
            (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2 ≤
          (3 * (2 * Mu + 1) * δ) * (Φ0 x) ^ 2 := by
        by_cases hxK : x ∈ K
        · have hc := hT_self x hxK
          have hup : |u_plus (proj2 x)| ≤ Mu := by simpa [Real.norm_eq_abs] using hMu x hxK
          have huT : |u (x + T • e3 0)| ≤ Mu + 1 := by
            have : u (x + T • e3 0) = u_plus (proj2 x) + (u (x + T • e3 0) - u_plus (proj2 x)) := by ring
            rw [this]
            exact (abs_add_le _ _).trans (by linarith [min_le_left (1 : ℝ) (ε / (3 * (2 * Mu + 1) * (J + 1)))])
          have hfac : (3 * (u (x + T • e3 0)) ^ 2 - 1) - (3 * (u_plus (proj2 x)) ^ 2 - 1) =
              3 * (u (x + T • e3 0) - u_plus (proj2 x)) * (u (x + T • e3 0) + u_plus (proj2 x)) := by ring
          have hsum : |u (x + T • e3 0) + u_plus (proj2 x)| ≤ 2 * Mu + 1 :=
            (abs_add_le _ _).trans (by linarith)
          have hcoeff : (3 * (u (x + T • e3 0)) ^ 2 - 1) - (3 * (u_plus (proj2 x)) ^ 2 - 1) ≤
              3 * (2 * Mu + 1) * δ := by
            calc _ ≤ |(3 * (u (x + T • e3 0)) ^ 2 - 1) - (3 * (u_plus (proj2 x)) ^ 2 - 1)| := le_abs_self _
              _ = 3 * |u (x + T • e3 0) - u_plus (proj2 x)| * |u (x + T • e3 0) + u_plus (proj2 x)| := by
                  rw [hfac, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
              _ ≤ 3 * δ * (2 * Mu + 1) := mul_le_mul (by linarith) hsum (abs_nonneg _) (by positivity)
              _ = 3 * (2 * Mu + 1) * δ := by ring
          have hmul := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Φ0 x))
          linarith
        · have hΦ0_0 : Φ0 x = 0 := by
            by_contra hne; exact hxK (hΦ0_supp_Q (subset_tsupport Φ0 hne))
          simp [hΦ0_0]
      have hIT : Integrable (fun x : Space => (3 * (u (x + T • e3 0)) ^ 2 - 1) * (Φ0 x) ^ 2) :=
        (((continuous_const.mul ((hu.continuous.comp (continuous_id.add continuous_const)).pow 2)).sub
          continuous_const).mul (hΦ0_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hΦ0_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
      have hmono := integral_mono (hIT.sub hI2) (hΦ0_sq_int.const_mul (3 * (2 * Mu + 1) * δ)) hdiff_pt
      simp only [Pi.sub_apply] at hmono
      rw [integral_sub hIT hI2, integral_const_mul] at hmono
      have hδJ : 3 * (2 * Mu + 1) * δ * J ≤ ε := by
        have hle : δ ≤ ε / (3 * (2 * Mu + 1) * (J + 1)) := min_le_right _ _
        calc 3 * (2 * Mu + 1) * δ * J
            ≤ 3 * (2 * Mu + 1) * (ε / (3 * (2 * Mu + 1) * (J + 1))) * J :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (by positivity)) hJ0
          _ = ε * (J / (J + 1)) := by field_simp
          _ ≤ ε := mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).mpr (by linarith))
      have h0 := hT_ineq T
      rw [integral_add hI1 hIT] at h0
      rw [integral_add hI1 hI2]
      linarith
    have hpd0 (x : Space) : pd3 Φ0 0 x = deriv ψ (x 0) * φ (proj2 x) := by
      have h1 := line_deriv3 hΦ0_c1 x (e3 0) 0
      have h2 : HasDerivAt (fun s : ℝ => Φ0 (x + s • e3 0)) (deriv ψ (x 0) * φ (proj2 x)) 0 := by
        have heq : (fun s : ℝ => Φ0 (x + s • e3 0)) = fun s => ψ (x 0 + s) * φ (proj2 x) := by
          ext s
          have h0 : (x + s • e3 0) 0 = x 0 + s := by simp [e3]
          have hp : proj2 (x + s • e3 0) = proj2 x := by ext k; fin_cases k <;> simp [proj2, e3]
          change ψ ((x + s • e3 0) 0) * φ (proj2 (x + s • e3 0)) = _
          rw [h0, hp]
        rw [heq]
        have ha : HasDerivAt (fun s : ℝ => x 0 + s) 1 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
        have hb : HasDerivAt ψ (deriv ψ (x 0)) (x 0 + 0) := by
          simpa using ((contDiff_cut1 L).differentiable one_ne_zero (x 0)).hasDerivAt
        have hc := (hb.comp 0 ha).mul_const (φ (proj2 x))
        rw [mul_one] at hc; exact hc
      simpa [pd3] using h1.unique h2
    have hpdi (i : Fin 2) (x : Space) : pd3 Φ0 i.succ x = ψ (x 0) * pd2 φ i (proj2 x) := by
      have h1 := line_deriv3 hΦ0_c1 x (e3 i.succ) 0
      have h2 : HasDerivAt (fun s : ℝ => Φ0 (x + s • e3 i.succ)) (ψ (x 0) * pd2 φ i (proj2 x)) 0 := by
        have heq : (fun s : ℝ => Φ0 (x + s • e3 i.succ)) =
            fun s => ψ (x 0) * φ (proj2 x + s • e2 i) := by
          ext s
          have h0 : (x + s • e3 i.succ) 0 = x 0 := by fin_cases i <;> simp [e3]
          have hp : proj2 (x + s • e3 i.succ) = proj2 x + s • e2 i := by
            ext k; fin_cases i <;> fin_cases k <;> simp [proj2, e2, e3]
          change ψ ((x + s • e3 i.succ) 0) * φ (proj2 (x + s • e3 i.succ)) = _
          rw [h0, hp]
        rw [heq]
        have hb := line_deriv2 hφ (proj2 x) (e2 i) 0
        simpa [pd2] using hb.const_mul (ψ (x 0))
      simpa [pd3] using h1.unique h2
    have hsplit_pt (x : Space) :
        ‖∇ Φ0 x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2 =
          (deriv ψ (x 0)) ^ 2 * (φ (proj2 x)) ^ 2 +
          (ψ (x 0)) ^ 2 * (‖∇ φ (proj2 x)‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (φ (proj2 x)) ^ 2) := by
      have h1 := hpdi 0 x; simp only [Fin.succ_zero_eq_one] at h1
      have h2 := hpdi 1 x; simp only [Fin.succ_one_eq_two] at h2
      rw [norm_grad3_sq, norm_grad2_sq, Fin.sum_univ_three, Fin.sum_univ_two, hpd0 x, h1, h2]
      dsimp [Φ0]; ring
    have hint_tot : Integrable (fun x : Space =>
        ‖∇ Φ0 x‖ ^ 2 + (3 * (u_plus (proj2 x)) ^ 2 - 1) * (Φ0 x) ^ 2) := by
      have hgrad_cont : Continuous (∇ Φ0) :=
        (toDual ℝ Space).symm.continuous.comp (hΦ0_c1.continuous_fderiv one_ne_zero)
      have hgrad_supp : HasCompactSupport (∇ Φ0) :=
        hΦ0_supp.mono' fun x hx => support_fderiv_subset ℝ fun he => hx (by simp [gradient, he])
      exact ((hgrad_cont.norm.pow 2).integrable_of_hasCompactSupport
        (hgrad_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))).add
        ((((continuous_const.mul ((hu_plus_c.comp contDiff_proj2.continuous).pow 2)).sub continuous_const).mul
          (hΦ0_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hΦ0_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0])))
    rw [integral_split3 hint_tot] at hlim_T
    have hfactor : (∫ t : ℝ, ∫ y : Plane2,
        (‖∇ Φ0 (mk3 t y)‖ ^ 2 + (3 * (u_plus (proj2 (mk3 t y))) ^ 2 - 1) * (Φ0 (mk3 t y)) ^ 2)) =
        (∫ t : ℝ, (deriv ψ t) ^ 2) * (∫ y : Plane2, (φ y) ^ 2) +
        (∫ t : ℝ, (ψ t) ^ 2) * ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) := by
      have hφ2_int : Integrable (fun y : Plane2 => (φ y) ^ 2) :=
        (hφ.continuous.pow 2).integrable_of_hasCompactSupport
          (hφc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
      have hgrad2_c : Continuous (∇ φ) :=
        (toDual ℝ Plane2).symm.continuous.comp (hφ.continuous_fderiv one_ne_zero)
      have hgrad2_s : HasCompactSupport (∇ φ) :=
        hφc.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [gradient, he])
      have hQ_int : Integrable (fun y : Plane2 =>
          ‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) :=
        ((hgrad2_c.norm.pow 2).integrable_of_hasCompactSupport
          (hgrad2_s.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))).add
        ((((continuous_const.mul (hu_plus_c.pow 2)).sub continuous_const).mul
          (hφ.continuous.pow 2)).integrable_of_hasCompactSupport
          (hφc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0])))
      have hψ2_int : Integrable (fun t : ℝ => (ψ t) ^ 2) :=
        ((contDiff_cut1 L).continuous.pow 2).integrable_of_hasCompactSupport
          ((hasCompactSupport_cut1 L).mono' fun s hs => subset_closure fun h0 => hs (by simp [h0]))
      have hdψ2_int : Integrable (fun t : ℝ => (deriv ψ t) ^ 2) := by
        refine (((contDiff_cut1 L).continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -L) (b := L)) ?_
        intro s hs; by_contra hnot
        have hge : L ≤ |s| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
          rcases hnot with h1 | h2
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        exact hs (by simp [ψ, deriv_cut1_zero_outer hge])
      have hinner (t : ℝ) :
          (∫ y : Plane2, (‖∇ Φ0 (mk3 t y)‖ ^ 2 + (3 * (u_plus (proj2 (mk3 t y))) ^ 2 - 1) * (Φ0 (mk3 t y)) ^ 2)) =
          (deriv ψ t) ^ 2 * (∫ y : Plane2, (φ y) ^ 2) +
          (ψ t) ^ 2 * (∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2)) := by
        have hcongr : (fun y : Plane2 =>
            ‖∇ Φ0 (mk3 t y)‖ ^ 2 + (3 * (u_plus (proj2 (mk3 t y))) ^ 2 - 1) * (Φ0 (mk3 t y)) ^ 2) =
            fun y => (deriv ψ t) ^ 2 * (φ y) ^ 2 +
              (ψ t) ^ 2 * (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) := by
          ext y; rw [hsplit_pt (mk3 t y)]
          have h0 : (mk3 t y) 0 = t := by simp [mk3]
          have hp : proj2 (mk3 t y) = y := by ext k; fin_cases k <;> simp [mk3, proj2]
          rw [h0, hp]
        rw [hcongr, integral_add (hφ2_int.const_mul _) (hQ_int.const_mul _),
          integral_const_mul, integral_const_mul]
      simp_rw [hinner]
      rw [integral_add (hdψ2_int.mul_const _) (hψ2_int.mul_const _),
        integral_mul_const, integral_mul_const]
    rw [hfactor] at hlim_T
    have hψ_pos : 0 < ∫ t : ℝ, (ψ t) ^ 2 := lt_of_lt_of_le (by linarith) (integral_cut1_sq_ge hL)
    have hψ_ge : 2 * (L - 1) ≤ ∫ t : ℝ, (ψ t) ^ 2 := integral_cut1_sq_ge hL
    have hdψ_le : (∫ t : ℝ, (deriv ψ t) ^ 2) ≤ 18 := integral_deriv_cut1_sq_le hL
    have hφ2_nn : 0 ≤ ∫ y : Plane2, (φ y) ^ 2 := integral_nonneg fun y => sq_nonneg _
    have hdiv := div_nonneg hlim_T hψ_pos.le
    rw [add_div, mul_div_right_comm, mul_div_cancel_left₀ _ hψ_pos.ne'] at hdiv
    have hrat : (∫ t : ℝ, (deriv ψ t) ^ 2) / (∫ t : ℝ, (ψ t) ^ 2) ≤ 18 / (2 * (L - 1)) :=
      div_le_div₀ (by norm_num) hdψ_le (by linarith) hψ_ge
    have hmul : (∫ t : ℝ, (deriv ψ t) ^ 2) / (∫ t : ℝ, (ψ t) ^ 2) * (∫ y : Plane2, (φ y) ^ 2) ≤
        (18 / (2 * (L - 1))) * (∫ y : Plane2, (φ y) ^ 2) :=
      mul_le_mul_of_nonneg_right hrat hφ2_nn
    linarith
  by_contra! hneg
  let Q := ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2)
  let A := ∫ y : Plane2, (φ y) ^ 2
  have hA0 : 0 ≤ A := integral_nonneg fun y => sq_nonneg _
  let L : ℝ := max 2 (1 + 18 * (A + 1) / (-Q))
  have hL2 : 2 ≤ L := le_max_left _ _
  have hL_big : 18 * (A + 1) / (-Q) ≤ L - 1 := by dsimp [L]; linarith [le_max_right 2 (1 + 18 * (A + 1) / (-Q))]
  have hstep := hstep_L L hL2
  have h1 : 18 / (2 * (L - 1)) * A < -Q := by
    have hL1 : 0 < L - 1 := by linarith
    have hQpos : 0 < -Q := by dsimp [Q]; linarith
    have h2 : 18 * (A + 1) ≤ (-Q) * (L - 1) := by
      have := (div_le_iff₀ hQpos).mp hL_big; linarith
    have h3 : 18 * A < (-Q) * (2 * (L - 1)) := by nlinarith
    have h4 : 18 * A / (2 * (L - 1)) < -Q := (div_lt_iff₀ (by positivity)).mpr h3
    have h5 : 18 / (2 * (L - 1)) * A = 18 * A / (2 * (L - 1)) := by ring
    linarith
  dsimp [Q, A] at h1
  linarith

theorem weak_partial_2d {u : Space → ℝ} (hu : ContDiff ℝ 2 u)
    (hweak3 : ∀ (e : Space) (η : Space → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x : Space, inner ℝ (∇ (fun z => fderiv ℝ u z e) x) (∇ η x)) +
        (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x e)) = 0)
    {u_plus : Plane2 → ℝ} (hu_plus : ContDiff ℝ 2 u_plus)
    (hconv2 : ∀ R : ℝ, 0 ≤ R → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℝ, ∀ T : ℝ, T0 ≤ T → ∀ x ∈ Q3 R,
      |u (x + T • e3 0) - u_plus (proj2 x)| ≤ ε ∧
      (∀ i : Fin 2, |pd3 u i.succ (x + T • e3 0) - pd2 u_plus i (proj2 x)| ≤ ε) ∧
      (∀ i : Fin 2, |pd32 u i.succ 0 (x + T • e3 0)| ≤ ε) ∧
      (∀ i j : Fin 2, |pd32 u i.succ j.succ (x + T • e3 0) - pd22 u_plus i j (proj2 x)| ≤ ε))
    (j : Fin 2) {η : Plane2 → ℝ} (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    (∫ y : Plane2, inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) +
      (∫ y : Plane2, η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) = 0 := by
  obtain ⟨Rη, hRη⟩ := hηc.isBounded.subset_closedBall (0 : Plane2)
  let R0 : ℝ := max 2 Rη
  have hη_zero_out (y : Plane2) (hy : y ∉ Q2 R0) : η y = 0 := by
    by_contra hne
    have hmem : y ∈ closedBall (0 : Plane2) Rη := hRη (subset_tsupport η hne)
    rw [mem_closedBall, dist_zero_right] at hmem
    apply hy; intro i; rw [Set.mem_Icc, ← abs_le]
    have := PiLp.norm_apply_le y i; rw [Real.norm_eq_abs] at this
    exact this.trans (hmem.trans (le_max_right 2 Rη))
  let ψ (s : ℝ) : ℝ := cut1 2 s
  let Φ0 (x : Space) : ℝ := ψ (x 0) * η (proj2 x)
  have hΦ0_c1 : ContDiff ℝ 1 Φ0 :=
    ((contDiff_cut1 2).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff).mul
      (hη.comp contDiff_proj2)
  have hΦ0_supp_Q : tsupport Φ0 ⊆ Q3 R0 := by
    have hsub : Function.support Φ0 ⊆ Q3 R0 := by
      intro x hx; rw [Function.mem_support] at hx
      intro i; fin_cases i
      · rw [Set.mem_Icc, ← abs_le]
        by_contra! hgt
        have h2le : 2 ≤ |x 0| := by dsimp [R0] at hgt; linarith [le_max_left 2 Rη]
        exact hx (by simp [Φ0, ψ, cut1_zero h2le])
      · have hy : proj2 x ∈ Q2 R0 := by
          by_contra hnot; exact hx (by simp [Φ0, hη_zero_out (proj2 x) hnot])
        simpa [proj2] using hy 0
      · have hy : proj2 x ∈ Q2 R0 := by
          by_contra hnot; exact hx (by simp [Φ0, hη_zero_out (proj2 x) hnot])
        simpa [proj2] using hy 1
    exact closure_minimal hsub (isCompact_Q3 R0).isClosed
  have hΦ0_supp : HasCompactSupport Φ0 :=
    (isCompact_Q3 R0).of_isClosed_subset (isClosed_tsupport Φ0) hΦ0_supp_Q
  have hpd0 (x : Space) : pd3 Φ0 0 x = deriv ψ (x 0) * η (proj2 x) := by
    have h1 := line_deriv3 hΦ0_c1 x (e3 0) 0
    have h2 : HasDerivAt (fun s : ℝ => Φ0 (x + s • e3 0)) (deriv ψ (x 0) * η (proj2 x)) 0 := by
      have heq : (fun s : ℝ => Φ0 (x + s • e3 0)) = fun s => ψ (x 0 + s) * η (proj2 x) := by
        ext s
        have h0 : (x + s • e3 0) 0 = x 0 + s := by simp [e3]
        have hp : proj2 (x + s • e3 0) = proj2 x := by ext k; fin_cases k <;> simp [proj2, e3]
        change ψ ((x + s • e3 0) 0) * η (proj2 (x + s • e3 0)) = _
        rw [h0, hp]
      rw [heq]
      have ha : HasDerivAt (fun s : ℝ => x 0 + s) 1 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_add (x 0)
      have hb : HasDerivAt ψ (deriv ψ (x 0)) (x 0 + 0) := by
        simpa using ((contDiff_cut1 2).differentiable one_ne_zero (x 0)).hasDerivAt
      have hc := (hb.comp 0 ha).mul_const (η (proj2 x))
      rw [mul_one] at hc; exact hc
    simpa [pd3] using h1.unique h2
  have hpdi (k : Fin 2) (x : Space) : pd3 Φ0 k.succ x = ψ (x 0) * pd2 η k (proj2 x) := by
    have h1 := line_deriv3 hΦ0_c1 x (e3 k.succ) 0
    have h2 : HasDerivAt (fun s : ℝ => Φ0 (x + s • e3 k.succ)) (ψ (x 0) * pd2 η k (proj2 x)) 0 := by
      have heq : (fun s : ℝ => Φ0 (x + s • e3 k.succ)) =
          fun s => ψ (x 0) * η (proj2 x + s • e2 k) := by
        ext s
        have h0 : (x + s • e3 k.succ) 0 = x 0 := by fin_cases k <;> simp [e3]
        have hp : proj2 (x + s • e3 k.succ) = proj2 x + s • e2 k := by
          ext m; fin_cases k <;> fin_cases m <;> simp [proj2, e2, e3]
        change ψ ((x + s • e3 k.succ) 0) * η (proj2 (x + s • e3 k.succ)) = _
        rw [h0, hp]
      rw [heq]
      have hb := line_deriv2 hη (proj2 x) (e2 k) 0
      simpa [pd2] using hb.const_mul (ψ (x 0))
    simpa [pd3] using h1.unique h2
  let F_T (T : ℝ) (x : Space) : ℝ :=
    pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x +
    pd32 u j.succ 1 (x + T • e3 0) * pd3 Φ0 1 x +
    pd32 u j.succ 2 (x + T • e3 0) * pd3 Φ0 2 x +
    Φ0 x * ((3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0))
  let F_lim (x : Space) : ℝ :=
    pd22 u_plus j 0 (proj2 x) * pd3 Φ0 1 x +
    pd22 u_plus j 1 (proj2 x) * pd3 Φ0 2 x +
    Φ0 x * ((3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x))
  have hFT_zero (T : ℝ) : (∫ x : Space, F_T T x) = 0 := by
    let ΦT (x : Space) : ℝ := Φ0 (x - T • e3 0)
    have hΦT_c1 : ContDiff ℝ 1 ΦT := hΦ0_c1.comp (contDiff_id.sub contDiff_const)
    have hΦT_supp : HasCompactSupport ΦT :=
      hΦ0_supp.comp_homeomorph (Homeomorph.subRight (T • e3 0))
    have hw := hweak3 (e3 j.succ) ΦT hΦT_c1 hΦT_supp
    change (∫ x : Space, inner ℝ (∇ (pd3 u j.succ) x) (∇ ΦT x)) +
      (∫ x : Space, ΦT x * ((3 * (u x) ^ 2 - 1) * pd3 u j.succ x)) = 0 at hw
    have hgrad_shift (x : Space) : ∇ ΦT (x + T • e3 0) = ∇ Φ0 x := by
      have hfd : fderiv ℝ ΦT (x + T • e3 0) = fderiv ℝ Φ0 x := by
        have ha : HasFDerivAt Φ0 (fderiv ℝ Φ0 x) (x + T • e3 0 - T • e3 0) := by
          simpa only [add_sub_cancel_right] using (hΦ0_c1.differentiable one_ne_zero x).hasFDerivAt
        have hb : HasFDerivAt (fun z : Space => z - T • e3 0) (ContinuousLinearMap.id ℝ Space) (x + T • e3 0) :=
          (hasFDerivAt_id (x + T • e3 0)).sub_const (T • e3 0)
        simpa only [ΦT, Function.comp_def, ContinuousLinearMap.comp_id] using (ha.comp (x + T • e3 0) hb).fderiv
      unfold gradient; rw [hfd]
    have hv_c1 : ContDiff ℝ 1 (pd3 u j.succ) := (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
    have hgrad_c {f : Space → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
      (toDual ℝ Space).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
    have hgrad_s {f : Space → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (∇ f) :=
      hf.mono' fun x hx => support_fderiv_subset ℝ fun he => hx (by simp [gradient, he])
    have hI1 : Integrable (fun x : Space => inner ℝ (∇ (pd3 u j.succ) x) (∇ ΦT x)) :=
      ((hgrad_c hv_c1).inner (hgrad_c hΦT_c1)).integrable_of_hasCompactSupport
        ((hgrad_s hΦT_supp).mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
    have hI2 : Integrable (fun x : Space => ΦT x * ((3 * (u x) ^ 2 - 1) * pd3 u j.succ x)) :=
      ((hΦT_c1.continuous.mul (((continuous_const.mul (hu.continuous.pow 2)).sub continuous_const).mul
        hv_c1.continuous))).integrable_of_hasCompactSupport
        (hΦT_supp.mono' fun x hx => subset_closure fun h0 => hx (by simp [h0]))
    rw [← integral_add hI1 hI2] at hw
    have hshift := integral_add_right_eq_self (μ := volume)
      (fun x : Space => inner ℝ (∇ (pd3 u j.succ) x) (∇ ΦT x) +
        ΦT x * ((3 * (u x) ^ 2 - 1) * pd3 u j.succ x)) (T • e3 0)
    rw [← hshift] at hw
    rw [← hw]
    apply integral_congr_ae; refine ae_of_all _ fun x => ?_
    dsimp only
    rw [hgrad_shift x, inner_grad3_pts, Fin.sum_univ_three]
    simp only [ΦT, add_sub_cancel_right, F_T, pd32]
  have hFlim_zero : (∫ x : Space, F_lim x) = 0 := by
    have hpdΦ_c (k : Fin 3) : Continuous (pd3 Φ0 k) :=
      (hΦ0_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hpdΦ_supp (k : Fin 3) (x : Space) (hx : x ∉ Q3 R0) : pd3 Φ0 k x = 0 := by
      have hnb : x ∉ tsupport Φ0 := fun hm => hx (hΦ0_supp_Q hm)
      have h0 : fderiv ℝ Φ0 x = 0 := by
        by_contra hne; exact hnb (support_fderiv_subset ℝ hne)
      simp [pd3, h0]
    have hΦ0_zero (x : Space) (hx : x ∉ Q3 R0) : Φ0 x = 0 := by
      by_contra hne; exact hx (hΦ0_supp_Q (subset_tsupport Φ0 hne))
    have hpd2_c (i : Fin 2) : Continuous (pd2 u_plus i) :=
      ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hpd22_c (i k : Fin 2) : Continuous (pd22 u_plus i k) :=
      (((hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    have hFlim_c : Continuous F_lim :=
      ((((hpd22_c j 0).comp contDiff_proj2.continuous).mul (hpdΦ_c 1)).add
        (((hpd22_c j 1).comp contDiff_proj2.continuous).mul (hpdΦ_c 2))).add
        (hΦ0_c1.continuous.mul (((continuous_const.mul ((hu_plus.continuous.comp contDiff_proj2.continuous).pow 2)).sub
          continuous_const).mul ((hpd2_c j).comp contDiff_proj2.continuous)))
    have hFlim_int : Integrable F_lim := by
      refine hFlim_c.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Q3 R0) ?_
      intro x hx; by_contra hnot
      exact hx (by simp [F_lim, hpdΦ_supp 1 x hnot, hpdΦ_supp 2 x hnot, hΦ0_zero x hnot])
    have hFT_int (T : ℝ) : Integrable (F_T T) := by
      have hpd1_c (i : Fin 3) : Continuous (pd3 u i) :=
        ((hu.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
      have hpd2_3c (i k : Fin 3) : Continuous (pd32 u i k) :=
        (((hu.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          one_ne_zero).clm_apply continuous_const
      have hsh : Continuous (fun x : Space => x + T • e3 0) := continuous_id.add continuous_const
      have hc : Continuous (F_T T) :=
        (((((hpd2_3c j.succ 0).comp hsh).mul (hpdΦ_c 0)).add
          (((hpd2_3c j.succ 1).comp hsh).mul (hpdΦ_c 1))).add
          (((hpd2_3c j.succ 2).comp hsh).mul (hpdΦ_c 2))).add
          (hΦ0_c1.continuous.mul (((continuous_const.mul ((hu.continuous.comp hsh).pow 2)).sub
            continuous_const).mul ((hpd1_c j.succ).comp hsh)))
      refine hc.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Q3 R0) ?_
      intro x hx; by_contra hnot
      exact hx (by simp [F_T, hpdΦ_supp 0 x hnot, hpdΦ_supp 1 x hnot, hpdΦ_supp 2 x hnot, hΦ0_zero x hnot])
    obtain ⟨B0, hB0⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn (hpdΦ_c 0).continuousOn
    obtain ⟨B1, hB1⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn (hpdΦ_c 1).continuousOn
    obtain ⟨B2, hB2⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn (hpdΦ_c 2).continuousOn
    obtain ⟨BΦ, hBΦ⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn hΦ0_c1.continuous.continuousOn
    obtain ⟨Bu, hBu⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn
      (hu_plus.continuous.comp contDiff_proj2.continuous).continuousOn
    obtain ⟨Bg, hBg⟩ := (isCompact_Q3 R0).exists_bound_of_continuousOn
      ((hpd2_c j).comp contDiff_proj2.continuous).continuousOn
    let B : ℝ := max 0 B0 + max 0 B1 + max 0 B2 + max 0 BΦ * (3 * (max 0 Bu + 1) ^ 2 + 1 + 3 * (2 * max 0 Bu + 1) * max 0 Bg) + 1
    have hB_pos : 0 < B := by
      have : 0 ≤ max 0 B0 := le_max_left _ _
      have : 0 ≤ max 0 B1 := le_max_left _ _
      have : 0 ≤ max 0 B2 := le_max_left _ _
      have : 0 ≤ max 0 BΦ := le_max_left _ _
      have : 0 ≤ max 0 Bu := le_max_left _ _
      have : 0 ≤ max 0 Bg := le_max_left _ _
      dsimp [B]; positivity
    have hvol_Q3 : volume (Q3 R0) < ⊤ := (isCompact_Q3 R0).measure_lt_top
    suffices hε : ∀ ε : ℝ, 0 < ε → |∫ x : Space, F_lim x| ≤ ε by
      by_contra hne
      have hpos_a : 0 < |∫ x : Space, F_lim x| := abs_pos.mpr hne
      linarith [hε (|∫ x : Space, F_lim x| / 2) (half_pos hpos_a)]
    intro ε hε
    let V : ℝ := volume.real (Q3 R0) + 1
    have hV_pos : 0 < V := by dsimp [V]; positivity
    let δ : ℝ := min 1 (ε / (B * V))
    have hδ : 0 < δ := lt_min one_pos (by positivity)
    obtain ⟨T, hT⟩ := hconv2 R0 (by linarith [le_max_left 2 Rη]) δ hδ
    have hT_self := hT T le_rfl
    have hpt (x : Space) : |F_T T x - F_lim x| ≤ (B * δ) * (Q3 R0).indicator (fun _ => (1 : ℝ)) x := by
      by_cases hx : x ∈ Q3 R0
      · rw [Set.indicator_of_mem hx, mul_one]
        obtain ⟨hu_c, hg_c, h0_c, h2_c⟩ := hT_self x hx
        have hδ1 : δ ≤ 1 := min_le_left _ _
        have h1 : |pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x| ≤ max 0 B0 * δ := by
          rw [abs_mul]
          have ha : |pd3 Φ0 0 x| ≤ max 0 B0 := (by simpa [Real.norm_eq_abs] using hB0 x hx : |pd3 Φ0 0 x| ≤ B0).trans (le_max_right _ _)
          have hb := h0_c j
          nlinarith [abs_nonneg (pd32 u j.succ 0 (x + T • e3 0)), abs_nonneg (pd3 Φ0 0 x)]
        have h2 : |(pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)) * pd3 Φ0 1 x| ≤ max 0 B1 * δ := by
          rw [abs_mul]
          have ha : |pd3 Φ0 1 x| ≤ max 0 B1 := (by simpa [Real.norm_eq_abs] using hB1 x hx : |pd3 Φ0 1 x| ≤ B1).trans (le_max_right _ _)
          have hb : |pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)| ≤ δ := by
            simpa [Fin.succ_zero_eq_one] using h2_c j 0
          nlinarith [abs_nonneg (pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)), abs_nonneg (pd3 Φ0 1 x)]
        have h3 : |(pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)) * pd3 Φ0 2 x| ≤ max 0 B2 * δ := by
          rw [abs_mul]
          have ha : |pd3 Φ0 2 x| ≤ max 0 B2 := (by simpa [Real.norm_eq_abs] using hB2 x hx : |pd3 Φ0 2 x| ≤ B2).trans (le_max_right _ _)
          have hb : |pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)| ≤ δ := by
            simpa [Fin.succ_one_eq_two] using h2_c j 1
          nlinarith [abs_nonneg (pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)), abs_nonneg (pd3 Φ0 2 x)]
        have h4 : |Φ0 x * ((3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0) -
            (3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x))| ≤
            max 0 BΦ * (3 * (max 0 Bu + 1) ^ 2 + 1 + 3 * (2 * max 0 Bu + 1) * max 0 Bg) * δ := by
          rw [abs_mul]
          have hΦx : |Φ0 x| ≤ max 0 BΦ := (by simpa [Real.norm_eq_abs] using hBΦ x hx : |Φ0 x| ≤ BΦ).trans (le_max_right _ _)
          have hup : |u_plus (proj2 x)| ≤ max 0 Bu := (by simpa [Real.norm_eq_abs] using hBu x hx : |u_plus (proj2 x)| ≤ Bu).trans (le_max_right _ _)
          have hgp : |pd2 u_plus j (proj2 x)| ≤ max 0 Bg := (by simpa [Real.norm_eq_abs] using hBg x hx : |pd2 u_plus j (proj2 x)| ≤ Bg).trans (le_max_right _ _)
          have huT : |u (x + T • e3 0)| ≤ max 0 Bu + 1 := by
            have : u (x + T • e3 0) = u_plus (proj2 x) + (u (x + T • e3 0) - u_plus (proj2 x)) := by ring
            rw [this]; exact (abs_add_le _ _).trans (by linarith)
          have hsplit : (3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0) -
              (3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x) =
              (3 * (u (x + T • e3 0)) ^ 2 - 1) * (pd3 u j.succ (x + T • e3 0) - pd2 u_plus j (proj2 x)) +
              3 * (u (x + T • e3 0) - u_plus (proj2 x)) * (u (x + T • e3 0) + u_plus (proj2 x)) * pd2 u_plus j (proj2 x) := by ring
          have ha : |(3 * (u (x + T • e3 0)) ^ 2 - 1) * (pd3 u j.succ (x + T • e3 0) - pd2 u_plus j (proj2 x))| ≤
              (3 * (max 0 Bu + 1) ^ 2 + 1) * δ := by
            rw [abs_mul]
            have hsq : |3 * (u (x + T • e3 0)) ^ 2 - 1| ≤ 3 * (max 0 Bu + 1) ^ 2 + 1 := by
              have h1 := abs_sub (3 * (u (x + T • e3 0)) ^ 2) (1 : ℝ)
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_pos one_pos, abs_pow] at h1
              have h2 : |u (x + T • e3 0)| ^ 2 ≤ (max 0 Bu + 1) ^ 2 :=
                pow_le_pow_left₀ (abs_nonneg _) huT 2
              linarith
            exact mul_le_mul hsq (hg_c j) (abs_nonneg _) (by positivity)
          have hb : |3 * (u (x + T • e3 0) - u_plus (proj2 x)) * (u (x + T • e3 0) + u_plus (proj2 x)) *
              pd2 u_plus j (proj2 x)| ≤ (3 * (2 * max 0 Bu + 1) * max 0 Bg) * δ := by
            rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
            have hsum : |u (x + T • e3 0) + u_plus (proj2 x)| ≤ 2 * max 0 Bu + 1 :=
              (abs_add_le _ _).trans (by linarith)
            have h12 : 3 * |u (x + T • e3 0) - u_plus (proj2 x)| * |u (x + T • e3 0) + u_plus (proj2 x)| ≤
                3 * δ * (2 * max 0 Bu + 1) :=
              mul_le_mul (by linarith) hsum (abs_nonneg _) (by positivity)
            calc _ ≤ (3 * δ * (2 * max 0 Bu + 1)) * max 0 Bg :=
                mul_le_mul h12 hgp (abs_nonneg _) (by positivity)
              _ = (3 * (2 * max 0 Bu + 1) * max 0 Bg) * δ := by ring
          have htot : |(3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0) -
              (3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x)| ≤
              (3 * (max 0 Bu + 1) ^ 2 + 1 + 3 * (2 * max 0 Bu + 1) * max 0 Bg) * δ := by
            rw [hsplit]; exact (abs_add_le _ _).trans (by linarith)
          calc |Φ0 x| * _ ≤ max 0 BΦ * ((3 * (max 0 Bu + 1) ^ 2 + 1 + 3 * (2 * max 0 Bu + 1) * max 0 Bg) * δ) :=
              mul_le_mul hΦx htot (abs_nonneg _) (le_max_left _ _)
            _ = _ := by ring
        have hre : F_T T x - F_lim x =
            pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x +
            (pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)) * pd3 Φ0 1 x +
            (pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)) * pd3 Φ0 2 x +
            Φ0 x * ((3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0) -
              (3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x)) := by
          dsimp [F_T, F_lim]; ring
        rw [hre]
        have ha1 := abs_add_le (pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x +
            (pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)) * pd3 Φ0 1 x +
            (pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)) * pd3 Φ0 2 x)
          (Φ0 x * ((3 * (u (x + T • e3 0)) ^ 2 - 1) * pd3 u j.succ (x + T • e3 0) -
            (3 * (u_plus (proj2 x)) ^ 2 - 1) * pd2 u_plus j (proj2 x)))
        have ha2 := abs_add_le (pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x +
            (pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)) * pd3 Φ0 1 x)
          ((pd32 u j.succ 2 (x + T • e3 0) - pd22 u_plus j 1 (proj2 x)) * pd3 Φ0 2 x)
        have ha3 := abs_add_le (pd32 u j.succ 0 (x + T • e3 0) * pd3 Φ0 0 x)
          ((pd32 u j.succ 1 (x + T • e3 0) - pd22 u_plus j 0 (proj2 x)) * pd3 Φ0 1 x)
        dsimp [B]; linarith
      · rw [Set.indicator_of_notMem hx, mul_zero]
        simp [F_T, F_lim, hpdΦ_supp 0 x hx, hpdΦ_supp 1 x hx, hpdΦ_supp 2 x hx, hΦ0_zero x hx]
    have hdiff_eq : |∫ x : Space, F_lim x| = |∫ x : Space, (F_T T x - F_lim x)| := by
      rw [integral_sub (hFT_int T) hFlim_int, hFT_zero T, zero_sub, abs_neg]
    rw [hdiff_eq]
    have hind_int : Integrable (fun x : Space => (B * δ) * (Q3 R0).indicator (fun _ => (1 : ℝ)) x) :=
      ((integrableOn_const (C := (1 : ℝ)) hvol_Q3.ne).integrable_indicator
        (isCompact_Q3 R0).measurableSet).const_mul (B * δ)
    calc |∫ x : Space, (F_T T x - F_lim x)|
        ≤ ∫ x : Space, |F_T T x - F_lim x| := abs_integral_le_integral_abs
      _ ≤ ∫ x : Space, (B * δ) * (Q3 R0).indicator (fun _ => (1 : ℝ)) x :=
          integral_mono ((hFT_int T).sub hFlim_int).abs hind_int hpt
      _ = (B * δ) * volume.real (Q3 R0) := by
          rw [integral_const_mul, integral_indicator (isCompact_Q3 R0).measurableSet,
            setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ (B * (ε / (B * V))) * V := by
          have h1 : δ ≤ ε / (B * V) := min_le_right _ _
          have h2 : volume.real (Q3 R0) ≤ V := by dsimp [V]; linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hB_pos.le) h2 (by positivity) (by positivity)
      _ = ε := by field_simp
  have hFlim_int : Integrable F_lim := by
    have hpdΦ_c (k : Fin 3) : Continuous (pd3 Φ0 k) :=
      (hΦ0_c1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hpd2_c : Continuous (pd2 u_plus j) :=
      ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hpd22_c (k : Fin 2) : Continuous (pd22 u_plus j k) :=
      (((hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    have hc : Continuous F_lim :=
      ((((hpd22_c 0).comp contDiff_proj2.continuous).mul (hpdΦ_c 1)).add
        (((hpd22_c 1).comp contDiff_proj2.continuous).mul (hpdΦ_c 2))).add
        (hΦ0_c1.continuous.mul (((continuous_const.mul ((hu_plus.continuous.comp contDiff_proj2.continuous).pow 2)).sub
          continuous_const).mul (hpd2_c.comp contDiff_proj2.continuous)))
    refine hc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Q3 R0) ?_
    intro x hx; by_contra hnot
    have h0 : Φ0 x = 0 := by by_contra hne; exact hnot (hΦ0_supp_Q (subset_tsupport Φ0 hne))
    have hd0 (k : Fin 3) : pd3 Φ0 k x = 0 := by
      have hnb : x ∉ tsupport Φ0 := fun hm => hnot (hΦ0_supp_Q hm)
      have hf : fderiv ℝ Φ0 x = 0 := by by_contra hne; exact hnb (support_fderiv_subset ℝ hne)
      simp [pd3, hf]
    exact hx (by simp [F_lim, hd0 1, hd0 2, h0])
  rw [integral_split3 hFlim_int] at hFlim_zero
  have hI_grad : Integrable (fun y : Plane2 => inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) := by
    have hv : ContDiff ℝ 1 (pd2 u_plus j) := (hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const
    have h1 : Continuous (∇ (pd2 u_plus j)) := (toDual ℝ Plane2).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
    have h2 : Continuous (∇ η) := (toDual ℝ Plane2).symm.continuous.comp (hη.continuous_fderiv one_ne_zero)
    have hs : HasCompactSupport (∇ η) := hηc.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [gradient, he])
    exact (h1.inner h2).integrable_of_hasCompactSupport
      (hs.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
  have hI_pot : Integrable (fun y : Plane2 => η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) := by
    have h1 : Continuous (pd2 u_plus j) := ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (hη.continuous.mul (((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul h1)).integrable_of_hasCompactSupport
      (hηc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
  have hinner (t : ℝ) : (∫ y : Plane2, F_lim (mk3 t y)) =
      ψ t * ((∫ y : Plane2, inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) +
        (∫ y : Plane2, η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y))) := by
    have hcongr : (fun y : Plane2 => F_lim (mk3 t y)) =
        fun y => ψ t * (inner ℝ (∇ (pd2 u_plus j) y) (∇ η y) +
          η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) := by
      ext y
      have h0 : (mk3 t y) 0 = t := by simp [mk3]
      have hp : proj2 (mk3 t y) = y := by ext k; fin_cases k <;> simp [mk3, proj2]
      have h1 := hpdi 0 (mk3 t y); simp only [Fin.succ_zero_eq_one, h0, hp] at h1
      have h2 := hpdi 1 (mk3 t y); simp only [Fin.succ_one_eq_two, h0, hp] at h2
      dsimp [F_lim, Φ0]
      rw [h1, h2, h0, hp, inner_grad2_eq, Fin.sum_univ_two]
      unfold pd22; ring
    rw [hcongr, integral_const_mul, integral_add hI_grad hI_pot]
  simp_rw [hinner] at hFlim_zero
  rw [integral_mul_const] at hFlim_zero
  have hψ_pos : 0 < ∫ t : ℝ, ψ t := lt_of_lt_of_le (by norm_num) (integral_cut1_ge (L := 2) le_rfl)
  exact (mul_eq_zero.mp hFlim_zero).resolve_left hψ_pos.ne'

private theorem sternberg_zumbrun_test {u_plus : Plane2 → ℝ} (hu_plus : ContDiff ℝ 2 u_plus)
    {C1 : ℝ} (hC1 : 0 ≤ C1) (hpd2_le : ∀ y i, |pd2 u_plus i y| ≤ C1)
    (hstab2 : ∀ φ : Plane2 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2))
    (hweak2 : ∀ (j : Fin 2) (η : Plane2 → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ y : Plane2, inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) +
        (∫ y : Plane2, η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) = 0)
    {ζ : Plane2 → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ) :
    (1 / (2 * C1 ^ 2 + 1)) * (∫ y : Plane2, K_sz u_plus y * (ζ y) ^ 2) ≤
      ∫ y : Plane2, ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2 := by
  have hpd_c1 (j : Fin 2) : ContDiff ℝ 1 (pd2 u_plus j) :=
    (hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hpd22_c (j k : Fin 2) : Continuous (pd22 u_plus j k) :=
    ((hpd_c1 j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  let g2 (y : Plane2) : ℝ := (pd2 u_plus 0 y) ^ 2 + (pd2 u_plus 1 y) ^ 2
  have hg2_eq (y : Plane2) : g2 y = ‖∇ u_plus y‖ ^ 2 := by
    rw [norm_grad2_sq, Fin.sum_univ_two]
  have hg2_c1 : ContDiff ℝ 1 g2 := ((hpd_c1 0).pow 2).add ((hpd_c1 1).pow 2)
  have hg2_le (y : Plane2) : g2 y ≤ 2 * C1 ^ 2 := by
    have h0 : (pd2 u_plus 0 y) ^ 2 ≤ C1 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpd2_le y 0) 2
    have h1 : (pd2 u_plus 1 y) ^ 2 ≤ C1 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpd2_le y 1) 2
    dsimp [g2]; linarith
  let D2sq (y : Plane2) : ℝ :=
    (pd22 u_plus 0 0 y) ^ 2 + (pd22 u_plus 0 1 y) ^ 2 +
    (pd22 u_plus 1 0 y) ^ 2 + (pd22 u_plus 1 1 y) ^ 2
  let B (y : Plane2) : ℝ :=
    (pd2 u_plus 0 y * pd22 u_plus 0 0 y + pd2 u_plus 1 y * pd22 u_plus 1 0 y) * pd2 ζ 0 y +
    (pd2 u_plus 0 y * pd22 u_plus 0 1 y + pd2 u_plus 1 y * pd22 u_plus 1 1 y) * pd2 ζ 1 y
  have hgrad_c {f : Plane2 → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (∇ f) :=
    (toDual ℝ Plane2).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)
  have hgrad_s {f : Plane2 → ℝ} (hf : HasCompactSupport f) : HasCompactSupport (∇ f) :=
    hf.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [gradient, he])
  have hpdζ_c (k : Fin 2) : Continuous (pd2 ζ k) :=
    (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpdζ_s (k : Fin 2) : HasCompactSupport (pd2 ζ k) :=
    hζc.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [pd2, he])
  have hbochner : (∫ y : Plane2,
      (D2sq y * (ζ y) ^ 2 + 2 * ζ y * B y + (3 * (u_plus y) ^ 2 - 1) * g2 y * (ζ y) ^ 2)) = 0 := by
    have hwj (j : Fin 2) :
        (∫ y : Plane2, (((pd22 u_plus j 0 y) ^ 2 + (pd22 u_plus j 1 y) ^ 2) * (ζ y) ^ 2 +
          2 * ζ y * (pd2 u_plus j y * pd22 u_plus j 0 y * pd2 ζ 0 y +
            pd2 u_plus j y * pd22 u_plus j 1 y * pd2 ζ 1 y) +
          (3 * (u_plus y) ^ 2 - 1) * (pd2 u_plus j y) ^ 2 * (ζ y) ^ 2)) = 0 := by
      let ηj (y : Plane2) : ℝ := pd2 u_plus j y * (ζ y) ^ 2
      have hηj_c1 : ContDiff ℝ 1 ηj := (hpd_c1 j).mul (hζ.pow 2)
      have hηj_s : HasCompactSupport ηj :=
        hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [ηj, h0])
      have hw := hweak2 j ηj hηj_c1 hηj_s
      have hpd_ηj (k : Fin 2) (y : Plane2) :
          pd2 ηj k y = pd22 u_plus j k y * (ζ y) ^ 2 + 2 * pd2 u_plus j y * ζ y * pd2 ζ k y := by
        have h1 : HasDerivAt (fun s : ℝ => pd2 u_plus j (y + s • e2 k)) (pd22 u_plus j k y) 0 := by
          simpa [pd22, pd2] using line_deriv2 (hpd_c1 j) y (e2 k) 0
        have h2 : HasDerivAt (fun s : ℝ => ζ (y + s • e2 k)) (pd2 ζ k y) 0 := by
          simpa [pd2] using line_deriv2 hζ y (e2 k) 0
        have h3 : HasDerivAt (fun s : ℝ => ηj (y + s • e2 k)) (pd2 ηj k y) 0 := by
          simpa [pd2] using line_deriv2 hηj_c1 y (e2 k) 0
        have h4 := h1.fun_mul (h2.fun_pow 2)
        have huq := h3.unique h4
        simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at huq
        rw [huq]; ring
      have hI1 : Integrable (fun y : Plane2 => inner ℝ (∇ (pd2 u_plus j) y) (∇ ηj y)) :=
        ((hgrad_c (hpd_c1 j)).inner (hgrad_c hηj_c1)).integrable_of_hasCompactSupport
          ((hgrad_s hηj_s).mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
      have hI2 : Integrable (fun y : Plane2 => ηj y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) :=
        (hηj_c1.continuous.mul (((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
          (hpd_c1 j).continuous)).integrable_of_hasCompactSupport
          (hηj_s.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
      rw [← integral_add hI1 hI2] at hw
      rw [← hw]
      apply integral_congr_ae; refine ae_of_all _ fun y => ?_
      dsimp only
      rw [inner_grad2_eq, Fin.sum_univ_two, hpd_ηj 0 y, hpd_ηj 1 y]
      dsimp [ηj, pd22]; ring
    have hIj (j : Fin 2) : Integrable (fun y : Plane2 =>
        ((pd22 u_plus j 0 y) ^ 2 + (pd22 u_plus j 1 y) ^ 2) * (ζ y) ^ 2 +
        2 * ζ y * (pd2 u_plus j y * pd22 u_plus j 0 y * pd2 ζ 0 y +
          pd2 u_plus j y * pd22 u_plus j 1 y * pd2 ζ 1 y) +
        (3 * (u_plus y) ^ 2 - 1) * (pd2 u_plus j y) ^ 2 * (ζ y) ^ 2) := by
      have hc : Continuous (fun y : Plane2 =>
          ((pd22 u_plus j 0 y) ^ 2 + (pd22 u_plus j 1 y) ^ 2) * (ζ y) ^ 2 +
          2 * ζ y * (pd2 u_plus j y * pd22 u_plus j 0 y * pd2 ζ 0 y +
            pd2 u_plus j y * pd22 u_plus j 1 y * pd2 ζ 1 y) +
          (3 * (u_plus y) ^ 2 - 1) * (pd2 u_plus j y) ^ 2 * (ζ y) ^ 2) :=
        ((((((hpd22_c j 0).pow 2).add ((hpd22_c j 1).pow 2)).mul (hζ.continuous.pow 2)).add
          ((continuous_const.mul hζ.continuous).mul
            ((((hpd_c1 j).continuous.mul (hpd22_c j 0)).mul (hpdζ_c 0)).add
              (((hpd_c1 j).continuous.mul (hpd22_c j 1)).mul (hpdζ_c 1))))).add
          ((((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
            ((hpd_c1 j).continuous.pow 2)).mul (hζ.continuous.pow 2)))
      exact hc.integrable_of_hasCompactSupport
        (hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
    have hsum := integral_add (hIj 0) (hIj 1)
    rw [hwj 0, hwj 1, add_zero] at hsum
    rw [← hsum]
    apply integral_congr_ae; refine ae_of_all _ fun y => ?_
    dsimp [D2sq, B, g2]; ring
  have hInt_K : Integrable (fun y : Plane2 => K_sz u_plus y * (ζ y) ^ 2) := by
    have hc : Continuous (fun y : Plane2 => K_sz u_plus y * (ζ y) ^ 2) :=
      ((((((hpd_c1 0).continuous.mul (hpd22_c 1 0)).sub ((hpd_c1 1).continuous.mul (hpd22_c 0 0))).pow 2).add
        ((((hpd_c1 0).continuous.mul (hpd22_c 1 1)).sub ((hpd_c1 1).continuous.mul (hpd22_c 0 1))).pow 2)).mul
        (hζ.continuous.pow 2))
    exact hc.integrable_of_hasCompactSupport
      (hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
  have hInt_g2ζ : Integrable (fun y : Plane2 => g2 y * ‖∇ ζ y‖ ^ 2) :=
    (hg2_c1.continuous.mul ((hgrad_c hζ).norm.pow 2)).integrable_of_hasCompactSupport
      ((hgrad_s hζc).mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
  have hInt_rem : Integrable (fun y : Plane2 => ‖∇ ζ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ζ y) ^ 2) :=
    (((hgrad_c hζ).norm.pow 2).integrable_of_hasCompactSupport
      ((hgrad_s hζc).mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))).add
      ((((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
        (hζ.continuous.pow 2)).integrable_of_hasCompactSupport
        (hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0])))
  let Crem : ℝ := ∫ y : Plane2, (‖∇ ζ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ζ y) ^ 2)
  have hstep_ε (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
      (1 / (2 * C1 ^ 2 + 1)) * (∫ y : Plane2, K_sz u_plus y * (ζ y) ^ 2) ≤
        (∫ y : Plane2, g2 y * ‖∇ ζ y‖ ^ 2) + ε ^ 2 * Crem := by
    let rε (y : Plane2) : ℝ := Real.sqrt (g2 y + ε ^ 2)
    have hpos_rad (y : Plane2) : 0 < g2 y + ε ^ 2 := by
      dsimp [g2]; positivity
    have hrε_pos (y : Plane2) : 0 < rε y := Real.sqrt_pos.mpr (hpos_rad y)
    have hrε_sq (y : Plane2) : (rε y) ^ 2 = g2 y + ε ^ 2 := Real.sq_sqrt (hpos_rad y).le
    have hrε_c1 : ContDiff ℝ 1 rε :=
      (hg2_c1.add contDiff_const).sqrt fun y => (hpos_rad y).ne'
    let φ (y : Plane2) : ℝ := rε y * ζ y
    have hφ_c1 : ContDiff ℝ 1 φ := hrε_c1.mul hζ
    have hφ_s : HasCompactSupport φ :=
      hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [φ, h0])
    have hst := hstab2 φ hφ_c1 hφ_s
    have hpd_rε (k : Fin 2) (y : Plane2) :
        pd2 rε k y = (pd2 u_plus 0 y * pd22 u_plus 0 k y + pd2 u_plus 1 y * pd22 u_plus 1 k y) / rε y := by
      have h0 : HasDerivAt (fun s : ℝ => pd2 u_plus 0 (y + s • e2 k)) (pd22 u_plus 0 k y) 0 := by
        simpa [pd22, pd2] using line_deriv2 (hpd_c1 0) y (e2 k) 0
      have h1 : HasDerivAt (fun s : ℝ => pd2 u_plus 1 (y + s • e2 k)) (pd22 u_plus 1 k y) 0 := by
        simpa [pd22, pd2] using line_deriv2 (hpd_c1 1) y (e2 k) 0
      have hg : HasDerivAt (fun s : ℝ => g2 (y + s • e2 k) + ε ^ 2)
          (2 * (pd2 u_plus 0 y * pd22 u_plus 0 k y + pd2 u_plus 1 y * pd22 u_plus 1 k y)) 0 := by
        have h := ((h0.fun_pow 2).fun_add (h1.fun_pow 2)).add_const (ε ^ 2)
        refine h.congr_deriv ?_
        simp only [zero_smul, add_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]; ring
      have hsq := (Real.hasDerivAt_sqrt (by simpa using (hpos_rad y).ne')).comp 0 hg
      have hl : HasDerivAt (fun s : ℝ => rε (y + s • e2 k)) (pd2 rε k y) 0 := by
        simpa [pd2] using line_deriv2 hrε_c1 y (e2 k) 0
      have huq := hl.unique hsq
      simp only [zero_smul, add_zero] at huq
      rw [huq]; dsimp [rε]; field_simp [(hrε_pos y).ne']
    have hpd_φ (k : Fin 2) (y : Plane2) :
        pd2 φ k y = pd2 rε k y * ζ y + rε y * pd2 ζ k y := by
      have h1 : HasDerivAt (fun s : ℝ => rε (y + s • e2 k)) (pd2 rε k y) 0 := by
        simpa [pd2] using line_deriv2 hrε_c1 y (e2 k) 0
      have h2 : HasDerivAt (fun s : ℝ => ζ (y + s • e2 k)) (pd2 ζ k y) 0 := by
        simpa [pd2] using line_deriv2 hζ y (e2 k) 0
      have h3 : HasDerivAt (fun s : ℝ => φ (y + s • e2 k)) (pd2 φ k y) 0 := by
        simpa [pd2] using line_deriv2 hφ_c1 y (e2 k) 0
      have huq := h3.unique (h1.fun_mul h2)
      simp only [zero_smul, add_zero] at huq; exact huq
    have hpt_alg (y : Plane2) :
        (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) -
          (D2sq y * (ζ y) ^ 2 + 2 * ζ y * B y + (3 * (u_plus y) ^ 2 - 1) * g2 y * (ζ y) ^ 2) ≤
        -(1 / (2 * C1 ^ 2 + 1)) * (K_sz u_plus y * (ζ y) ^ 2) +
          g2 y * ‖∇ ζ y‖ ^ 2 + ε ^ 2 * (‖∇ ζ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ζ y) ^ 2) := by
      have hdiff_grad :
          (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) -
            (D2sq y * (ζ y) ^ 2 + 2 * ζ y * B y + (3 * (u_plus y) ^ 2 - 1) * g2 y * (ζ y) ^ 2) =
          -(D2sq y - ((pd2 rε 0 y) ^ 2 + (pd2 rε 1 y) ^ 2)) * (ζ y) ^ 2 +
            g2 y * ‖∇ ζ y‖ ^ 2 + ε ^ 2 * (‖∇ ζ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ζ y) ^ 2) := by
        rw [norm_grad2_sq φ y, norm_grad2_sq ζ y, Fin.sum_univ_two, Fin.sum_univ_two,
          hpd_φ 0 y, hpd_φ 1 y]
        have hcross0 : rε y * pd2 rε 0 y =
            pd2 u_plus 0 y * pd22 u_plus 0 0 y + pd2 u_plus 1 y * pd22 u_plus 1 0 y := by
          rw [hpd_rε 0 y]; field_simp [(hrε_pos y).ne']
        have hcross1 : rε y * pd2 rε 1 y =
            pd2 u_plus 0 y * pd22 u_plus 0 1 y + pd2 u_plus 1 y * pd22 u_plus 1 1 y := by
          rw [hpd_rε 1 y]; field_simp [(hrε_pos y).ne']
        have hφsq : (φ y) ^ 2 = (g2 y + ε ^ 2) * (ζ y) ^ 2 := by
          dsimp [φ]; rw [mul_pow, hrε_sq y]
        rw [hφsq]
        have hr2 := hrε_sq y
        dsimp [B]
        linear_combination 2 * ζ y * pd2 ζ 0 y * hcross0 + 2 * ζ y * pd2 ζ 1 y * hcross1 +
          ((pd2 ζ 0 y) ^ 2 + (pd2 ζ 1 y) ^ 2) * hr2
      rw [hdiff_grad]
      have hlag : (D2sq y - ((pd2 rε 0 y) ^ 2 + (pd2 rε 1 y) ^ 2)) * (g2 y + ε ^ 2) =
          ε ^ 2 * D2sq y + K_sz u_plus y := by
        rw [hpd_rε 0 y, hpd_rε 1 y, div_pow, div_pow, hrε_sq y]
        have hne : g2 y + ε ^ 2 ≠ 0 := (hpos_rad y).ne'
        field_simp [hne]
        dsimp [D2sq, K_sz, g2]; ring
      have hK_nn : 0 ≤ K_sz u_plus y := by dsimp [K_sz]; positivity
      have hD2_nn : 0 ≤ D2sq y := by dsimp [D2sq]; positivity
      have hbound : (1 / (2 * C1 ^ 2 + 1)) * K_sz u_plus y ≤
          D2sq y - ((pd2 rε 0 y) ^ 2 + (pd2 rε 1 y) ^ 2) := by
        have hrad_le : g2 y + ε ^ 2 ≤ 2 * C1 ^ 2 + 1 := by
          have hεsq : ε ^ 2 ≤ 1 := by nlinarith
          linarith [hg2_le y]
        have h1 : K_sz u_plus y / (2 * C1 ^ 2 + 1) ≤ K_sz u_plus y / (g2 y + ε ^ 2) :=
          div_le_div_of_nonneg_left hK_nn (hpos_rad y) hrad_le
        have h2 : K_sz u_plus y / (g2 y + ε ^ 2) ≤ (ε ^ 2 * D2sq y + K_sz u_plus y) / (g2 y + ε ^ 2) :=
          div_le_div_of_nonneg_right (by nlinarith) (hpos_rad y).le
        have h3 : (ε ^ 2 * D2sq y + K_sz u_plus y) / (g2 y + ε ^ 2) =
            D2sq y - ((pd2 rε 0 y) ^ 2 + (pd2 rε 1 y) ^ 2) := by
          rw [← hlag, mul_div_cancel_right₀ _ (hpos_rad y).ne']
        have h4 : (1 / (2 * C1 ^ 2 + 1)) * K_sz u_plus y = K_sz u_plus y / (2 * C1 ^ 2 + 1) := by ring
        linarith
      have hmul := mul_le_mul_of_nonneg_right hbound (sq_nonneg (ζ y))
      linarith
    have hInt_φ : Integrable (fun y : Plane2 => ‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) :=
      (((hgrad_c hφ_c1).norm.pow 2).integrable_of_hasCompactSupport
        ((hgrad_s hφ_s).mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))).add
        ((((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
          (hφ_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hφ_s.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0])))
    have hInt_boch : Integrable (fun y : Plane2 =>
        D2sq y * (ζ y) ^ 2 + 2 * ζ y * B y + (3 * (u_plus y) ^ 2 - 1) * g2 y * (ζ y) ^ 2) := by
      have hc : Continuous (fun y : Plane2 =>
          D2sq y * (ζ y) ^ 2 + 2 * ζ y * B y + (3 * (u_plus y) ^ 2 - 1) * g2 y * (ζ y) ^ 2) :=
        ((((((hpd22_c 0 0).pow 2).add ((hpd22_c 0 1).pow 2)).add ((hpd22_c 1 0).pow 2)).add
            ((hpd22_c 1 1).pow 2)).mul (hζ.continuous.pow 2)).add
          ((continuous_const.mul hζ.continuous).mul
            ((((((hpd_c1 0).continuous.mul (hpd22_c 0 0)).add ((hpd_c1 1).continuous.mul (hpd22_c 1 0))).mul (hpdζ_c 0)).add
              ((((hpd_c1 0).continuous.mul (hpd22_c 0 1)).add ((hpd_c1 1).continuous.mul (hpd22_c 1 1))).mul (hpdζ_c 1)))))
          |>.add ((((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
            hg2_c1.continuous).mul (hζ.continuous.pow 2))
      exact hc.integrable_of_hasCompactSupport
        (hζc.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
    have hInt_rhs1 : Integrable (fun y : Plane2 => -(1 / (2 * C1 ^ 2 + 1)) * (K_sz u_plus y * (ζ y) ^ 2) +
        g2 y * ‖∇ ζ y‖ ^ 2) := (hInt_K.const_mul (-(1 / (2 * C1 ^ 2 + 1)))).add hInt_g2ζ
    have hInt_rhs : Integrable (fun y : Plane2 =>
        -(1 / (2 * C1 ^ 2 + 1)) * (K_sz u_plus y * (ζ y) ^ 2) + g2 y * ‖∇ ζ y‖ ^ 2 +
        ε ^ 2 * (‖∇ ζ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (ζ y) ^ 2)) :=
      hInt_rhs1.add (hInt_rem.const_mul (ε ^ 2))
    have hmono := integral_mono (hInt_φ.sub hInt_boch) hInt_rhs hpt_alg
    simp only [Pi.sub_apply] at hmono
    rw [integral_sub hInt_φ hInt_boch, hbochner, sub_zero,
      integral_add hInt_rhs1 (hInt_rem.const_mul _),
      integral_add (hInt_K.const_mul _) hInt_g2ζ,
      integral_const_mul, integral_const_mul] at hmono
    dsimp [Crem]
    linarith
  have hres : (1 / (2 * C1 ^ 2 + 1)) * (∫ y : Plane2, K_sz u_plus y * (ζ y) ^ 2) ≤
      ∫ y : Plane2, g2 y * ‖∇ ζ y‖ ^ 2 := by
    by_contra! hgt
    let δ := (1 / (2 * C1 ^ 2 + 1)) * (∫ y : Plane2, K_sz u_plus y * (ζ y) ^ 2) -
      ∫ y : Plane2, g2 y * ‖∇ ζ y‖ ^ 2
    let ε := min 1 (Real.sqrt (δ / (2 * (|Crem| + 1))))
    have hε0 : 0 < ε := lt_min one_pos (Real.sqrt_pos.mpr (by dsimp [δ]; positivity))
    have hε1 : ε ≤ 1 := min_le_left _ _
    have hstep := hstep_ε ε hε0 hε1
    have hε_sq : ε ^ 2 ≤ δ / (2 * (|Crem| + 1)) := by
      have h1 : ε ≤ Real.sqrt (δ / (2 * (|Crem| + 1))) := min_le_right _ _
      calc ε ^ 2 ≤ (Real.sqrt (δ / (2 * (|Crem| + 1)))) ^ 2 := pow_le_pow_left₀ hε0.le h1 2
        _ = δ / (2 * (|Crem| + 1)) := Real.sq_sqrt (by dsimp [δ]; positivity)
    have hCrem_b : ε ^ 2 * Crem ≤ δ / 2 := by
      calc ε ^ 2 * Crem ≤ ε ^ 2 * |Crem| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ (δ / (2 * (|Crem| + 1))) * (|Crem| + 1) :=
            mul_le_mul hε_sq (by linarith) (abs_nonneg _) (by dsimp [δ]; positivity)
        _ = δ / 2 := by field_simp
    dsimp [δ] at hCrem_b
    linarith
  refine hres.trans_eq (integral_congr_ae (ae_of_all _ fun y => ?_))
  dsimp only; rw [hg2_eq y]

theorem sternberg_zumbrun_zero {u_plus : Plane2 → ℝ} (hu_plus : ContDiff ℝ 2 u_plus)
    {C1 : ℝ} (hC1 : 0 ≤ C1) (hpd2_le : ∀ y i, |pd2 u_plus i y| ≤ C1)
    (hstab2 : ∀ φ : Plane2 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2))
    (hweak2 : ∀ (j : Fin 2) (η : Plane2 → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ y : Plane2, inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) +
        (∫ y : Plane2, η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) = 0) :
    ∀ y : Plane2, K_sz u_plus y = 0 := by
  have hshell_bound (N : ℕ) :
      (∫ y in Q2 ((2 : ℝ) ^ N), (1 : ℝ) / (‖y‖ ^ 2 + 1)) ≤ 4 + 16 * (N : ℝ) := by
    have hf_cont : Continuous (fun y : Plane2 => (1 : ℝ) / (‖y‖ ^ 2 + 1)) :=
      continuous_const.div ((continuous_norm.pow 2).add continuous_const) fun y => by positivity
    induction N with
    | zero =>
      simp only [pow_zero, Nat.cast_zero, mul_zero, add_zero]
      have hfin : volume (Q2 1) ≠ ⊤ := by rw [volume_Q2 zero_le_one]; exact ENNReal.ofReal_ne_top
      have hcomp : IsCompact (Q2 1) := by
        have h1 : Q2 1 = (EuclideanSpace.equiv (Fin 2) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 2 => Icc (-1) 1) := by
          ext y; constructor
          · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
          · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
        rw [h1]
        exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
      have hmono := setIntegral_mono_on (hf_cont.continuousOn.integrableOn_compact hcomp)
        (integrableOn_const (C := (1 : ℝ)) hfin) (measurableSet_Q2 1)
        (fun y _ => (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg ‖y‖]))
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, volume_Q2 zero_le_one,
        ENNReal.toReal_ofReal (by norm_num)] at hmono
      linarith
    | succ k ih =>
      have hsub : Q2 ((2 : ℝ) ^ k) ⊆ Q2 ((2 : ℝ) ^ (k + 1)) := by
        intro y hy i
        have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by rw [pow_succ]; linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
        exact ⟨by linarith [(hy i).1], by linarith [(hy i).2]⟩
      have hcomp_next : IsCompact (Q2 ((2 : ℝ) ^ (k + 1))) := by
        have h1 : Q2 ((2 : ℝ) ^ (k + 1)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
            Set.pi Set.univ (fun _ : Fin 2 => Icc (-((2 : ℝ) ^ (k + 1))) ((2 : ℝ) ^ (k + 1))) := by
          ext y; constructor
          · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
          · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
        rw [h1]
        exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
      have hint_next : IntegrableOn (fun y : Plane2 => (1 : ℝ) / (‖y‖ ^ 2 + 1)) (Q2 ((2 : ℝ) ^ (k + 1))) volume :=
        hf_cont.continuousOn.integrableOn_compact hcomp_next
      have hunion : Q2 ((2 : ℝ) ^ k) ∪ (Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) = Q2 ((2 : ℝ) ^ (k + 1)) :=
        union_sdiff_cancel hsub
      have hsplit : (∫ y in Q2 ((2 : ℝ) ^ (k + 1)), (1 : ℝ) / (‖y‖ ^ 2 + 1)) =
          (∫ y in Q2 ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1)) +
          (∫ y in Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1)) := by
        conv_lhs => rw [← hunion]
        exact setIntegral_union disjoint_sdiff_self_right
          ((measurableSet_Q2 _).diff (measurableSet_Q2 _))
          (hint_next.mono_set hsub) (hint_next.mono_set sdiff_subset)
      have hshell : (∫ y in Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k), (1 : ℝ) / (‖y‖ ^ 2 + 1)) ≤ 16 := by
        have hfin : volume (Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) ≠ ⊤ :=
          ((measure_mono sdiff_subset).trans_lt (by rw [volume_Q2 (by positivity)]; exact ENNReal.ofReal_lt_top)).ne
        have hpt (y : Plane2) (hy : y ∈ Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) :
            (1 : ℝ) / (‖y‖ ^ 2 + 1) ≤ 1 / ((2 : ℝ) ^ k) ^ 2 := by
          have hnot : ¬(∀ i : Fin 2, y i ∈ Icc (-((2 : ℝ) ^ k)) ((2 : ℝ) ^ k)) := hy.2
          push Not at hnot
          obtain ⟨i, hi⟩ := hnot
          have hgt : (2 : ℝ) ^ k < |y i| := by
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
            rcases hi with h1 | h2
            · rw [abs_of_neg (by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) k])]; linarith
            · rw [abs_of_pos (by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) k])]; linarith
          have hnorm : (2 : ℝ) ^ k ≤ ‖y‖ := by
            have := PiLp.norm_apply_le y i; rw [Real.norm_eq_abs] at this; linarith
          have hsq : ((2 : ℝ) ^ k) ^ 2 ≤ ‖y‖ ^ 2 + 1 := by
            have := pow_le_pow_left₀ (by positivity) hnorm 2; linarith
          exact div_le_div_of_nonneg_left zero_le_one (by positivity) hsq
        have hmono := setIntegral_mono_on (hint_next.mono_set sdiff_subset)
          (integrableOn_const (C := (1 : ℝ) / ((2 : ℝ) ^ k) ^ 2) hfin)
          ((measurableSet_Q2 _).diff (measurableSet_Q2 _)) hpt
        rw [setIntegral_const, smul_eq_mul] at hmono
        have hvol_le : volume.real (Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) ≤ (2 * (2 : ℝ) ^ (k + 1)) ^ 2 := by
          have hm : volume (Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) ≤ volume (Q2 ((2 : ℝ) ^ (k + 1))) :=
            measure_mono sdiff_subset
          rw [volume_Q2 (by positivity)] at hm
          have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hm
          rw [ENNReal.toReal_ofReal (by positivity)] at hto
          exact hto
        calc _ ≤ volume.real (Q2 ((2 : ℝ) ^ (k + 1)) \ Q2 ((2 : ℝ) ^ k)) * (1 / ((2 : ℝ) ^ k) ^ 2) := hmono
          _ ≤ (2 * (2 : ℝ) ^ (k + 1)) ^ 2 * (1 / ((2 : ℝ) ^ k) ^ 2) :=
              mul_le_mul_of_nonneg_right hvol_le (by positivity)
          _ = 16 := by
              rw [pow_succ]; have hne : ((2 : ℝ) ^ k) ^ 2 ≠ 0 := by positivity
              field_simp [hne]; ring
      push_cast; linarith
  have hball_zero (R0 : ℝ) (hR0 : 1 ≤ R0) : (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) = 0 := by
    have hK_c : Continuous (K_sz u_plus) := by
      have h1 (i : Fin 2) : Continuous (pd2 u_plus i) :=
        ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
      have h2 (i j : Fin 2) : Continuous (pd22 u_plus i j) :=
        (((hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
          one_ne_zero).clm_apply continuous_const
      unfold K_sz
      exact ((((h1 0).mul (h2 1 0)).sub ((h1 1).mul (h2 0 0))).pow 2).add
        ((((h1 0).mul (h2 1 1)).sub ((h1 1).mul (h2 0 1))).pow 2)
    have hK_nn (y : Plane2) : 0 ≤ K_sz u_plus y := by unfold K_sz; positivity
    have hge0 : 0 ≤ ∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y :=
      setIntegral_nonneg measurableSet_closedBall fun y _ => hK_nn y
    suffices hle0 : (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) ≤ 0 by linarith
    let cLog : ℝ := Real.log 2
    have hcLog : 0 < cLog := Real.log_pos one_lt_two
    have hbound_m (m : ℕ) (hm1 : 1 ≤ m) (hmR : R0 ≤ (2 : ℝ) ^ m) :
        (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) ≤
          (2 * C1 ^ 2 + 1) * (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ)) := by
      let R : ℝ := (2 : ℝ) ^ m
      have hR_ge2 : 2 ≤ R := by
        dsimp [R]
        have : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ m := pow_le_pow_right₀ one_le_two hm1
        simpa using this
      let Lm : ℝ := Real.log (R ^ 2 + 1)
      have hLm_ge : 2 * (m : ℝ) * cLog ≤ Lm := by
        have h1 : (2 : ℝ) ^ (2 * m) ≤ R ^ 2 + 1 := by
          dsimp [R]; rw [pow_mul']; linarith
        have h2 := Real.log_le_log (by positivity) h1
        rw [Real.log_pow] at h2
        push_cast at h2; dsimp [Lm, cLog]; linarith
      have hLm_pos : 0 < Lm := lt_of_lt_of_le (by positivity) hLm_ge
      let rad (y : Plane2) : ℝ := (y 0) ^ 2 + (y 1) ^ 2 + 1
      have hrad_eq (y : Plane2) : rad y = ‖y‖ ^ 2 + 1 := by
        have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
          simp only [Real.norm_eq_abs, sq_abs]
        dsimp [rad]; linarith
      have hrad_c1 : ContDiff ℝ 1 rad :=
        (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.pow 2).add
          ((EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.pow 2)).add contDiff_const
      let ζ (y : Plane2) : ℝ := hermite (2 - Real.log (rad y) / Lm)
      have hζ_c1 : ContDiff ℝ 1 ζ :=
        contDiff_hermite.comp (contDiff_const.sub
          ((hrad_c1.log fun y => by dsimp [rad]; positivity).div_const Lm))
      have hζ_supp_Q : ∀ y ∉ Q2 ((2 : ℝ) ^ (2 * m + 1)), ζ y = 0 ∧ ‖∇ ζ y‖ ^ 2 = 0 := by
        intro y hy
        have hnot : ¬(∀ i : Fin 2, y i ∈ Icc (-((2 : ℝ) ^ (2 * m + 1))) ((2 : ℝ) ^ (2 * m + 1))) := hy
        push Not at hnot
        obtain ⟨i, hi⟩ := hnot
        have hgt : (2 : ℝ) ^ (2 * m + 1) < |y i| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
          rcases hi with h1 | h2
          · rw [abs_of_neg (by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * m + 1)])]; linarith
          · rw [abs_of_pos (by linarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * m + 1)])]; linarith
        have h2R : R ^ 2 + 1 < (2 : ℝ) ^ (2 * m + 1) := by
          have hpow : (2 : ℝ) ^ (2 * m + 1) = 2 * R ^ 2 := by
            dsimp [R]; rw [pow_succ, pow_mul']; ring
          nlinarith
        have hnorm : R ^ 2 + 1 < ‖y‖ := by
          have := PiLp.norm_apply_le y i; rw [Real.norm_eq_abs] at this; linarith
        have hrad_gt : (R ^ 2 + 1) ^ 2 < rad y := by
          rw [hrad_eq]; nlinarith
        have hlog_gt : 2 < Real.log (rad y) / Lm := by
          rw [lt_div_iff₀ hLm_pos]
          have := Real.log_lt_log (by positivity) hrad_gt
          rw [Real.log_pow] at this; norm_num at this; dsimp [Lm]; linarith
        have hζ0 : ζ y = 0 := hermite_zero_of_le (by linarith)
        have hev : ζ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
          have hopen : ∀ᶠ z in 𝓝 y, (R ^ 2 + 1) ^ 2 < rad z :=
            (continuousAt_const (y := (R ^ 2 + 1) ^ 2)).eventually_lt hrad_c1.continuous.continuousAt hrad_gt
          filter_upwards [hopen] with z hz
          have hlg : 2 < Real.log (rad z) / Lm := by
            rw [lt_div_iff₀ hLm_pos]
            have := Real.log_lt_log (by positivity) hz
            rw [Real.log_pow] at this; norm_num at this; dsimp [Lm]; linarith
          exact hermite_zero_of_le (by linarith)
        have hfd0 : fderiv ℝ ζ y = 0 := by
          rw [hev.fderiv_eq, fderiv_const_apply]
        exact ⟨hζ0, by simp [gradient, hfd0]⟩
      have hζ_c : HasCompactSupport ζ := by
        have hcomp : IsCompact (Q2 ((2 : ℝ) ^ (2 * m + 1))) := by
          have h1 : Q2 ((2 : ℝ) ^ (2 * m + 1)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
              Set.pi Set.univ (fun _ : Fin 2 => Icc (-((2 : ℝ) ^ (2 * m + 1))) ((2 : ℝ) ^ (2 * m + 1))) := by
            ext y; constructor
            · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
            · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
          rw [h1]
          exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
        refine HasCompactSupport.of_support_subset_isCompact hcomp ?_
        intro y hy; by_contra hnot; exact hy (hζ_supp_Q y hnot).1
      have hgradζ_le (y : Plane2) : ‖∇ ζ y‖ ^ 2 ≤ 9 / (Lm ^ 2 * (‖y‖ ^ 2 + 1)) := by
        have hpd (k : Fin 2) : pd2 ζ k y =
            hermite' (2 - Real.log (rad y) / Lm) * (-(2 * y k) / (rad y * Lm)) := by
          have hrad_d : HasDerivAt (fun s : ℝ => rad (y + s • e2 k)) (2 * y k) 0 := by
            have h0 : HasDerivAt (fun s : ℝ => (y + s • e2 k) 0) (if k = 0 then 1 else 0) 0 := by
              have : (fun s : ℝ => (y + s • e2 k) 0) = fun s => y 0 + (if k = 0 then s else 0) := by
                ext s; fin_cases k <;> simp [e2]
              rw [this]; fin_cases k
              · simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 0)
              · simpa using hasDerivAt_const (0 : ℝ) (y 0)
            have h1 : HasDerivAt (fun s : ℝ => (y + s • e2 k) 1) (if k = 1 then 1 else 0) 0 := by
              have : (fun s : ℝ => (y + s • e2 k) 1) = fun s => y 1 + (if k = 1 then s else 0) := by
                ext s; fin_cases k <;> simp [e2]
              rw [this]; fin_cases k
              · simpa using hasDerivAt_const (0 : ℝ) (y 1)
              · simpa using (hasDerivAt_id (0 : ℝ)).const_add (y 1)
            have h := ((h0.fun_pow 2).fun_add (h1.fun_pow 2)).add_const (1 : ℝ)
            refine h.congr_deriv ?_
            fin_cases k <;> simp [e2]
          have hlog_d : HasDerivAt (fun s : ℝ => 2 - Real.log (rad (y + s • e2 k)) / Lm)
              (-(2 * y k) / (rad y * Lm)) 0 := by
            have h1 := ((hrad_d.log (by simp only [zero_smul, add_zero]; dsimp [rad]; positivity)).div_const Lm)
            have h2 := (hasDerivAt_const (0 : ℝ) (2 : ℝ)).fun_sub h1
            refine h2.congr_deriv ?_
            simp only [zero_smul, add_zero]
            have hrne : rad y ≠ 0 := by dsimp [rad]; positivity
            field_simp [hrne, hLm_pos.ne']; ring
          have hh_at : HasDerivAt hermite (hermite' (2 - Real.log (rad y) / Lm))
              (2 - Real.log (rad (y + (0 : ℝ) • e2 k)) / Lm) := by
            simpa only [zero_smul, add_zero] using hasDerivAt_hermite (2 - Real.log (rad y) / Lm)
          have hcomp := hh_at.comp (0 : ℝ) hlog_d
          have hl : HasDerivAt (fun s : ℝ => ζ (y + s • e2 k)) (pd2 ζ k y) 0 := by
            simpa [pd2] using line_deriv2 hζ_c1 y (e2 k) 0
          exact hl.unique hcomp
        rw [norm_grad2_sq, Fin.sum_univ_two, hpd 0, hpd 1]
        have hh' : (hermite' (2 - Real.log (rad y) / Lm)) ^ 2 ≤ 9 / 4 := by
          rw [← sq_abs]
          have := hermite'_abs_le (2 - Real.log (rad y) / Lm)
          nlinarith [abs_nonneg (hermite' (2 - Real.log (rad y) / Lm))]
        have halg : (hermite' (2 - Real.log (rad y) / Lm) * (-(2 * y 0) / (rad y * Lm))) ^ 2 +
            (hermite' (2 - Real.log (rad y) / Lm) * (-(2 * y 1) / (rad y * Lm))) ^ 2 =
            (hermite' (2 - Real.log (rad y) / Lm)) ^ 2 *
              (4 * ((y 0) ^ 2 + (y 1) ^ 2) / (rad y ^ 2 * Lm ^ 2)) := by ring
        rw [halg, ← hrad_eq y]
        have hnum : (y 0) ^ 2 + (y 1) ^ 2 ≤ rad y := by dsimp [rad]; linarith
        have hfrac : 4 * ((y 0) ^ 2 + (y 1) ^ 2) / (rad y ^ 2 * Lm ^ 2) ≤ 4 / (Lm ^ 2 * rad y) := by
          have hrp : 0 < rad y := by dsimp [rad]; positivity
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_pos_of_pos hLm_pos]
        calc _ ≤ (9 / 4) * (4 / (Lm ^ 2 * rad y)) :=
            mul_le_mul hh' hfrac (by positivity) (by norm_num)
          _ = 9 / (Lm ^ 2 * rad y) := by ring
      have hsz := sternberg_zumbrun_test hu_plus hC1 hpd2_le hstab2 hweak2 hζ_c1 hζ_c
      have hKζ_int : Integrable (fun y : Plane2 => K_sz u_plus y * (ζ y) ^ 2) :=
        (hK_c.mul (hζ_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hζ_c.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))
      have hlhs : (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) ≤
          ∫ y : Plane2, K_sz u_plus y * (ζ y) ^ 2 := by
        have h1 : (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) =
            ∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y * (ζ y) ^ 2 := by
          apply setIntegral_congr_fun measurableSet_closedBall
          intro y hy
          rw [mem_closedBall, dist_zero_right] at hy
          have hleR : ‖y‖ ≤ R := hy.trans hmR
          have hrad_le : rad y ≤ R ^ 2 + 1 := by
            rw [hrad_eq]; nlinarith [norm_nonneg y]
          have hlog_le : Real.log (rad y) / Lm ≤ 1 :=
            (div_le_one hLm_pos).mpr (Real.log_le_log (by dsimp [rad]; positivity) hrad_le)
          dsimp only
          rw [show ζ y = 1 from hermite_one_of_ge (by linarith), one_pow, mul_one]
        rw [h1]
        exact setIntegral_le_integral hKζ_int (ae_of_all _ fun y => mul_nonneg (hK_nn y) (sq_nonneg _))
      have hgrad_cont : Continuous (∇ ζ) := (toDual ℝ Plane2).symm.continuous.comp (hζ_c1.continuous_fderiv one_ne_zero)
      have hgrad_supp : HasCompactSupport (∇ ζ) :=
        hζ_c.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [gradient, he])
      have hgrad_u_cont : Continuous (∇ u_plus) :=
        (toDual ℝ Plane2).symm.continuous.comp ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero)
      have hRHS_int : Integrable (fun y : Plane2 => ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2) :=
        ((hgrad_u_cont.norm.pow 2).mul (hgrad_cont.norm.pow 2)).integrable_of_hasCompactSupport
          ((hgrad_supp.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0])).mul_left)
      have hRHS_eq : (∫ y : Plane2, ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2) =
          ∫ y in Q2 ((2 : ℝ) ^ (2 * m + 1)), ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2 := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro y hy; rw [(hζ_supp_Q y hy).2, mul_zero]
      have hf_cont : Continuous (fun y : Plane2 => (1 : ℝ) / (‖y‖ ^ 2 + 1)) :=
        continuous_const.div ((continuous_norm.pow 2).add continuous_const) fun y => by positivity
      have hcomp_Q : IsCompact (Q2 ((2 : ℝ) ^ (2 * m + 1))) := by
        have h1 : Q2 ((2 : ℝ) ^ (2 * m + 1)) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
            Set.pi Set.univ (fun _ : Fin 2 => Icc (-((2 : ℝ) ^ (2 * m + 1))) ((2 : ℝ) ^ (2 * m + 1))) := by
          ext y; constructor
          · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
          · rintro ⟨f, hf, rfl⟩ i; simpa using hf i (Set.mem_univ i)
        rw [h1]
        exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
      have hRHS_le : (∫ y : Plane2, ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2) ≤
          (18 * C1 ^ 2 / Lm ^ 2) * (4 + 16 * ((2 * m + 1 : ℕ) : ℝ)) := by
        rw [hRHS_eq]
        have hmono := setIntegral_mono_on hRHS_int.integrableOn
          ((hf_cont.continuousOn.integrableOn_compact hcomp_Q).const_mul (18 * C1 ^ 2 / Lm ^ 2))
          (measurableSet_Q2 _) (fun y _ => by
            have hu_sq : ‖∇ u_plus y‖ ^ 2 ≤ 2 * C1 ^ 2 := by
              rw [norm_grad2_sq, Fin.sum_univ_two]
              have h0 : (pd2 u_plus 0 y) ^ 2 ≤ C1 ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpd2_le y 0) 2
              have h1 : (pd2 u_plus 1 y) ^ 2 ≤ C1 ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hpd2_le y 1) 2
              linarith
            calc ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2
                ≤ (2 * C1 ^ 2) * (9 / (Lm ^ 2 * (‖y‖ ^ 2 + 1))) :=
                  mul_le_mul hu_sq (hgradζ_le y) (sq_nonneg _) (by positivity)
              _ = (18 * C1 ^ 2 / Lm ^ 2) * (1 / (‖y‖ ^ 2 + 1)) := by
                  have hne1 : Lm ^ 2 ≠ 0 := by positivity
                  have hne2 : (‖y‖ ^ 2 + 1 : ℝ) ≠ 0 := by positivity
                  field_simp [hne1, hne2]
                  ring)
        rw [integral_const_mul] at hmono
        exact hmono.trans (mul_le_mul_of_nonneg_left (hshell_bound (2 * m + 1)) (by positivity))
      have h4_16 : (4 : ℝ) + 16 * ((2 * m + 1 : ℕ) : ℝ) ≤ 52 * (m : ℝ) := by
        have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
        push_cast; linarith
      have hLm_sq : 4 * cLog ^ 2 * (m : ℝ) ^ 2 ≤ Lm ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hLm_ge 2
        linarith
      have hRHS_final : (∫ y : Plane2, ‖∇ u_plus y‖ ^ 2 * ‖∇ ζ y‖ ^ 2) ≤
          (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ)) := by
        have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1)
        calc _ ≤ (18 * C1 ^ 2 / Lm ^ 2) * (52 * (m : ℝ)) :=
              hRHS_le.trans (mul_le_mul_of_nonneg_left h4_16 (by positivity))
          _ ≤ (18 * C1 ^ 2 / (4 * cLog ^ 2 * (m : ℝ) ^ 2)) * (52 * (m : ℝ)) :=
              mul_le_mul_of_nonneg_right
                (div_le_div_of_nonneg_left (by positivity) (by positivity) hLm_sq) (by positivity)
          _ = (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ)) := by field_simp
      have hmul := mul_le_mul_of_nonneg_left hlhs (by positivity : 0 ≤ 1 / (2 * C1 ^ 2 + 1))
      have hcomb : (1 / (2 * C1 ^ 2 + 1)) * (∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y) ≤
          (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ)) := hmul.trans (hsz.trans hRHS_final)
      have h2C : 0 < 2 * C1 ^ 2 + 1 := by positivity
      have hcomb2 := mul_le_mul_of_nonneg_left hcomb h2C.le
      rw [← mul_assoc, mul_one_div_cancel h2C.ne', one_mul] at hcomb2
      have heq_r : (2 * C1 ^ 2 + 1) * ((18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ))) =
          (2 * C1 ^ 2 + 1) * (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m : ℝ)) := by ring
      linarith
    by_contra! hpos_I
    let I0 := ∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y
    let M := (2 * C1 ^ 2 + 1) * (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2)
    obtain ⟨m0, hm0⟩ := exists_nat_gt (max (max 1 R0) (M / I0))
    have hm1 : 1 ≤ m0 := by
      have : (1 : ℝ) < (m0 : ℝ) := lt_of_le_of_lt (le_trans (le_max_left 1 R0) (le_max_left _ _)) hm0
      exact_mod_cast this.le
    have hmR : R0 ≤ (2 : ℝ) ^ m0 := by
      have h1 : R0 ≤ (m0 : ℝ) := (le_trans (le_max_right 1 R0) (le_max_left _ _)).trans hm0.le
      have h2 : (m0 : ℝ) ≤ (2 : ℝ) ^ m0 := by exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self (n := m0))
      exact h1.trans h2
    have hbm := hbound_m m0 hm1 hmR
    have hM_lt : M / (m0 : ℝ) < I0 := by
      have hm_pos : (0 : ℝ) < (m0 : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hm1)
      rw [div_lt_iff₀ hm_pos]
      have h1 : M / I0 < (m0 : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm0
      have h2 := (div_lt_iff₀ hpos_I).mp h1
      linarith
    have heqM : (2 * C1 ^ 2 + 1) * (18 * C1 ^ 2 * 52) / (4 * cLog ^ 2 * (m0 : ℝ)) = M / (m0 : ℝ) := by
      dsimp [M]; ring
    linarith
  intro y0
  have hK_c : Continuous (K_sz u_plus) := by
    have h1 (i : Fin 2) : Continuous (pd2 u_plus i) :=
      ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have h2 (i j : Fin 2) : Continuous (pd22 u_plus i j) :=
      (((hu_plus.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv
        one_ne_zero).clm_apply continuous_const
    unfold K_sz
    exact ((((h1 0).mul (h2 1 0)).sub ((h1 1).mul (h2 0 0))).pow 2).add
      ((((h1 0).mul (h2 1 1)).sub ((h1 1).mul (h2 0 1))).pow 2)
  have hK_nn (y : Plane2) : 0 ≤ K_sz u_plus y := by unfold K_sz; positivity
  by_contra hne
  have hpos_y : 0 < K_sz u_plus y0 := lt_of_le_of_ne (hK_nn y0) (Ne.symm hne)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hK_c.continuousAt (K_sz u_plus y0 / 2) (half_pos hpos_y)
  let r : ℝ := min 1 (δ / 2)
  have hr : 0 < r := lt_min one_pos (half_pos hδ)
  let R0 : ℝ := ‖y0‖ + 2
  have hsub : ball y0 r ⊆ closedBall (0 : Plane2) R0 := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖y - y0‖ < r := by simpa [dist_eq_norm] using hy
    have h2 : ‖y‖ ≤ ‖y - y0‖ + ‖y0‖ := by
      have : y = (y - y0) + y0 := by abel
      conv_lhs => rw [this]
      exact norm_add_le _ _
    have h3 : r ≤ 1 := min_le_left _ _
    dsimp [R0]; linarith
  have hI0 := hball_zero R0 (by dsimp [R0]; linarith [norm_nonneg y0])
  have hint_B : IntegrableOn (K_sz u_plus) (closedBall (0 : Plane2) R0) volume :=
    hK_c.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hmono1 : (∫ y in ball y0 r, K_sz u_plus y) ≤ ∫ y in closedBall (0 : Plane2) R0, K_sz u_plus y :=
    setIntegral_mono_set hint_B (ae_of_all _ hK_nn) (Eventually.of_forall hsub)
  have hfin_b : volume (ball y0 r) ≠ ⊤ := measure_ball_lt_top.ne
  have hmono2 : (∫ _y in ball y0 r, K_sz u_plus y0 / 2) ≤ ∫ y in ball y0 r, K_sz u_plus y :=
    setIntegral_mono_on (integrableOn_const (C := K_sz u_plus y0 / 2) hfin_b)
      (hint_B.mono_set hsub) measurableSet_ball (fun y hy => by
        have hd : dist y y0 < δ := lt_of_lt_of_le hy (le_trans (min_le_right _ _) (half_lt_self hδ).le)
        have hc := hclose hd; rw [Real.dist_eq, abs_lt] at hc; linarith)
  rw [setIntegral_const, smul_eq_mul] at hmono2
  have hvol_pos : 0 < volume.real (ball y0 r) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume y0 hr).ne' hfin_b
  have hprod_pos : 0 < volume.real (ball y0 r) * (K_sz u_plus y0 / 2) := by positivity
  linarith

end Mod4a

namespace Mod4b
open InnerProductSpace MeasureTheory Filter Set Metric
open scoped Topology Laplacian Gradient
private theorem hasDerivAt_mk2_0 {f : Plane2 → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    HasDerivAt (fun r : ℝ => f (mk2 r t)) (pd2 f 0 (mk2 s t)) s := by
  have h := line_deriv2 hf (mk2 0 t) (e2 0) s
  have heq : (fun r : ℝ => f (mk2 0 t + r • e2 0)) = fun r => f (mk2 r t) := by
    ext r; rw [mk2_add_e0, zero_add]
  rw [heq, mk2_add_e0, zero_add] at h
  exact h

private theorem hasDerivAt_mk2_1 {f : Plane2 → ℝ} (hf : ContDiff ℝ 1 f) (s t : ℝ) :
    HasDerivAt (fun r : ℝ => f (mk2 s r)) (pd2 f 1 (mk2 s t)) t := by
  have h := line_deriv2 hf (mk2 s 0) (e2 1) t
  have heq : (fun r : ℝ => f (mk2 s 0 + r • e2 1)) = fun r => f (mk2 s r) := by
    ext r; rw [mk2_add_e1, zero_add]
  rw [heq, mk2_add_e1, zero_add] at h
  exact h

private theorem partial_comm2 {f : Plane2 → ℝ} (hf : ContDiff ℝ 2 f) (y : Plane2) (i j : Fin 2) :
    pd22 f i j y = pd22 f j i y := by
  have hF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd (a b : Fin 2) : pd22 f a b y = (fderiv ℝ (fderiv ℝ f) y (e2 b)) (e2 a) := by
    unfold pd22 pd2
    rw [fderiv_clm_apply (hF.differentiable one_ne_zero y) (differentiableAt_const (e2 a))]
    simp
  rw [hd i j, hd j i]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (e2 j) (e2 i)

private theorem laplacian_sum2 {f : Plane2 → ℝ} (hf : ContDiff ℝ 2 f) (y : Plane2) :
    (Δ f) y = pd22 f 0 0 y + pd22 f 1 1 y := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  dsimp only
  rw [Fin.sum_univ_two]
  have ht (i : Fin 2) : iteratedFDeriv ℝ 2 f y ![b i, b i] = pd22 f i i y := by
    have hb : b i = e2 i := by ext j; simp [b, e2, EuclideanSpace.basisFun_apply]
    have hF : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    rw [iteratedFDeriv_two_apply, hb]
    unfold pd22 pd2
    rw [fderiv_clm_apply (hF.differentiable one_ne_zero y) (differentiableAt_const (e2 i))]
    simp
  rw [ht 0, ht 1]

private theorem integral_split2 {f : Plane2 → ℝ} (hf : Integrable f) :
    (∫ q : Plane2, f q) = ∫ t : ℝ, ∫ s : ℝ, f (mk2 s t) := by
  let e1 : Plane2 ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
  let e2m : (Fin 2 → ℝ) ≃ᵐ ℝ × (Fin 1 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 1
  let e3m : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let e : Plane2 ≃ᵐ ℝ × ℝ := (e1.trans e2m).trans ((MeasurableEquiv.refl ℝ).prodCongr e3m)
  have hmp : MeasurePreserving e volume volume :=
    ((PiLp.volume_preserving_ofLp (Fin 2)).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 1)).trans
      ((MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ))
  have he_symm (p : ℝ × ℝ) : e.symm p = mk2 p.2 p.1 := by
    ext k; fin_cases k <;> rfl
  have hint : Integrable (fun p : ℝ × ℝ => f (mk2 p.2 p.1)) := by
    have h1 := (hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
    exact h1.congr (ae_of_all _ fun p => by simp [he_symm])
  rw [← hmp.symm.integral_comp e.symm.measurableEmbedding]
  have heq : (fun p : ℝ × ℝ => f (e.symm p)) = fun p => f (mk2 p.2 p.1) := funext fun p => by rw [he_symm]
  rw [heq, Measure.volume_eq_prod, integral_prod _ hint]

private theorem setIntegral_Q2_split {R : ℝ} (hR : 0 ≤ R) {f : Plane2 → ℝ} (hf : Continuous f) :
    (∫ q in Q2 R, f q) = ∫ t in Icc (-R) R, ∫ s in Icc (-R) R, f (mk2 s t) := by
  let e1 : Plane2 ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
  let e2m : (Fin 2 → ℝ) ≃ᵐ ℝ × (Fin 1 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 1
  let e3m : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
  let e : Plane2 ≃ᵐ ℝ × ℝ := (e1.trans e2m).trans ((MeasurableEquiv.refl ℝ).prodCongr e3m)
  have hmp : MeasurePreserving e volume volume :=
    ((PiLp.volume_preserving_ofLp (Fin 2)).trans
      (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 1)).trans
      ((MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ))
  have he_symm (p : ℝ × ℝ) : e.symm p = mk2 p.2 p.1 := by
    ext k; fin_cases k <;> rfl
  have he_apply (q : Plane2) : e q = (q 1, q 0) := by
    apply e.symm.injective; rw [MeasurableEquiv.symm_apply_apply, he_symm, mk2_eta]
  have hpre : e ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R) = Q2 R := by
    ext q; simp only [Set.mem_preimage, Set.mem_prod, he_apply, Q2]
    constructor
    · rintro ⟨h1, h0⟩ i; fin_cases i <;> assumption
    · intro h; exact ⟨h 1, h 0⟩
  have hQ2m : MeasurableSet (Q2 R) := by
    have heq : Q2 R = ⋂ i : Fin 2, (fun y : Plane2 => y i) ⁻¹' Icc (-R) R := by ext y; simp [Q2]
    rw [heq]
    exact MeasurableSet.iInter fun i =>
      measurableSet_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
  have hchg : (∫ q in Q2 R, f q) = ∫ p in Icc (-R) R ×ˢ Icc (-R) R, f (mk2 p.2 p.1) := by
    have h1 : (∫ q in Q2 R, f q) = ∫ q in e ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R), (f ∘ e.symm) (e q) := by
      rw [hpre]; apply setIntegral_congr_fun hQ2m; intro q _; simp
    rw [h1, hmp.setIntegral_preimage_emb e.measurableEmbedding (f ∘ e.symm) (Icc (-R) R ×ˢ Icc (-R) R)]
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro p _; simp [he_symm]
  rw [hchg]
  have hmk_c : Continuous (fun p : ℝ × ℝ => mk2 p.2 p.1) := by
    refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
    rw [continuous_pi_iff]; intro k; fin_cases k
    · exact continuous_snd
    · exact continuous_fst
  have hint : IntegrableOn (fun p : ℝ × ℝ => f (mk2 p.2 p.1)) (Icc (-R) R ×ˢ Icc (-R) R) volume :=
    (hf.comp hmk_c).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint]

private theorem eq_of_hasDerivAt_zero_Icc {f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ r ∈ Icc a b, HasDerivAt f 0 r) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    f x = f y := by
  have hc : ContinuousOn f (Icc a b) := fun r hr => (hd r hr).continuousAt.continuousWithinAt
  have h1 := monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    (fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => by rw [(hd r (interior_subset hr)).deriv])
  have h2 := antitoneOn_of_deriv_nonpos (convex_Icc a b) hc
    (fun r hr => (hd r (interior_subset hr)).differentiableAt.differentiableWithinAt)
    (fun r hr => by rw [(hd r (interior_subset hr)).deriv])
  rcases le_total x y with h | h
  · exact le_antisymm (h1 hx hy h) (h2 hx hy h)
  · exact le_antisymm (h2 hy hx h) (h1 hy hx h)

private noncomputable def rot2_iso (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) : Plane2 ≃ₗᵢ[ℝ] Plane2 :=
  { toLinearEquiv :=
      { toFun := fun q => mk2 (c * q 0 - s * q 1) (s * q 0 + c * q 1)
        invFun := fun y => mk2 (c * y 0 + s * y 1) (-s * y 0 + c * y 1)
        map_add' := fun x y => by ext i; fin_cases i <;> simp [mk2] <;> ring
        map_smul' := fun r x => by ext i; fin_cases i <;> simp [mk2] <;> ring
        left_inv := fun q => by
          ext i; fin_cases i <;> simp [mk2]
          · linear_combination q 0 * hcs
          · linear_combination q 1 * hcs
        right_inv := fun y => by
          ext i; fin_cases i <;> simp [mk2]
          · linear_combination y 0 * hcs
          · linear_combination y 1 * hcs }
    norm_map' := fun q => by
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fin.sum_univ_two, Fin.sum_univ_two]
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, mk2_0, mk2_1, Real.norm_eq_abs, sq_abs]
      linear_combination ((q 0) ^ 2 + (q 1) ^ 2) * hcs }

private theorem rot2_apply (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (q : Plane2) :
    rot2_iso c s hcs q = mk2 (c * q 0 - s * q 1) (s * q 0 + c * q 1) := rfl

private theorem rot2_e0 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rot2_iso c s hcs (e2 0) = c • e2 0 + s • e2 1 := by
  ext i; fin_cases i <;> simp [rot2_apply, mk2, e2]

private theorem rot2_e1 (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rot2_iso c s hcs (e2 1) = (-s) • e2 0 + c • e2 1 := by
  ext i; fin_cases i <;> simp [rot2_apply, mk2, e2]

private theorem rot2_derivs {u : Plane2 → ℝ} (hu : ContDiff ℝ 2 u)
    (p : Plane2) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    let W (q : Plane2) : ℝ := u (p + rot2_iso c s hcs q)
    ContDiff ℝ 2 W ∧
    (∀ q, pd2 W 0 q = c * pd2 u 0 (p + rot2_iso c s hcs q) + s * pd2 u 1 (p + rot2_iso c s hcs q)) ∧
    (∀ q, pd2 W 1 q = -s * pd2 u 0 (p + rot2_iso c s hcs q) + c * pd2 u 1 (p + rot2_iso c s hcs q)) ∧
    (∀ q, pd22 W 0 0 q + pd22 W 1 1 q = pd22 u 0 0 (p + rot2_iso c s hcs q) + pd22 u 1 1 (p + rot2_iso c s hcs q)) ∧
    (∀ q, K_sz W q = K_sz u (p + rot2_iso c s hcs q)) := by
  intro W
  let R := rot2_iso c s hcs
  have haff : ContDiff ℝ 2 (fun q : Plane2 => p + R q) := contDiff_const.add R.toContinuousLinearEquiv.contDiff
  have hWc2 : ContDiff ℝ 2 W := hu.comp haff
  have hpd_gen {f : Plane2 → ℝ} (hf : ContDiff ℝ 1 f) (q : Plane2) :
      pd2 (fun z => f (p + R z)) 0 q = c * pd2 f 0 (p + R q) + s * pd2 f 1 (p + R q) ∧
      pd2 (fun z => f (p + R z)) 1 q = -s * pd2 f 0 (p + R q) + c * pd2 f 1 (p + R q) := by
    have hcomp (i : Fin 2) : pd2 (fun z => f (p + R z)) i q = fderiv ℝ f (p + R q) (R (e2 i)) := by
      have hl : HasDerivAt (fun r : ℝ => p + R (q + r • e2 i)) (R (e2 i)) 0 := by
        have heq : (fun r : ℝ => p + R (q + r • e2 i)) = fun r => (p + R q) + r • R (e2 i) := by
          ext r; rw [map_add, map_smul, add_assoc]
        rw [heq]; simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (R (e2 i))).const_add (p + R q)
      have h1 := (hf.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt 0 hl
      have h2 := line_deriv2 (hf.comp (haff.of_le (by norm_num))) q (e2 i) 0
      simpa [pd2, Function.comp_def] using h2.unique h1
    constructor
    · rw [hcomp 0, rot2_e0, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; rfl
    · rw [hcomp 1, rot2_e1, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; rfl
  have hW0 (q : Plane2) : pd2 W 0 q = c * pd2 u 0 (p + R q) + s * pd2 u 1 (p + R q) :=
    (hpd_gen (hu.of_le (by norm_num)) q).1
  have hW1 (q : Plane2) : pd2 W 1 q = -s * pd2 u 0 (p + R q) + c * pd2 u 1 (p + R q) :=
    (hpd_gen (hu.of_le (by norm_num)) q).2
  have hpd_c1 (j : Fin 2) : ContDiff ℝ 1 (pd2 u j) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hpd22_eq (q : Plane2) :
      pd22 W 0 0 q = c ^ 2 * pd22 u 0 0 (p + R q) + c * s * (pd22 u 0 1 (p + R q) + pd22 u 1 0 (p + R q)) + s ^ 2 * pd22 u 1 1 (p + R q) ∧
      pd22 W 1 0 q = -s * c * pd22 u 0 0 (p + R q) - s ^ 2 * pd22 u 0 1 (p + R q) + c ^ 2 * pd22 u 1 0 (p + R q) + c * s * pd22 u 1 1 (p + R q) ∧
      pd22 W 0 1 q = -s * c * pd22 u 0 0 (p + R q) + c ^ 2 * pd22 u 0 1 (p + R q) - s ^ 2 * pd22 u 1 0 (p + R q) + c * s * pd22 u 1 1 (p + R q) ∧
      pd22 W 1 1 q = s ^ 2 * pd22 u 0 0 (p + R q) - c * s * (pd22 u 0 1 (p + R q) + pd22 u 1 0 (p + R q)) + c ^ 2 * pd22 u 1 1 (p + R q) := by
    have hf0 (k : Fin 2) : pd2 (pd2 W 0) k q =
        c * pd2 (fun z => pd2 u 0 (p + R z)) k q + s * pd2 (fun z => pd2 u 1 (p + R z)) k q := by
      have heq : pd2 W 0 = fun z => c * pd2 u 0 (p + R z) + s * pd2 u 1 (p + R z) := funext hW0
      rw [heq]
      have h1 : ContDiff ℝ 1 (fun z => pd2 u 0 (p + R z)) := (hpd_c1 0).comp (haff.of_le (by norm_num))
      have h2 : ContDiff ℝ 1 (fun z => pd2 u 1 (p + R z)) := (hpd_c1 1).comp (haff.of_le (by norm_num))
      have hl := line_deriv2 (((contDiff_const (c := c)).mul h1).add ((contDiff_const (c := s)).mul h2)) q (e2 k) 0
      have hr := ((line_deriv2 h1 q (e2 k) 0).const_mul c).fun_add ((line_deriv2 h2 q (e2 k) 0).const_mul s)
      simpa [pd2] using hl.unique hr
    have hf1 (k : Fin 2) : pd2 (pd2 W 1) k q =
        -s * pd2 (fun z => pd2 u 0 (p + R z)) k q + c * pd2 (fun z => pd2 u 1 (p + R z)) k q := by
      have heq : pd2 W 1 = fun z => -s * pd2 u 0 (p + R z) + c * pd2 u 1 (p + R z) := funext hW1
      rw [heq]
      have h1 : ContDiff ℝ 1 (fun z => pd2 u 0 (p + R z)) := (hpd_c1 0).comp (haff.of_le (by norm_num))
      have h2 : ContDiff ℝ 1 (fun z => pd2 u 1 (p + R z)) := (hpd_c1 1).comp (haff.of_le (by norm_num))
      have hl := line_deriv2 (((contDiff_const (c := -s)).mul h1).add ((contDiff_const (c := c)).mul h2)) q (e2 k) 0
      have hr := ((line_deriv2 h1 q (e2 k) 0).const_mul (-s)).fun_add ((line_deriv2 h2 q (e2 k) 0).const_mul c)
      simpa [pd2] using hl.unique hr
    have ha0 := hpd_gen (hpd_c1 0) q
    have ha1 := hpd_gen (hpd_c1 1) q
    unfold pd22
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hf0 0, ha0.1, ha1.1]; ring
    · rw [hf1 0, ha0.1, ha1.1]; ring
    · rw [hf0 1, ha0.2, ha1.2]; ring
    · rw [hf1 1, ha0.2, ha1.2]; ring
  refine ⟨hWc2, hW0, hW1, fun q => ?_, fun q => ?_⟩
  · obtain ⟨h00, _, _, h11⟩ := hpd22_eq q
    rw [h00, h11]
    linear_combination (pd22 u 0 0 (p + R q) + pd22 u 1 1 (p + R q)) * hcs
  · obtain ⟨h00, h10, h01, h11⟩ := hpd22_eq q
    have hsym : pd22 u 0 1 (p + R q) = pd22 u 1 0 (p + R q) := partial_comm2 hu (p + R q) 0 1
    unfold K_sz
    rw [hW0 q, hW1 q, h00, h10, h01, h11, hsym]
    have hA : (c * pd2 u 0 (p + R q) + s * pd2 u 1 (p + R q)) *
          (-s * c * pd22 u 0 0 (p + R q) - s ^ 2 * pd22 u 1 0 (p + R q) + c ^ 2 * pd22 u 1 0 (p + R q) + c * s * pd22 u 1 1 (p + R q)) -
        (-s * pd2 u 0 (p + R q) + c * pd2 u 1 (p + R q)) *
          (c ^ 2 * pd22 u 0 0 (p + R q) + c * s * (pd22 u 1 0 (p + R q) + pd22 u 1 0 (p + R q)) + s ^ 2 * pd22 u 1 1 (p + R q)) =
        c * (pd2 u 0 (p + R q) * pd22 u 1 0 (p + R q) - pd2 u 1 (p + R q) * pd22 u 0 0 (p + R q)) +
        s * (pd2 u 0 (p + R q) * pd22 u 1 1 (p + R q) - pd2 u 1 (p + R q) * pd22 u 1 0 (p + R q)) := by
      linear_combination (c * (pd2 u 0 (p + R q) * pd22 u 1 0 (p + R q) - pd2 u 1 (p + R q) * pd22 u 0 0 (p + R q)) +
        s * (pd2 u 0 (p + R q) * pd22 u 1 1 (p + R q) - pd2 u 1 (p + R q) * pd22 u 1 0 (p + R q))) * hcs
    have hB : (c * pd2 u 0 (p + R q) + s * pd2 u 1 (p + R q)) *
          (s ^ 2 * pd22 u 0 0 (p + R q) - c * s * (pd22 u 1 0 (p + R q) + pd22 u 1 0 (p + R q)) + c ^ 2 * pd22 u 1 1 (p + R q)) -
        (-s * pd2 u 0 (p + R q) + c * pd2 u 1 (p + R q)) *
          (-s * c * pd22 u 0 0 (p + R q) + c ^ 2 * pd22 u 1 0 (p + R q) - s ^ 2 * pd22 u 1 0 (p + R q) + c * s * pd22 u 1 1 (p + R q)) =
        -s * (pd2 u 0 (p + R q) * pd22 u 1 0 (p + R q) - pd2 u 1 (p + R q) * pd22 u 0 0 (p + R q)) +
        c * (pd2 u 0 (p + R q) * pd22 u 1 1 (p + R q) - pd2 u 1 (p + R q) * pd22 u 1 0 (p + R q)) := by
      linear_combination (-s * (pd2 u 0 (p + R q) * pd22 u 1 0 (p + R q) - pd2 u 1 (p + R q) * pd22 u 0 0 (p + R q)) +
        c * (pd2 u 0 (p + R q) * pd22 u 1 1 (p + R q) - pd2 u 1 (p + R q) * pd22 u 1 0 (p + R q))) * hcs
    rw [hA, hB]
    linear_combination ((pd2 u 0 (p + R q) * pd22 u 1 0 (p + R q) - pd2 u 1 (p + R q) * pd22 u 0 0 (p + R q)) ^ 2 +
      (pd2 u 0 (p + R q) * pd22 u 1 1 (p + R q) - pd2 u 1 (p + R q) * pd22 u 1 0 (p + R q)) ^ 2) * hcs

private theorem rot2_stability {u : Plane2 → ℝ}
    (hstab : ∀ φ : Plane2 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u y) ^ 2 - 1) * (φ y) ^ 2))
    (p : Plane2) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    {ψ : Plane2 → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    0 ≤ ∫ q : Plane2, (‖∇ ψ q‖ ^ 2 + (3 * (u (p + rot2_iso c s hcs q)) ^ 2 - 1) * (ψ q) ^ 2) := by
  let R := rot2_iso c s hcs
  let φ (y : Plane2) : ℝ := ψ (R.symm (y - p))
  have hφ_c1 : ContDiff ℝ 1 φ :=
    hψ.comp (R.symm.toContinuousLinearEquiv.contDiff.comp (contDiff_id.sub contDiff_const))
  have hφ_s : HasCompactSupport φ := by
    obtain ⟨B, hB⟩ := hψc.isBounded.subset_closedBall (0 : Plane2)
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall p B) ?_
    intro y hy
    have hm : R.symm (y - p) ∈ closedBall (0 : Plane2) B := hB (subset_tsupport ψ hy)
    rw [mem_closedBall, dist_zero_right, R.symm.norm_map] at hm
    rwa [mem_closedBall, dist_eq_norm]
  have hst := hstab φ hφ_c1 hφ_s
  have hgrad_norm (q : Plane2) : ‖∇ φ (p + R q)‖ ^ 2 = ‖∇ ψ q‖ ^ 2 := by
    have h1 : fderiv ℝ φ (p + R q) = (fderiv ℝ ψ q).comp R.symm.toContinuousLinearMap := by
      ext d
      have hl := line_deriv2 hφ_c1 (p + R q) d 0
      have hr := line_deriv2 hψ q (R.symm d) 0
      have heq : (fun s : ℝ => φ (p + R q + s • d)) = fun s => ψ (q + s • R.symm d) := by
        ext s; dsimp [φ]
        rw [show p + R q + s • d - p = R q + s • d by abel, map_add, map_smul, R.symm_apply_apply]
      rw [heq] at hl
      simpa using hl.unique hr
    have hnorm : ‖∇ φ (p + R q)‖ = ‖∇ ψ q‖ := by
      unfold gradient
      rw [(toDual ℝ Plane2).symm.norm_map, (toDual ℝ Plane2).symm.norm_map, h1]
      exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv (fderiv ℝ ψ q) R.symm
    rw [hnorm]
  have hmp_R : MeasurePreserving R volume volume := R.measurePreserving
  have hst1 : 0 ≤ ∫ y : Plane2, (‖∇ φ (p + y)‖ ^ 2 + (3 * (u (p + y)) ^ 2 - 1) * (φ (p + y)) ^ 2) := by
    have hshift := integral_add_left_eq_self (μ := volume)
      (fun y : Plane2 => ‖∇ φ y‖ ^ 2 + (3 * (u y) ^ 2 - 1) * (φ y) ^ 2) p
    linarith
  have hst2 : 0 ≤ ∫ q : Plane2, (‖∇ φ (p + R q)‖ ^ 2 + (3 * (u (p + R q)) ^ 2 - 1) * (φ (p + R q)) ^ 2) := by
    have hcomp := hmp_R.integral_comp R.toHomeomorph.measurableEmbedding
      (fun y : Plane2 => ‖∇ φ (p + y)‖ ^ 2 + (3 * (u (p + y)) ^ 2 - 1) * (φ (p + y)) ^ 2)
    linarith
  refine hst2.trans_eq (integral_congr_ae (ae_of_all _ fun q => ?_))
  dsimp only
  rw [hgrad_norm q]
  simp [φ, R]

private theorem vertical_constancy {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hK : ∀ q, K_sz W q = 0) {s : ℝ}
    (hA0 : 0 < pd2 W 0 (mk2 s 0)) (hB0 : pd2 W 1 (mk2 s 0) = 0) :
    ∀ t : ℝ, pd2 W 0 (mk2 s t) = pd2 W 0 (mk2 s 0) ∧
      pd2 W 1 (mk2 s t) = 0 ∧ W (mk2 s t) = W (mk2 s 0) := by
  let A (t : ℝ) : ℝ := pd2 W 0 (mk2 s t)
  let B (t : ℝ) : ℝ := pd2 W 1 (mk2 s t)
  have hAd (t : ℝ) : HasDerivAt A (pd22 W 0 1 (mk2 s t)) t :=
    hasDerivAt_mk2_1 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s t
  have hBd (t : ℝ) : HasDerivAt B (pd22 W 1 1 (mk2 s t)) t :=
    hasDerivAt_mk2_1 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s t
  have hAc : Continuous A := continuous_iff_continuousAt.mpr fun t => (hAd t).continuousAt
  have hK_eq (t : ℝ) : A t * pd22 W 0 1 (mk2 s t) = B t * pd22 W 0 0 (mk2 s t) ∧
      A t * pd22 W 1 1 (mk2 s t) = B t * pd22 W 0 1 (mk2 s t) := by
    have hk := hK (mk2 s t)
    unfold K_sz at hk
    have h1 : pd2 W 0 (mk2 s t) * pd22 W 1 0 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 0 (mk2 s t) = 0 := by
      nlinarith [sq_nonneg (pd2 W 0 (mk2 s t) * pd22 W 1 0 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 0 (mk2 s t)),
        sq_nonneg (pd2 W 0 (mk2 s t) * pd22 W 1 1 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 1 (mk2 s t))]
    have h2 : pd2 W 0 (mk2 s t) * pd22 W 1 1 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 1 (mk2 s t) = 0 := by
      nlinarith [sq_nonneg (pd2 W 0 (mk2 s t) * pd22 W 1 0 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 0 (mk2 s t)),
        sq_nonneg (pd2 W 0 (mk2 s t) * pd22 W 1 1 (mk2 s t) - pd2 W 1 (mk2 s t) * pd22 W 0 1 (mk2 s t))]
    have hsym := partial_comm2 hW (mk2 s t) 1 0
    rw [hsym] at h1
    exact ⟨by dsimp [A, B]; linarith, by dsimp [A, B]; linarith⟩
  have hconst_on {a b : ℝ} (ha0 : a ≤ 0) (h0b : 0 ≤ b) (hpos : ∀ t ∈ Icc a b, 0 < A t) :
      ∀ t ∈ Icc a b, A t = A 0 ∧ B t = 0 := by
    have hBA (t : ℝ) (ht : t ∈ Icc a b) : B t / A t = 0 := by
      have hzd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt (fun x => B x / A x) 0 r := by
        have hq := (hBd r).fun_div (hAd r) (hpos r hr).ne'
        refine hq.congr_deriv ?_
        have h2 := (hK_eq r).2
        have hne : A r ≠ 0 := (hpos r hr).ne'
        field_simp [hne]; linarith
      have heq := eq_of_hasDerivAt_zero_Icc hzd ht ⟨ha0, h0b⟩
      simpa [B, hB0] using heq
    have hB0_on (t : ℝ) (ht : t ∈ Icc a b) : B t = 0 := by
      have := hBA t ht
      exact (div_eq_zero_iff.mp this).resolve_right (hpos t ht).ne'
    have hA_on (t : ℝ) (ht : t ∈ Icc a b) : A t = A 0 := by
      have hzd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt A 0 r := by
        have h1 := (hK_eq r).1
        rw [hB0_on r hr, zero_mul] at h1
        have hder0 : pd22 W 0 1 (mk2 s r) = 0 := (mul_eq_zero.mp h1).resolve_left (hpos r hr).ne'
        exact (hAd r).congr_deriv hder0
      exact eq_of_hasDerivAt_zero_Icc hzd ht ⟨ha0, h0b⟩
    exact fun t ht => ⟨hA_on t ht, hB0_on t ht⟩
  have hpos_all (t : ℝ) : 0 < A t := by
    rcases le_or_gt 0 t with ht | ht
    · by_contra hle; push Not at hle
      let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ A r ≤ A 0 / 2}
      have hSne : S.Nonempty := ⟨t, ht, by linarith⟩
      have hSbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
      let T := sInf S
      have hT0 : 0 ≤ T := le_csInf hSne fun r hr => hr.1
      have hScl : IsClosed S := isClosed_Ici.inter (isClosed_le hAc continuous_const)
      have hT_mem : T ∈ S := hScl.csInf_mem hSne hSbdd
      have hT_pos : 0 < T := by
        rcases eq_or_lt_of_le hT0 with h0 | hpos
        · exfalso; have := hT_mem.2; rw [← h0] at this; linarith
        · exact hpos
      have hA_eq (r : ℝ) (hr0 : 0 ≤ r) (hrT : r < T) : A r = A 0 := by
        have hpos_r : ∀ u ∈ Icc 0 r, 0 < A u := by
          intro u ⟨hu0, hur⟩
          by_contra hu_le; push Not at hu_le
          have hmem : u ∈ S := ⟨hu0, by linarith⟩
          have : T ≤ u := csInf_le hSbdd hmem
          linarith
        exact (hconst_on le_rfl hr0 hpos_r r ⟨hr0, le_rfl⟩).1
      have hlim : Tendsto (fun n : ℕ => A (T - T / ((n : ℝ) + 2))) atTop (𝓝 (A T)) := by
        refine (hAc.tendsto T).comp ?_
        have h0 : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.sub h0
      have hconst_seq : (fun n : ℕ => A (T - T / ((n : ℝ) + 2))) = fun _ => A 0 := by
        ext n
        have h1 : 0 < T / ((n : ℝ) + 2) := by positivity
        have h2 : T / ((n : ℝ) + 2) ≤ T := by
          rw [div_le_iff₀ (by positivity)]; nlinarith
        exact hA_eq _ (by linarith) (by linarith)
      rw [hconst_seq] at hlim
      have hAT : A T = A 0 := tendsto_nhds_unique hlim tendsto_const_nhds
      linarith [hT_mem.2]
    · by_contra hle; push Not at hle
      let S : Set ℝ := {r : ℝ | r ≤ 0 ∧ A r ≤ A 0 / 2}
      have hSne : S.Nonempty := ⟨t, ht.le, by linarith⟩
      have hSbdd : BddAbove S := ⟨0, fun r hr => hr.1⟩
      let T := sSup S
      have hT0 : T ≤ 0 := csSup_le hSne fun r hr => hr.1
      have hScl : IsClosed S := isClosed_Iic.inter (isClosed_le hAc continuous_const)
      have hT_mem : T ∈ S := hScl.csSup_mem hSne hSbdd
      have hT_neg : T < 0 := by
        rcases eq_or_lt_of_le hT0 with h0 | hneg
        · exfalso; have := hT_mem.2; rw [h0] at this; linarith
        · exact hneg
      have hA_eq (r : ℝ) (hrT : T < r) (hr0 : r ≤ 0) : A r = A 0 := by
        have hpos_r : ∀ u ∈ Icc r 0, 0 < A u := by
          intro u ⟨hru, hu0⟩
          by_contra hu_le; push Not at hu_le
          have hmem : u ∈ S := ⟨hu0, by linarith⟩
          have : u ≤ T := le_csSup hSbdd hmem
          linarith
        exact (hconst_on hr0 le_rfl hpos_r r ⟨le_rfl, hr0⟩).1
      have hlim : Tendsto (fun n : ℕ => A (T - T / ((n : ℝ) + 2))) atTop (𝓝 (A T)) := by
        refine (hAc.tendsto T).comp ?_
        have h0 : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.sub h0
      have hconst_seq : (fun n : ℕ => A (T - T / ((n : ℝ) + 2))) = fun _ => A 0 := by
        ext n
        have h1 : T / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hT_neg (by positivity)
        have h2 : T ≤ T / ((n : ℝ) + 2) := by
          rw [le_div_iff₀ (by positivity)]; nlinarith
        exact hA_eq _ (by linarith) (by linarith)
      rw [hconst_seq] at hlim
      have hAT : A T = A 0 := tendsto_nhds_unique hlim tendsto_const_nhds
      linarith [hT_mem.2]
  have hAB (t : ℝ) : A t = A 0 ∧ B t = 0 :=
    hconst_on (min_le_right t 0) (le_max_right t 0) (fun r _ => hpos_all r) t ⟨min_le_left t 0, le_max_left t 0⟩
  intro t
  refine ⟨(hAB t).1, (hAB t).2, ?_⟩
  have hWd (r : ℝ) : HasDerivAt (fun x : ℝ => W (mk2 s x)) 0 r :=
    (hasDerivAt_mk2_1 (hW.of_le (by norm_num)) s r).congr_deriv (hAB r).2
  exact is_const_of_deriv_eq_zero (fun r => (hWd r).differentiableAt)
    (fun r => (hWd r).deriv) t 0

private theorem horizontal_ode_on_pos {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hpde : ∀ q, pd22 W 0 0 q + pd22 W 1 1 q + W q - (W q) ^ 3 = 0)
    (hK : ∀ q, K_sz W q = 0)
    (hA0 : 0 < pd2 W 0 (mk2 0 0)) (hB0 : pd2 W 1 (mk2 0 0) = 0)
    {a b : ℝ} (ha0 : a ≤ 0) (h0b : 0 ≤ b) (hpos : ∀ s ∈ Icc a b, 0 < pd2 W 0 (mk2 s 0)) :
    ∀ s ∈ Icc a b,
      (∀ t : ℝ, W (mk2 s t) = W (mk2 s 0)) ∧
      pd2 W 1 (mk2 s 0) = 0 ∧
      pd22 W 0 0 (mk2 s 0) = (W (mk2 s 0)) ^ 3 - W (mk2 s 0) ∧
      (1 / 2) * (pd2 W 0 (mk2 s 0)) ^ 2 - Wpot (W (mk2 s 0)) =
        (1 / 2) * (pd2 W 0 (mk2 0 0)) ^ 2 - Wpot (W (mk2 0 0)) := by
  let α (s : ℝ) : ℝ := pd2 W 0 (mk2 s 0)
  let β (s : ℝ) : ℝ := pd2 W 1 (mk2 s 0)
  have hαd (s : ℝ) : HasDerivAt α (pd22 W 0 0 (mk2 s 0)) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hβd (s : ℝ) : HasDerivAt β (pd22 W 1 0 (mk2 s 0)) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hβ0_on (s : ℝ) (hs : s ∈ Icc a b) : β s = 0 := by
    have hzd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt (fun x => β x / α x) 0 r := by
      have hq := (hβd r).fun_div (hαd r) (hpos r hr).ne'
      refine hq.congr_deriv ?_
      have hk := hK (mk2 r 0); unfold K_sz at hk
      have h1 : α r * pd22 W 1 0 (mk2 r 0) - β r * pd22 W 0 0 (mk2 r 0) = 0 := by
        nlinarith [sq_nonneg (pd2 W 0 (mk2 r 0) * pd22 W 1 0 (mk2 r 0) - pd2 W 1 (mk2 r 0) * pd22 W 0 0 (mk2 r 0)),
          sq_nonneg (pd2 W 0 (mk2 r 0) * pd22 W 1 1 (mk2 r 0) - pd2 W 1 (mk2 r 0) * pd22 W 0 1 (mk2 r 0))]
      have hne : α r ≠ 0 := (hpos r hr).ne'
      field_simp [hne]; linarith
    have heq := eq_of_hasDerivAt_zero_Icc hzd hs ⟨ha0, h0b⟩
    have hz : β s / α s = 0 := by simpa [β, hB0] using heq
    exact (div_eq_zero_iff.mp hz).resolve_right (hpos s hs).ne'
  have hvert (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) :
      pd2 W 0 (mk2 s t) = pd2 W 0 (mk2 s 0) ∧ pd2 W 1 (mk2 s t) = 0 ∧ W (mk2 s t) = W (mk2 s 0) :=
    vertical_constancy hW hK (hpos s hs) (hβ0_on s hs) t
  have hode (s : ℝ) (hs : s ∈ Icc a b) : pd22 W 0 0 (mk2 s 0) = (W (mk2 s 0)) ^ 3 - W (mk2 s 0) := by
    have h11 : pd22 W 1 1 (mk2 s 0) = 0 := by
      have h1 : HasDerivAt (fun r : ℝ => pd2 W 1 (mk2 s r)) (pd22 W 1 1 (mk2 s 0)) 0 :=
        hasDerivAt_mk2_1 ((hW.fderiv_right (by norm_num)).clm_apply (contDiff_const (c := e2 1))) s 0
      have h2 : (fun r : ℝ => pd2 W 1 (mk2 s r)) = fun _ => 0 := funext fun r => (hvert s hs r).2.1
      rw [h2] at h1
      exact h1.unique (hasDerivAt_const 0 0)
    linarith [hpde (mk2 s 0)]
  let E (s : ℝ) : ℝ := (1 / 2) * (α s) ^ 2 - Wpot (W (mk2 s 0))
  have hE_const (s : ℝ) (hs : s ∈ Icc a b) : E s = E 0 := by
    have hEd (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt E 0 r := by
      have hW_d : HasDerivAt (fun x : ℝ => W (mk2 x 0)) (α r) r :=
        hasDerivAt_mk2_0 (hW.of_le (by norm_num)) r 0
      have hWpot_d : HasDerivAt Wpot ((W (mk2 r 0)) ^ 3 - W (mk2 r 0)) (W (mk2 r 0)) := by
        unfold Wpot
        exact ((((hasDerivAt_const (W (mk2 r 0)) (1 : ℝ)).fun_sub
          (hasDerivAt_pow 2 (W (mk2 r 0)))).fun_pow 2).div_const 4).congr_deriv (by norm_num; ring)
      have hcomb := (((hαd r).fun_pow 2).const_mul (1 / 2 : ℝ)).fun_sub (hWpot_d.comp r hW_d)
      refine hcomb.congr_deriv ?_
      rw [hode r hr]; norm_num; ring
    exact eq_of_hasDerivAt_zero_Icc hEd hs ⟨ha0, h0b⟩
  intro s hs
  exact ⟨fun t => (hvert s hs t).2.2, hβ0_on s hs, hode s hs, hE_const s hs⟩

set_option maxHeartbeats 600000 in
private theorem quadratic_cap_1d {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hW1 : ∀ q, |W q| ≤ 1)
    {a b : ℝ} (hab : a < b)
    (h1d : ∀ s ∈ Icc a b, ∀ t : ℝ, W (mk2 s t) = W (mk2 s 0))
    (hode : ∀ s ∈ Icc a b, pd22 W 0 0 (mk2 s 0) = (W (mk2 s 0)) ^ 3 - W (mk2 s 0))
    (hya : 0 < pd2 W 0 (mk2 a 0)) (hma : 0 < pd22 W 0 0 (mk2 a 0))
    (hca : 24 * (pd2 W 0 (mk2 a 0)) ^ 2 < (pd22 W 0 0 (mk2 a 0)) ^ 2)
    (hyb : 0 < pd2 W 0 (mk2 b 0)) (hmb : 0 < -pd22 W 0 0 (mk2 b 0))
    (hcb : 24 * (pd2 W 0 (mk2 b 0)) ^ 2 < (-pd22 W 0 0 (mk2 b 0)) ^ 2) :
    ∃ (ψ ψ' : ℝ → ℝ) (a1 b1 γ : ℝ), 0 < γ ∧
      (∀ s, HasDerivAt ψ (ψ' s) s) ∧ Continuous ψ' ∧ ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧
      (∀ s ∉ Icc a1 b1, ψ s = 0 ∧ ψ' s = 0) ∧
      (∀ t : ℝ, (∫ s : ℝ, ((ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2)) ≤ -γ) := by
  let f (s : ℝ) : ℝ := W (mk2 s 0)
  let f' (s : ℝ) : ℝ := pd2 W 0 (mk2 s 0)
  let f'' (s : ℝ) : ℝ := pd22 W 0 0 (mk2 s 0)
  have hfd (s : ℝ) : HasDerivAt f (f' s) s := hasDerivAt_mk2_0 (hW.of_le (by norm_num)) s 0
  have hf'd (s : ℝ) : HasDerivAt f' (f'' s) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hf''c : Continuous f'' :=
    ((((hW.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).comp (by
        refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
        rw [continuous_pi_iff]; intro k; fin_cases k
        · exact continuous_id
        · exact continuous_const)
  let ya := f' a; let ma := f'' a
  let yb := f' b; let mb := -f'' b
  have hya' : 0 < ya := hya
  have hma' : 0 < ma := hma
  have hyb' : 0 < yb := hyb
  have hmb' : 0 < mb := hmb
  have hca' : 24 * ya ^ 2 < ma ^ 2 := hca
  have hcb' : 24 * yb ^ 2 < mb ^ 2 := hcb
  let a1 := a - 2 * ya / ma
  let b1 := b + 2 * yb / mb
  have ha1_lt : a1 < a := by
    have hpos : 0 < 2 * ya / ma := by positivity
    dsimp [a1]; linarith
  have hb_lt : b < b1 := by
    have hpos : 0 < 2 * yb / mb := by positivity
    dsimp [b1]; linarith
  let pL (s : ℝ) : ℝ := (ma ^ 2 / (4 * ya)) * (s - a1) ^ 2
  let pL' (s : ℝ) : ℝ := (ma ^ 2 / (2 * ya)) * (s - a1)
  let pR (s : ℝ) : ℝ := (mb ^ 2 / (4 * yb)) * (b1 - s) ^ 2
  let pR' (s : ℝ) : ℝ := -(mb ^ 2 / (2 * yb)) * (b1 - s)
  have hpLd (s : ℝ) : HasDerivAt pL (pL' s) s := by
    have h1 := ((hasDerivAt_id s).sub_const a1).fun_pow 2 |>.const_mul (ma ^ 2 / (4 * ya))
    refine h1.congr_deriv ?_; dsimp [pL']; norm_num; ring
  have hpRd (s : ℝ) : HasDerivAt pR (pR' s) s := by
    have h1 := ((hasDerivAt_const s b1).fun_sub (hasDerivAt_id s)).fun_pow 2 |>.const_mul (mb ^ 2 / (4 * yb))
    refine h1.congr_deriv ?_; dsimp [pR']; norm_num; ring
  have hpL_a1 : pL a1 = 0 := by dsimp [pL]; ring
  have hpL'_a1 : pL' a1 = 0 := by dsimp [pL']; ring
  have hpL_a : pL a = ya := by
    dsimp [pL, a1]; field_simp [hya'.ne', hma'.ne']; ring
  have hpL'_a : pL' a = ma := by
    dsimp [pL', a1]; field_simp [hya'.ne', hma'.ne']; ring
  have hpR_b : pR b = yb := by
    dsimp [pR, b1]; field_simp [hyb'.ne', hmb'.ne']; ring
  have hpR'_b : pR' b = -mb := by
    dsimp [pR', b1]; field_simp [hyb'.ne', hmb'.ne']; ring
  have hpR_b1 : pR b1 = 0 := by dsimp [pR]; ring
  have hpR'_b1 : pR' b1 = 0 := by dsimp [pR']; ring
  let ψ (s : ℝ) : ℝ :=
    if s ≤ a1 then 0 else if s ≤ a then pL s else if s ≤ b then f' s else if s ≤ b1 then pR s else 0
  let ψ' (s : ℝ) : ℝ :=
    if s ≤ a1 then 0 else if s ≤ a then pL' s else if s ≤ b then f'' s else if s ≤ b1 then pR' s else 0
  have hψd (s : ℝ) : HasDerivAt ψ (ψ' s) s := by
    rcases lt_trichotomy s a1 with h | hsa1 | h
    · have hev : ψ =ᶠ[𝓝 s] fun _ => 0 := by
        filter_upwards [gt_mem_nhds h] with r hr; dsimp [ψ]; rw [if_pos hr.le]
      simpa [ψ', h.le] using (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
    · rw [hsa1]
      have hev : ψ =ᶠ[𝓝 a1] fun r => if r ≤ a1 then 0 else pL r := by
        filter_upwards [gt_mem_nhds ha1_lt] with r hr
        dsimp [ψ]; split_ifs with h1 h2 <;> first | rfl | linarith
      have hg := hasDerivAt_glue (c := a1) (d := 0) (hasDerivAt_const a1 0) (hpL'_a1 ▸ hpLd a1) hpL_a1.symm
      simpa [ψ'] using hg.congr_of_eventuallyEq hev
    · rcases lt_trichotomy s a with ha | hsa | ha
      · have hev : ψ =ᶠ[𝓝 s] pL := by
          filter_upwards [(lt_mem_nhds h).and (gt_mem_nhds ha)] with r ⟨h1, h2⟩
          dsimp [ψ]; rw [if_neg (not_le.mpr h1), if_pos h2.le]
        simpa [ψ', not_le.mpr h, ha.le] using (hpLd s).congr_of_eventuallyEq hev
      · rw [hsa]
        have hev : ψ =ᶠ[𝓝 a] fun r => if r ≤ a then pL r else f' r := by
          filter_upwards [(lt_mem_nhds ha1_lt).and (gt_mem_nhds hab)] with r ⟨h1, h2⟩
          dsimp [ψ]; rw [if_neg (not_le.mpr h1)]; split_ifs with h3 h4 <;> first | rfl | linarith
        have hg := hasDerivAt_glue (c := a) (d := ma) (hpL'_a ▸ hpLd a) (hf'd a) hpL_a
        have hval : ψ' a = ma := by dsimp [ψ']; rw [if_neg (not_le.mpr ha1_lt), if_pos le_rfl]; exact hpL'_a
        rw [hval]; exact hg.congr_of_eventuallyEq hev
      · rcases lt_trichotomy s b with hb | hsb | hb
        · have hev : ψ =ᶠ[𝓝 s] f' := by
            filter_upwards [(lt_mem_nhds ha).and (gt_mem_nhds hb)] with r ⟨h1, h2⟩
            dsimp [ψ]; rw [if_neg (by linarith), if_neg (not_le.mpr h1), if_pos h2.le]
          simpa [ψ', show ¬ s ≤ a1 by linarith, not_le.mpr ha, hb.le] using (hf'd s).congr_of_eventuallyEq hev
        · rw [hsb]
          have hev : ψ =ᶠ[𝓝 b] fun r => if r ≤ b then f' r else pR r := by
            filter_upwards [(lt_mem_nhds hab).and (gt_mem_nhds hb_lt)] with r ⟨h1, h2⟩
            dsimp [ψ]; rw [if_neg (by linarith), if_neg (not_le.mpr h1)]
            split_ifs with h3 h4 <;> first | rfl | linarith
          have hg := hasDerivAt_glue (c := b) (d := -mb)
            (by simpa [mb] using hf'd b) (hpR'_b ▸ hpRd b) hpR_b.symm
          have hval : ψ' b = -mb := by
            dsimp [ψ', mb]; rw [if_neg (by linarith), if_neg (not_le.mpr hab), if_pos le_rfl]; ring
          rw [hval]; exact hg.congr_of_eventuallyEq hev
        · rcases lt_trichotomy s b1 with hb1 | hsb1 | hb1
          · have hev : ψ =ᶠ[𝓝 s] pR := by
              filter_upwards [(lt_mem_nhds hb).and (gt_mem_nhds hb1)] with r ⟨h1, h2⟩
              dsimp [ψ]; rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr h1), if_pos h2.le]
            simpa [ψ', show ¬ s ≤ a1 by linarith, show ¬ s ≤ a by linarith, not_le.mpr hb, hb1.le] using
              (hpRd s).congr_of_eventuallyEq hev
          · rw [hsb1]
            have hev : ψ =ᶠ[𝓝 b1] fun r => if r ≤ b1 then pR r else 0 := by
              filter_upwards [lt_mem_nhds hb_lt] with r hr
              dsimp [ψ]; rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hr)]
            have hg := hasDerivAt_glue (c := b1) (d := 0) (hpR'_b1 ▸ hpRd b1) (hasDerivAt_const b1 0) hpR_b1
            have hval : ψ' b1 = 0 := by
              dsimp [ψ']; rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hb_lt), if_pos le_rfl]
              exact hpR'_b1
            rw [hval]; exact hg.congr_of_eventuallyEq hev
          · have hev : ψ =ᶠ[𝓝 s] fun _ => 0 := by
              filter_upwards [lt_mem_nhds hb1] with r hr
              dsimp [ψ]; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hr)]
            simpa [ψ', show ¬ s ≤ a1 by linarith, show ¬ s ≤ a by linarith, show ¬ s ≤ b by linarith,
              not_le.mpr hb1] using (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq hev
  have hψ'c : Continuous ψ' := by
    have hpL'c : Continuous pL' := continuous_const.mul (continuous_id.sub continuous_const)
    have hpR'c : Continuous pR' := continuous_const.mul (continuous_const.sub continuous_id)
    rw [continuous_iff_continuousAt]; intro s
    rcases lt_trichotomy s a1 with h | hsa1 | h
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [gt_mem_nhds h] with r hr; dsimp [ψ']; rw [if_pos hr.le]
    · rw [hsa1]
      have hev : ψ' =ᶠ[𝓝 a1] fun r => if r ≤ a1 then 0 else pL' r := by
        filter_upwards [gt_mem_nhds ha1_lt] with r hr
        dsimp [ψ']; split_ifs with h1 h2 <;> first | rfl | linarith
      exact (continuousAt_glue (c := a1) continuousAt_const hpL'c.continuousAt hpL'_a1.symm).congr hev.symm
    · rcases lt_trichotomy s a with ha | hsa | ha
      · refine hpL'c.continuousAt.congr ?_
        filter_upwards [(lt_mem_nhds h).and (gt_mem_nhds ha)] with r ⟨h1, h2⟩
        dsimp [ψ']; rw [if_neg (not_le.mpr h1), if_pos h2.le]
      · rw [hsa]
        have hev : ψ' =ᶠ[𝓝 a] fun r => if r ≤ a then pL' r else f'' r := by
          filter_upwards [(lt_mem_nhds ha1_lt).and (gt_mem_nhds hab)] with r ⟨h1, h2⟩
          dsimp [ψ']; rw [if_neg (not_le.mpr h1)]; split_ifs with h3 h4 <;> first | rfl | linarith
        exact (continuousAt_glue (c := a) hpL'c.continuousAt hf''c.continuousAt hpL'_a).congr hev.symm
      · rcases lt_trichotomy s b with hb | hsb | hb
        · refine hf''c.continuousAt.congr ?_
          filter_upwards [(lt_mem_nhds ha).and (gt_mem_nhds hb)] with r ⟨h1, h2⟩
          dsimp [ψ']; rw [if_neg (by linarith), if_neg (not_le.mpr h1), if_pos h2.le]
        · rw [hsb]
          have hev : ψ' =ᶠ[𝓝 b] fun r => if r ≤ b then f'' r else pR' r := by
            filter_upwards [(lt_mem_nhds hab).and (gt_mem_nhds hb_lt)] with r ⟨h1, h2⟩
            dsimp [ψ']; rw [if_neg (by linarith), if_neg (not_le.mpr h1)]
            split_ifs with h3 h4 <;> first | rfl | linarith
          exact (continuousAt_glue (c := b) hf''c.continuousAt hpR'c.continuousAt
            (by rw [hpR'_b]; dsimp [mb]; ring)).congr hev.symm
        · rcases lt_trichotomy s b1 with hb1 | hsb1 | hb1
          · refine hpR'c.continuousAt.congr ?_
            filter_upwards [(lt_mem_nhds hb).and (gt_mem_nhds hb1)] with r ⟨h1, h2⟩
            dsimp [ψ']; rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr h1), if_pos h2.le]
          · rw [hsb1]
            have hev : ψ' =ᶠ[𝓝 b1] fun r => if r ≤ b1 then pR' r else 0 := by
              filter_upwards [lt_mem_nhds hb_lt] with r hr
              dsimp [ψ']; rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hr)]
            exact (continuousAt_glue (c := b1) hpR'c.continuousAt continuousAt_const hpR'_b1).congr hev.symm
          · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
            filter_upwards [lt_mem_nhds hb1] with r hr
            dsimp [ψ']; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hr)]
  have hψ_c1 : ContDiff ℝ 1 ψ := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun s => (hψd s).differentiableAt, ?_⟩
    rwa [show deriv ψ = ψ' from funext fun s => (hψd s).deriv]
  have hψ_supp : HasCompactSupport ψ := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a1) (b := b1)) ?_
    intro s hs; rw [Function.mem_support] at hs
    rw [Set.mem_Icc]; by_contra hnot
    rw [not_and_or, not_le, not_le] at hnot
    rcases hnot with h1 | h2
    · exact hs (by dsimp [ψ]; rw [if_pos h1.le])
    · exact hs (by dsimp [ψ]; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr h2)])
  let γ : ℝ := (1 / 6) * (mb * yb + ma * ya)
  have hγ_pos : 0 < γ := by dsimp [γ]; positivity
  have hQ1 (t : ℝ) :
      (∫ s : ℝ, ((ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2)) ≤ -γ := by
    let g (s : ℝ) : ℝ := (ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2
    have hgc : Continuous g :=
      (hψ'c.pow 2).add (((continuous_const.mul ((hW.continuous.comp (by
        refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
        rw [continuous_pi_iff]; intro k; fin_cases k
        · exact continuous_id
        · exact continuous_const)).pow 2)).sub continuous_const).mul (hψ_c1.continuous.pow 2))
    have hg_zero : ∀ s ∉ Icc a1 b1, g s = 0 := by
      intro s hs; rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with h1 | h2
      · simp [g, ψ, ψ', h1.le]
      · simp [g, ψ, ψ', show ¬ s ≤ a1 by linarith, show ¬ s ≤ a by linarith,
          show ¬ s ≤ b by linarith, not_le.mpr h2]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hg_zero,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (μ := volume) a1 a) (hgc.intervalIntegrable (μ := volume) a b)
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (μ := volume) a1 b) (hgc.intervalIntegrable (μ := volume) b b1)
    have hmid : (∫ s in a..b, g s) = -mb * yb - ma * ya := by
      have hcongr : (∫ s in a..b, g s) = ∫ s in a..b, ((f'' s) ^ 2 + (3 * (f s) ^ 2 - 1) * (f' s) ^ 2) := by
        apply intervalIntegral.integral_congr_ae
        refine ae_of_all _ fun s hs => ?_
        have hmem : s ∈ Ioo a b → g s = (f'' s) ^ 2 + (3 * (f s) ^ 2 - 1) * (f' s) ^ 2 := by
          intro h; dsimp [g, ψ, ψ']
          rw [if_neg (by linarith [h.1]), if_neg (not_le.mpr h.1), if_pos h.2.le,
            if_neg (by linarith [h.1]), if_neg (not_le.mpr h.1), if_pos h.2.le,
            h1d s ⟨h.1.le, h.2.le⟩ t]
        have hmem2 : s ∈ Ioc a b := by rw [Set.uIoc_of_le hab.le] at hs; exact hs
        by_cases hsb : s = b
        · rw [hsb]; dsimp [g, ψ, ψ']
          rw [if_neg (by linarith), if_neg (not_le.mpr hab), if_pos le_rfl,
            if_neg (by linarith), if_neg (not_le.mpr hab), if_pos le_rfl,
            h1d b ⟨hab.le, le_rfl⟩ t]
        · exact hmem ⟨hmem2.1, lt_of_le_of_ne hmem2.2 hsb⟩
      rw [hcongr]
      have hF_d (s : ℝ) (hs : s ∈ Icc a b) :
          HasDerivAt (fun r => ((f r) ^ 3 - f r) * f' r)
            ((f'' s) ^ 2 + (3 * (f s) ^ 2 - 1) * (f' s) ^ 2) s := by
        have h1 := ((hfd s).fun_pow 3).fun_sub (hfd s)
        have h2 := h1.fun_mul (hf'd s)
        refine h2.congr_deriv ?_
        have heq := hode s hs; dsimp [f, f''] at heq ⊢
        rw [heq]; norm_num; ring
      have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hF_d s (by rwa [Set.uIcc_of_le hab.le] at hs))
        (((hf''c.pow 2).add (((continuous_const.mul ((hW.continuous.comp (by
          refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
          rw [continuous_pi_iff]; intro k; fin_cases k
          · exact continuous_id
          · exact continuous_const)).pow 2)).sub continuous_const).mul
          ((continuous_iff_continuousAt.mpr fun r => (hf'd r).continuousAt).pow 2))).intervalIntegrable (μ := volume) a b)
      rw [hFTC, ← hode b ⟨hab.le, le_rfl⟩, ← hode a ⟨le_rfl, hab.le⟩]
      dsimp [mb, yb, ma, ya, f', f'']; ring
    have hright : (∫ s in b..b1, g s) ≤ (5 / 6) * (mb * yb) := by
      have hle_pt : ∀ s ∈ Icc b b1,
          g s ≤ (pR' s) ^ 2 + 2 * yb ^ 2 := by
        intro s ⟨hsb, hsb1⟩
        have hWsq : 3 * (W (mk2 s t)) ^ 2 - 1 ≤ 2 := by
          have := hW1 (mk2 s t)
          have h1 : (W (mk2 s t)) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (W (mk2 s t))]
          linarith
        have hpR_bnd : 0 ≤ pR s ∧ pR s ≤ yb := by
          dsimp [pR]
          have h1 : 0 ≤ b1 - s := by linarith
          have h2 : b1 - s ≤ 2 * yb / mb := by dsimp [b1]; linarith
          refine ⟨by positivity, ?_⟩
          have hsq : (b1 - s) ^ 2 ≤ (2 * yb / mb) ^ 2 := pow_le_pow_left₀ h1 h2 2
          calc (mb ^ 2 / (4 * yb)) * (b1 - s) ^ 2
              ≤ (mb ^ 2 / (4 * yb)) * (2 * yb / mb) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = yb := by field_simp [hyb'.ne', hmb'.ne']; ring
        have hψ_eq : ψ s = pR s ∧ ψ' s = pR' s := by
          by_cases heq : s = b
          · rw [heq]; dsimp [ψ, ψ']
            rw [if_neg (by linarith), if_neg (not_le.mpr hab), if_pos le_rfl,
              if_neg (by linarith), if_neg (not_le.mpr hab), if_pos le_rfl]
            exact ⟨hpR_b.symm, by rw [hpR'_b]; dsimp [mb]; ring⟩
          · have hgt : b < s := lt_of_le_of_ne hsb (Ne.symm heq)
            dsimp [ψ, ψ']
            rw [if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hgt), if_pos hsb1,
              if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr hgt), if_pos hsb1]
            exact ⟨rfl, rfl⟩
        dsimp [g]; rw [hψ_eq.1, hψ_eq.2]
        have hpsq : (pR s) ^ 2 ≤ yb ^ 2 := pow_le_pow_left₀ hpR_bnd.1 hpR_bnd.2 2
        nlinarith [sq_nonneg (pR s)]
      have hpc : Continuous (fun s : ℝ => (pR' s) ^ 2 + 2 * yb ^ 2) :=
        ((continuous_const.mul (continuous_const.sub continuous_id)).pow 2).add continuous_const
      have hmono := intervalIntegral.integral_mono_on hb_lt.le (hgc.intervalIntegrable (μ := volume) b b1)
        (hpc.intervalIntegrable (μ := volume) b b1) hle_pt
      have hanti (s : ℝ) : HasDerivAt (fun r => -(mb ^ 4 / (12 * yb ^ 2)) * (b1 - r) ^ 3 + 2 * yb ^ 2 * r)
          ((pR' s) ^ 2 + 2 * yb ^ 2) s := by
        have h1 := (((hasDerivAt_const s b1).fun_sub (hasDerivAt_id s)).fun_pow 3).const_mul (-(mb ^ 4 / (12 * yb ^ 2)))
        have h2 := (hasDerivAt_id s).const_mul (2 * yb ^ 2)
        refine (h1.fun_add h2).congr_deriv ?_
        dsimp [pR']; norm_num; ring
      have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hanti s)
        (hpc.intervalIntegrable (μ := volume) b b1)
      have hval : (-(mb ^ 4 / (12 * yb ^ 2)) * (b1 - b1) ^ 3 + 2 * yb ^ 2 * b1) -
          (-(mb ^ 4 / (12 * yb ^ 2)) * (b1 - b) ^ 3 + 2 * yb ^ 2 * b) =
          (2 / 3) * (mb * yb) + 4 * yb ^ 3 / mb := by
        dsimp [b1]; field_simp [hyb'.ne', hmb'.ne']; ring
      have hsmall : 4 * yb ^ 3 / mb < (1 / 6) * (mb * yb) := by
        rw [div_lt_iff₀ hmb']
        have h1 : 24 * yb ^ 2 * yb < mb ^ 2 * yb := mul_lt_mul_of_pos_right hcb' hyb'
        linarith only [h1]
      linarith only [hmono, heval, hval, hsmall]
    have hleft : (∫ s in a1..a, g s) ≤ (5 / 6) * (ma * ya) := by
      have hle_pt : ∀ s ∈ Icc a1 a, g s ≤ (pL' s) ^ 2 + 2 * ya ^ 2 := by
        intro s ⟨hsa1, hsa⟩
        have hWsq : 3 * (W (mk2 s t)) ^ 2 - 1 ≤ 2 := by
          have := hW1 (mk2 s t)
          have h1 : (W (mk2 s t)) ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (W (mk2 s t))]
          linarith
        have hpL_bnd : 0 ≤ pL s ∧ pL s ≤ ya := by
          dsimp [pL]
          have h1 : 0 ≤ s - a1 := by linarith
          have h2 : s - a1 ≤ 2 * ya / ma := by dsimp [a1]; linarith
          refine ⟨by positivity, ?_⟩
          have hsq : (s - a1) ^ 2 ≤ (2 * ya / ma) ^ 2 := pow_le_pow_left₀ h1 h2 2
          calc (ma ^ 2 / (4 * ya)) * (s - a1) ^ 2
              ≤ (ma ^ 2 / (4 * ya)) * (2 * ya / ma) ^ 2 := mul_le_mul_of_nonneg_left hsq (by positivity)
            _ = ya := by field_simp [hya'.ne', hma'.ne']; ring
        have hψ_eq : ψ s = pL s ∧ ψ' s = pL' s := by
          by_cases heq : s = a1
          · rw [heq]; dsimp [ψ, ψ']; rw [if_pos le_rfl, if_pos le_rfl]; exact ⟨hpL_a1.symm, hpL'_a1.symm⟩
          · have hgt : a1 < s := lt_of_le_of_ne hsa1 (Ne.symm heq)
            dsimp [ψ, ψ']
            rw [if_neg (not_le.mpr hgt), if_pos hsa, if_neg (not_le.mpr hgt), if_pos hsa]
            exact ⟨rfl, rfl⟩
        dsimp [g]; rw [hψ_eq.1, hψ_eq.2]
        have hpsq : (pL s) ^ 2 ≤ ya ^ 2 := pow_le_pow_left₀ hpL_bnd.1 hpL_bnd.2 2
        nlinarith [sq_nonneg (pL s)]
      have hpc : Continuous (fun s : ℝ => (pL' s) ^ 2 + 2 * ya ^ 2) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).pow 2).add continuous_const
      have hmono := intervalIntegral.integral_mono_on ha1_lt.le (hgc.intervalIntegrable (μ := volume) a1 a)
        (hpc.intervalIntegrable (μ := volume) a1 a) hle_pt
      have hanti (s : ℝ) : HasDerivAt (fun r => (ma ^ 4 / (12 * ya ^ 2)) * (r - a1) ^ 3 + 2 * ya ^ 2 * r)
          ((pL' s) ^ 2 + 2 * ya ^ 2) s := by
        have h1 := (((hasDerivAt_id s).sub_const a1).fun_pow 3).const_mul (ma ^ 4 / (12 * ya ^ 2))
        have h2 := (hasDerivAt_id s).const_mul (2 * ya ^ 2)
        refine (h1.fun_add h2).congr_deriv ?_
        dsimp [pL']; norm_num; ring
      have heval := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hanti s)
        (hpc.intervalIntegrable (μ := volume) a1 a)
      have hval : ((ma ^ 4 / (12 * ya ^ 2)) * (a - a1) ^ 3 + 2 * ya ^ 2 * a) -
          ((ma ^ 4 / (12 * ya ^ 2)) * (a1 - a1) ^ 3 + 2 * ya ^ 2 * a1) =
          (2 / 3) * (ma * ya) + 4 * ya ^ 3 / ma := by
        dsimp [a1]; field_simp [hya'.ne', hma'.ne']; ring
      have hsmall : 4 * ya ^ 3 / ma < (1 / 6) * (ma * ya) := by
        rw [div_lt_iff₀ hma']
        have h1 : 24 * ya ^ 2 * ya < ma ^ 2 * ya := mul_lt_mul_of_pos_right hca' hya'
        linarith only [h1]
      linarith only [hmono, heval, hval, hsmall]
    dsimp [γ]; linarith only [hsplit1, hsplit2, hmid, hright, hleft]
  refine ⟨ψ, ψ', a1, b1, γ, hγ_pos, hψd, hψ'c, hψ_c1, hψ_supp, ?_, hQ1⟩
  intro s hs
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with h1 | h2
  · exact ⟨by dsimp [ψ]; rw [if_pos h1.le], by dsimp [ψ']; rw [if_pos h1.le]⟩
  · exact ⟨by dsimp [ψ]; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr h2)],
      by dsimp [ψ']; rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (not_le.mpr h2)]⟩

private theorem quadratic_cap_contradiction {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hW1 : ∀ q, |W q| ≤ 1)
    (hstab : ∀ ψ : Plane2 → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ q : Plane2, (‖∇ ψ q‖ ^ 2 + (3 * (W q) ^ 2 - 1) * (ψ q) ^ 2))
    {a b : ℝ} (hab : a < b)
    (h1d : ∀ s ∈ Icc a b, ∀ t : ℝ, W (mk2 s t) = W (mk2 s 0))
    (hode : ∀ s ∈ Icc a b, pd22 W 0 0 (mk2 s 0) = (W (mk2 s 0)) ^ 3 - W (mk2 s 0))
    (hya : 0 < pd2 W 0 (mk2 a 0)) (hma : 0 < pd22 W 0 0 (mk2 a 0))
    (hca : 24 * (pd2 W 0 (mk2 a 0)) ^ 2 < (pd22 W 0 0 (mk2 a 0)) ^ 2)
    (hyb : 0 < pd2 W 0 (mk2 b 0)) (hmb : 0 < -pd22 W 0 0 (mk2 b 0))
    (hcb : 24 * (pd2 W 0 (mk2 b 0)) ^ 2 < (-pd22 W 0 0 (mk2 b 0)) ^ 2) :
    False := by
  obtain ⟨ψ, ψ', a1, b1, γ, hγ_pos, hψd, hψ'c, hψ_c1, hψ_supp, hψ_zero, hQ1⟩ :=
    quadratic_cap_1d hW hW1 hab h1d hode hya hma hca hyb hmb hcb
  let Aψ : ℝ := ∫ s : ℝ, (ψ s) ^ 2
  have hAψ_nn : 0 ≤ Aψ := integral_nonneg fun s => sq_nonneg _
  let L : ℝ := max 2 (2 + 18 * (Aψ + 1) / γ)
  have hL2 : 2 ≤ L := le_max_left _ _
  let Φ (q : Plane2) : ℝ := ψ (q 0) * cut1 L (q 1)
  have hΦ_c1 : ContDiff ℝ 1 Φ :=
    (hψ_c1.comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
      ((contDiff_cut1 L).comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
  have hΦ_supp : HasCompactSupport Φ := by
    let R0 : ℝ := max (max |a1| |b1|) L
    have hcomp : IsCompact (Q2 R0) := by
      have h1 : Q2 R0 = (EuclideanSpace.equiv (Fin 2) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 2 => Icc (-R0) R0) := by
        ext y; constructor
        · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
        · rintro ⟨g, hg, rfl⟩ i; simpa using hg i (Set.mem_univ i)
      rw [h1]
      exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
    refine HasCompactSupport.of_support_subset_isCompact hcomp ?_
    intro q hq; rw [Function.mem_support] at hq
    intro i; fin_cases i
    · rw [Set.mem_Icc, ← abs_le]
      have hmem : q 0 ∈ Icc a1 b1 := by
        by_contra hnot
        exact hq (by simp [Φ, (hψ_zero (q 0) hnot).1])
      rw [abs_le]
      change -R0 ≤ q 0 ∧ q 0 ≤ R0
      exact ⟨by linarith [hmem.1, neg_abs_le a1, le_max_left |a1| |b1|, le_max_left (max |a1| |b1|) L],
        by linarith [hmem.2, le_abs_self b1, le_max_right |a1| |b1|, le_max_left (max |a1| |b1|) L]⟩
    · rw [Set.mem_Icc, ← abs_le]
      by_contra! hgt
      have h0 : cut1 L (q 1) = 0 := cut1_zero (le_trans (le_max_right _ L) hgt.le)
      exact hq (by simp [Φ, h0])
  have hst := hstab Φ hΦ_c1 hΦ_supp
  have hpd0 (q : Plane2) : pd2 Φ 0 q = ψ' (q 0) * cut1 L (q 1) := by
    have h1 := hasDerivAt_mk2_0 hΦ_c1 (q 0) (q 1)
    rw [mk2_eta] at h1
    have h2 : HasDerivAt (fun r : ℝ => Φ (mk2 r (q 1))) (ψ' (q 0) * cut1 L (q 1)) (q 0) := by
      have heq : (fun r : ℝ => Φ (mk2 r (q 1))) = fun r => ψ r * cut1 L (q 1) := by
        ext r; simp [Φ, mk2]
      rw [heq]; exact (hψd (q 0)).mul_const _
    exact h1.unique h2
  have hpd1 (q : Plane2) : pd2 Φ 1 q = ψ (q 0) * deriv (cut1 L) (q 1) := by
    have h1 := hasDerivAt_mk2_1 hΦ_c1 (q 0) (q 1)
    rw [mk2_eta] at h1
    have h2 : HasDerivAt (fun r : ℝ => Φ (mk2 (q 0) r)) (ψ (q 0) * deriv (cut1 L) (q 1)) (q 1) := by
      have heq : (fun r : ℝ => Φ (mk2 (q 0) r)) = fun r => ψ (q 0) * cut1 L r := by
        ext r; simp [Φ, mk2]
      rw [heq]
      exact ((contDiff_cut1 L).differentiable one_ne_zero (q 1)).hasDerivAt.const_mul (ψ (q 0))
    exact h1.unique h2
  have hgrad_c : Continuous (∇ Φ) := (toDual ℝ Plane2).symm.continuous.comp (hΦ_c1.continuous_fderiv one_ne_zero)
  have hgrad_s : HasCompactSupport (∇ Φ) :=
    hΦ_supp.mono' fun q hq => support_fderiv_subset ℝ fun he => hq (by simp [gradient, he])
  have hint_tot : Integrable (fun q : Plane2 => ‖∇ Φ q‖ ^ 2 + (3 * (W q) ^ 2 - 1) * (Φ q) ^ 2) :=
    ((hgrad_c.norm.pow 2).integrable_of_hasCompactSupport
      (hgrad_s.mono' fun q hq => subset_closure fun h0 => hq (by simp [h0]))).add
    ((((continuous_const.mul (hW.continuous.pow 2)).sub continuous_const).mul
      (hΦ_c1.continuous.pow 2)).integrable_of_hasCompactSupport
      (hΦ_supp.mono' fun q hq => subset_closure fun h0 => hq (by simp [h0])))
  rw [integral_split2 hint_tot] at hst
  have hψ2_int : Integrable (fun s : ℝ => (ψ s) ^ 2) :=
    (hψ_c1.continuous.pow 2).integrable_of_hasCompactSupport
      (hψ_supp.mono' fun s hs => subset_closure fun h0 => hs (by simp [h0]))
  have hcut2_int : Integrable (fun t : ℝ => (cut1 L t) ^ 2) :=
    ((contDiff_cut1 L).continuous.pow 2).integrable_of_hasCompactSupport
      ((hasCompactSupport_cut1 L).mono' fun s hs => subset_closure fun h0 => hs (by simp [h0]))
  have hdcut2_int : Integrable (fun t : ℝ => (deriv (cut1 L) t) ^ 2) := by
    refine (((contDiff_cut1 L).continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -L) (b := L)) ?_
    intro s hs; by_contra hnot
    have hge : L ≤ |s| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with h1 | h2
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    exact hs (by simp [(deriv_cut1_props L s).2.2 hge])
  have hinner_le (t : ℝ) :
      (∫ s : ℝ, (‖∇ Φ (mk2 s t)‖ ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (Φ (mk2 s t)) ^ 2)) ≤
        -γ * (cut1 L t) ^ 2 + Aψ * (deriv (cut1 L) t) ^ 2 := by
    have hInt_g : Integrable (fun s : ℝ => (ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2) := by
      have hc : Continuous (fun s : ℝ => (ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2) :=
        (hψ'c.pow 2).add (((continuous_const.mul ((hW.continuous.comp (by
          refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
          rw [continuous_pi_iff]; intro k; fin_cases k
          · exact continuous_id
          · exact continuous_const)).pow 2)).sub continuous_const).mul (hψ_c1.continuous.pow 2))
      refine hc.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a1) (b := b1)) ?_
      intro s hs; by_contra hnot
      exact hs (by simp [(hψ_zero s hnot).1, (hψ_zero s hnot).2])
    have heq : (fun s : ℝ => ‖∇ Φ (mk2 s t)‖ ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (Φ (mk2 s t)) ^ 2) =
        fun s => (cut1 L t) ^ 2 * ((ψ' s) ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (ψ s) ^ 2) +
          (deriv (cut1 L) t) ^ 2 * (ψ s) ^ 2 := by
      ext s
      rw [norm_grad2_sq, Fin.sum_univ_two, hpd0, hpd1]
      simp only [Φ, mk2_0, mk2_1]
      ring
    rw [heq, integral_add (hInt_g.const_mul _) (hψ2_int.const_mul _), integral_const_mul, integral_const_mul]
    have hmul := mul_le_mul_of_nonneg_left (hQ1 t) (sq_nonneg (cut1 L t))
    dsimp [Aψ]; linarith
  have hint_inner : Integrable (fun t : ℝ =>
      ∫ s : ℝ, (‖∇ Φ (mk2 s t)‖ ^ 2 + (3 * (W (mk2 s t)) ^ 2 - 1) * (Φ (mk2 s t)) ^ 2)) := by
    let e1 : Plane2 ≃ᵐ (Fin 2 → ℝ) := (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm
    let e2m : (Fin 2 → ℝ) ≃ᵐ ℝ × (Fin 1 → ℝ) := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 2 => ℝ) 1
    let e3m : (Fin 1 → ℝ) ≃ᵐ ℝ := MeasurableEquiv.funUnique (Fin 1) ℝ
    let e : Plane2 ≃ᵐ ℝ × ℝ := (e1.trans e2m).trans ((MeasurableEquiv.refl ℝ).prodCongr e3m)
    have hmp : MeasurePreserving e volume volume :=
      ((PiLp.volume_preserving_ofLp (Fin 2)).trans
        (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 2 => ℝ) 1)).trans
        ((MeasurePreserving.id volume).prod (MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ))
    have he_symm (p : ℝ × ℝ) : e.symm p = mk2 p.2 p.1 := by
      ext k; fin_cases k <;> rfl
    have hp : Integrable (fun p : ℝ × ℝ => ‖∇ Φ (mk2 p.2 p.1)‖ ^ 2 + (3 * (W (mk2 p.2 p.1)) ^ 2 - 1) * (Φ (mk2 p.2 p.1)) ^ 2) :=
      ((hmp.symm.integrable_comp_emb e.symm.measurableEmbedding).mpr hint_tot).congr (ae_of_all _ fun p => by simp [he_symm])
    exact hp.integral_prod_left
  have hmono := integral_mono hint_inner ((hcut2_int.const_mul (-γ)).add (hdcut2_int.const_mul Aψ)) hinner_le
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hcut2_int.const_mul _) (hdcut2_int.const_mul _), integral_const_mul, integral_const_mul] at hmono
  have hcut_ge : 2 * (L - 1) ≤ ∫ t : ℝ, (cut1 L t) ^ 2 := integral_cut1_sq_ge hL2
  have hdcut_le : (∫ t : ℝ, (deriv (cut1 L) t) ^ 2) ≤ 18 := integral_deriv_cut1_sq_le hL2
  have hL_big : 18 * (Aψ + 1) / γ ≤ L - 1 := by linarith [le_max_right 2 (2 + 18 * (Aψ + 1) / γ)]
  have h1 : 18 * (Aψ + 1) ≤ γ * (L - 1) := by
    have := (div_le_iff₀ hγ_pos).mp hL_big; linarith
  have h2 : -γ * (∫ t : ℝ, (cut1 L t) ^ 2) ≤ -γ * (2 * (L - 1)) := by nlinarith
  have h3 : Aψ * (∫ t : ℝ, (deriv (cut1 L) t) ^ 2) ≤ Aψ * 18 :=
    mul_le_mul_of_nonneg_left hdcut_le hAψ_nn
  linarith

private theorem E0_le_zero_of_ode {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hW1 : ∀ q, |W q| ≤ 1)
    (hpde : ∀ q, pd22 W 0 0 q + pd22 W 1 1 q + W q - (W q) ^ 3 = 0)
    (hK : ∀ q, K_sz W q = 0)
    (hA0 : 0 < pd2 W 0 (mk2 0 0)) (hB0 : pd2 W 1 (mk2 0 0) = 0) :
    (1 / 2) * (pd2 W 0 (mk2 0 0)) ^ 2 - Wpot (W (mk2 0 0)) ≤ 0 := by
  let f (s : ℝ) : ℝ := W (mk2 s 0)
  let f' (s : ℝ) : ℝ := pd2 W 0 (mk2 s 0)
  let f'' (s : ℝ) : ℝ := pd22 W 0 0 (mk2 s 0)
  let E0 : ℝ := (1 / 2) * (f' 0) ^ 2 - Wpot (f 0)
  have hfd (s : ℝ) : HasDerivAt f (f' s) s := hasDerivAt_mk2_0 (hW.of_le (by norm_num)) s 0
  have hf'd (s : ℝ) : HasDerivAt f' (f'' s) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hfd s).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun s => (hf'd s).continuousAt
  have hf1 (s : ℝ) : |f s| ≤ 1 := hW1 (mk2 s 0)
  have hf'0 : 0 < f' 0 := hA0
  change E0 ≤ 0
  by_contra! hE0_pos
  have hpos_r (s : ℝ) (hs : 0 ≤ s) : 0 < f' s := by
    by_contra hle; push Not at hle
    let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ f' r ≤ 0}
    have hSne : S.Nonempty := ⟨s, hs, hle⟩
    have hSbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
    let sp := sInf S
    have hsp0 : 0 ≤ sp := le_csInf hSne fun r hr => hr.1
    have hScl : IsClosed S := isClosed_Ici.inter (isClosed_le hf'c continuous_const)
    have hsp_mem : sp ∈ S := hScl.csInf_mem hSne hSbdd
    have hsp_pos : 0 < sp := lt_of_le_of_ne hsp0 (by rintro h; rw [← h] at hsp_mem; linarith [hsp_mem.2, hf'0])
    have hE_lt (r : ℝ) (hr0 : 0 ≤ r) (hrsp : r < sp) : (1 / 2) * (f' r) ^ 2 ≥ E0 := by
      have hpos_on : ∀ u ∈ Icc 0 r, 0 < f' u := by
        intro u ⟨hu0, hur⟩; by_contra hu_le; push Not at hu_le
        exact not_lt_of_ge (csInf_le hSbdd ⟨hu0, hu_le⟩) (lt_of_le_of_lt hur hrsp)
      have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hr0 hpos_on r ⟨hr0, le_rfl⟩).2.2.2
      have hWnn : 0 ≤ Wpot (f r) := by unfold Wpot; positivity
      dsimp [E0, f, f'] at hode ⊢; linarith
    have hlim : Tendsto (fun n : ℕ => (1 / 2) * (f' (sp - sp / ((n : ℝ) + 2))) ^ 2) atTop
        (𝓝 ((1 / 2) * (f' sp) ^ 2)) := by
      refine (tendsto_const_nhds.mul ((hf'c.tendsto sp).comp ?_ |>.pow 2))
      have h0 : Tendsto (fun n : ℕ => sp / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      simpa using tendsto_const_nhds.sub h0
    have hge_ev : ∀ n : ℕ, E0 ≤ (1 / 2) * (f' (sp - sp / ((n : ℝ) + 2))) ^ 2 := fun n => by
      have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
      have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
      exact hE_lt _ (by linarith) (by linarith)
    have hsp_ge : E0 ≤ (1 / 2) * (f' sp) ^ 2 := ge_of_tendsto hlim (Eventually.of_forall hge_ev)
    have hsp_ge0 : 0 ≤ f' sp := by
      have hlim2 : Tendsto (fun n : ℕ => f' (sp - sp / ((n : ℝ) + 2))) atTop (𝓝 (f' sp)) := by
        refine (hf'c.tendsto sp).comp ?_
        have h0 : Tendsto (fun n : ℕ => sp / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.sub h0
      refine ge_of_tendsto hlim2 (Eventually.of_forall fun n => ?_)
      have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
      have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
      by_contra hneg; push Not at hneg
      exact not_lt_of_ge (csInf_le hSbdd ⟨by linarith, hneg.le⟩) (by linarith)
    have hsp0' : f' sp = 0 := le_antisymm hsp_mem.2 hsp_ge0
    rw [hsp0'] at hsp_ge; linarith
  let c0 : ℝ := Real.sqrt (2 * E0)
  have hc0 : 0 < c0 := Real.sqrt_pos.mpr (by positivity)
  have hslope (s : ℝ) (hs : 0 ≤ s) : c0 ≤ f' s := by
    have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hs (fun r hr => hpos_r r hr.1) s ⟨hs, le_rfl⟩).2.2.2
    have hWnn : 0 ≤ Wpot (f s) := by unfold Wpot; positivity
    have hsq : 2 * E0 ≤ (f' s) ^ 2 := by dsimp [E0, f, f'] at hode ⊢; linarith
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (hpos_r s hs).le] at this
  let T : ℝ := 3 / c0
  have hT : 0 < T := by positivity
  obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope f f' hT hfc.continuousOn (fun r _ => hfd r)
  have hξ0 : 0 ≤ ξ := hξ.1.le
  have hdiff : f T - f 0 = f' ξ * T := by
    have := (eq_div_iff (sub_ne_zero.mpr hT.ne')).mp hmv; linarith
  have hge3 : 3 ≤ f T - f 0 := by
    rw [hdiff]
    calc 3 = c0 * T := by dsimp [T]; field_simp [hc0.ne']
      _ ≤ f' ξ * T := mul_le_mul_of_nonneg_right (hslope ξ hξ0) hT.le
  have hle2 : f T - f 0 ≤ 2 := by linarith [(abs_le.mp (hf1 T)).2, (abs_le.mp (hf1 0)).1]
  linarith

set_option maxHeartbeats 600000 in
private theorem E0_ge_zero_of_ode {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hW1 : ∀ q, |W q| ≤ 1)
    (hpde : ∀ q, pd22 W 0 0 q + pd22 W 1 1 q + W q - (W q) ^ 3 = 0)
    (hK : ∀ q, K_sz W q = 0)
    (hstab : ∀ ψ : Plane2 → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ q : Plane2, (‖∇ ψ q‖ ^ 2 + (3 * (W q) ^ 2 - 1) * (ψ q) ^ 2))
    (hA0 : 0 < pd2 W 0 (mk2 0 0)) (hB0 : pd2 W 1 (mk2 0 0) = 0) :
    0 ≤ (1 / 2) * (pd2 W 0 (mk2 0 0)) ^ 2 - Wpot (W (mk2 0 0)) := by
  let f (s : ℝ) : ℝ := W (mk2 s 0)
  let f' (s : ℝ) : ℝ := pd2 W 0 (mk2 s 0)
  let f'' (s : ℝ) : ℝ := pd22 W 0 0 (mk2 s 0)
  let E0 : ℝ := (1 / 2) * (f' 0) ^ 2 - Wpot (f 0)
  have hfd (s : ℝ) : HasDerivAt f (f' s) s := hasDerivAt_mk2_0 (hW.of_le (by norm_num)) s 0
  have hf'd (s : ℝ) : HasDerivAt f' (f'' s) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hfd s).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun s => (hf'd s).continuousAt
  have hf''c : Continuous f'' :=
    ((((hW.fderiv_right (by norm_num)).clm_apply contDiff_const).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).comp (by
        refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
        rw [continuous_pi_iff]; intro k; fin_cases k
        · exact continuous_id
        · exact continuous_const)
  have hf1 (s : ℝ) : |f s| ≤ 1 := hW1 (mk2 s 0)
  have hf'0 : 0 < f' 0 := hA0
  change 0 ≤ E0
  by_contra! hE0_neg
  have hW_lb (a b : ℝ) (ha0 : a ≤ 0) (h0b : 0 ≤ b) (hpos : ∀ r ∈ Icc a b, 0 < f' r)
      (r : ℝ) (hr : r ∈ Icc a b) : 2 * Real.sqrt (-E0) ≤ 1 - (f r) ^ 2 := by
    have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 ha0 h0b hpos r hr).2.2.2
    have hW : -E0 ≤ Wpot (f r) := by dsimp [E0, f, f'] at hode ⊢; nlinarith [sq_nonneg (f' r)]
    have h1 : 0 ≤ 1 - (f r) ^ 2 := by
      have := hf1 r; rw [← sq_abs (f r)]; nlinarith [abs_nonneg (f r)]
    have hsq : 4 * (-E0) ≤ (1 - (f r) ^ 2) ^ 2 := by unfold Wpot at hW; linarith
    have := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq h1, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show Real.sqrt 4 = 2 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    exact this
  have hR_ne : ({r : ℝ | 0 ≤ r ∧ f' r ≤ 0}).Nonempty := by
    by_contra hempty
    have hpos_r (r : ℝ) (hr : 0 ≤ r) : 0 < f' r := by
      by_contra hle; push Not at hle; exact hempty ⟨r, hr, hle⟩
    have hpos_f : ∃ s1 ≥ 0, 0 < f s1 := by
      by_contra! hle0
      have hf'_inc (r : ℝ) (hr : 0 ≤ r) : f' 0 ≤ f' r := by
        have hode_on (u : ℝ) (hu : u ∈ Icc 0 r) : 0 ≤ f'' u := by
          have heq := (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hr (fun x hx => hpos_r x hx.1) u hu).2.2.1
          have h1 : (f u) ^ 2 ≤ 1 := by rw [← sq_abs (f u)]; nlinarith [abs_nonneg (f u), hf1 u]
          have h2 := hle0 u hu.1
          dsimp [f, f''] at heq ⊢; rw [heq]; nlinarith
        exact monotoneOn_of_deriv_nonneg (convex_Icc 0 r) hf'c.continuousOn
          (fun u _ => (hf'd u).differentiableAt.differentiableWithinAt)
          (fun u hu => by rw [(hf'd u).deriv]; exact hode_on u (interior_subset hu))
          ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr
      let T := 3 / f' 0
      have hT : 0 < T := by positivity
      obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope f f' hT hfc.continuousOn (fun r _ => hfd r)
      have hdiff : f T - f 0 = f' ξ * T := by
        have := (eq_div_iff (sub_ne_zero.mpr hT.ne')).mp hmv; linarith
      have hge3 : 3 ≤ f T - f 0 := by
        rw [hdiff]; calc 3 = f' 0 * T := by dsimp [T]; field_simp [hf'0.ne']
          _ ≤ f' ξ * T := mul_le_mul_of_nonneg_right (hf'_inc ξ hξ.1.le) hT.le
      linarith [(abs_le.mp (hf1 T)).2, (abs_le.mp (hf1 0)).1]
    obtain ⟨s1, hs1_0, hfs1⟩ := hpos_f
    let c1 : ℝ := f s1 * (2 * Real.sqrt (-E0))
    have hc1 : 0 < c1 := mul_pos hfs1 (mul_pos two_pos (Real.sqrt_pos.mpr (by linarith)))
    have hf''_le (r : ℝ) (hr : s1 ≤ r) : f'' r ≤ -c1 := by
      have hpos_on : ∀ u ∈ Icc 0 r, 0 < f' u := fun u hu => hpos_r u hu.1
      have heq := (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl (by linarith) hpos_on r ⟨by linarith, le_rfl⟩).2.2.1
      have hfs : f s1 ≤ f r :=
        monotoneOn_of_deriv_nonneg (convex_Icc s1 r) hfc.continuousOn
          (fun u _ => (hfd u).differentiableAt.differentiableWithinAt)
          (fun u hu => by rw [(hfd u).deriv]; exact (hpos_r u (by linarith [(interior_subset hu).1])).le)
          ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr
      have hlb := hW_lb 0 r le_rfl (by linarith) hpos_on r ⟨by linarith, le_rfl⟩
      dsimp [f, f'', c1] at heq hlb hfs ⊢
      rw [heq]; nlinarith [Real.sqrt_pos.mpr (by linarith : 0 < -E0)]
    let T := s1 + (f' s1 + 1) / c1
    have hT : s1 < T := by
      have hfs : 0 < f' s1 + 1 := by linarith [hpos_r s1 hs1_0]
      have hpos : 0 < (f' s1 + 1) / c1 := by positivity
      dsimp [T]; linarith
    obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope f' f'' hT hf'c.continuousOn (fun r _ => hf'd r)
    have hdiff : f' T - f' s1 = f'' ξ * (T - s1) := by
      have := (eq_div_iff (by linarith : T - s1 ≠ 0)).mp hmv; linarith
    have hle : f' T - f' s1 ≤ -(f' s1 + 1) := by
      rw [hdiff]
      have hmul := mul_le_mul_of_nonneg_right (hf''_le ξ hξ.1.le) (by linarith : 0 ≤ T - s1)
      have hcalc : -c1 * (T - s1) = -(f' s1 + 1) := by dsimp [T]; field_simp [hc1.ne']; ring
      linarith
    linarith [hpos_r T (by linarith)]
  have hL_ne : ({r : ℝ | r ≤ 0 ∧ f' r ≤ 0}).Nonempty := by
    by_contra hempty
    have hpos_l (r : ℝ) (hr : r ≤ 0) : 0 < f' r := by
      by_contra hle; push Not at hle; exact hempty ⟨r, hr, hle⟩
    have hneg_f : ∃ s1 ≤ 0, f s1 < 0 := by
      by_contra! hge0
      have hf'_dec (r : ℝ) (hr : r ≤ 0) : f' 0 ≤ f' r := by
        have hode_on (u : ℝ) (hu : u ∈ Icc r 0) : f'' u ≤ 0 := by
          have heq := (horizontal_ode_on_pos hW hpde hK hA0 hB0 hr le_rfl (fun x hx => hpos_l x hx.2) u hu).2.2.1
          have h1 : (f u) ^ 2 ≤ 1 := by rw [← sq_abs (f u)]; nlinarith [abs_nonneg (f u), hf1 u]
          have h2 := hge0 u hu.2
          dsimp [f, f''] at heq ⊢; rw [heq]; nlinarith
        exact antitoneOn_of_deriv_nonpos (convex_Icc r 0) hf'c.continuousOn
          (fun u _ => (hf'd u).differentiableAt.differentiableWithinAt)
          (fun u hu => by rw [(hf'd u).deriv]; exact hode_on u (interior_subset hu))
          ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr
      let T := -(3 / f' 0)
      have hT : T < 0 := by
        have hpos : 0 < 3 / f' 0 := by positivity
        dsimp [T]; linarith
      obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope f f' hT hfc.continuousOn (fun r _ => hfd r)
      have hdiff : f 0 - f T = f' ξ * (0 - T) := by
        have := (eq_div_iff (by linarith : 0 - T ≠ 0)).mp hmv; linarith
      have hge3 : 3 ≤ f 0 - f T := by
        rw [hdiff]; calc 3 = f' 0 * (0 - T) := by dsimp [T]; field_simp [hf'0.ne']; ring
          _ ≤ f' ξ * (0 - T) := mul_le_mul_of_nonneg_right (hf'_dec ξ hξ.2.le) (by linarith)
      linarith [(abs_le.mp (hf1 0)).2, (abs_le.mp (hf1 T)).1]
    obtain ⟨s1, hs1_0, hfs1⟩ := hneg_f
    let c1 : ℝ := (-f s1) * (2 * Real.sqrt (-E0))
    have hc1 : 0 < c1 := mul_pos (by linarith) (mul_pos two_pos (Real.sqrt_pos.mpr (by linarith)))
    have hf''_ge (r : ℝ) (hr : r ≤ s1) : c1 ≤ f'' r := by
      have hpos_on : ∀ u ∈ Icc r 0, 0 < f' u := fun u hu => hpos_l u hu.2
      have heq := (horizontal_ode_on_pos hW hpde hK hA0 hB0 (by linarith) le_rfl hpos_on r ⟨le_rfl, by linarith⟩).2.2.1
      have hfs : f r ≤ f s1 :=
        monotoneOn_of_deriv_nonneg (convex_Icc r s1) hfc.continuousOn
          (fun u _ => (hfd u).differentiableAt.differentiableWithinAt)
          (fun u hu => by rw [(hfd u).deriv]; exact (hpos_l u (by linarith [(interior_subset hu).2])).le)
          ⟨le_rfl, hr⟩ ⟨hr, le_rfl⟩ hr
      have hlb := hW_lb r 0 (by linarith) le_rfl hpos_on r ⟨le_rfl, by linarith⟩
      dsimp [f, f'', c1] at heq hlb hfs ⊢
      rw [heq]; nlinarith [Real.sqrt_pos.mpr (by linarith : 0 < -E0)]
    let T := s1 - (f' s1 + 1) / c1
    have hT : T < s1 := by
      have hfs : 0 < f' s1 + 1 := by linarith [hpos_l s1 hs1_0]
      have hpos : 0 < (f' s1 + 1) / c1 := by positivity
      dsimp [T]; linarith
    obtain ⟨ξ, hξ, hmv⟩ := exists_hasDerivAt_eq_slope f' f'' hT hf'c.continuousOn (fun r _ => hf'd r)
    have hdiff : f' s1 - f' T = f'' ξ * (s1 - T) := by
      have := (eq_div_iff (by linarith : s1 - T ≠ 0)).mp hmv; linarith
    have hge : f' s1 + 1 ≤ f' s1 - f' T := by
      rw [hdiff]
      have hmul := mul_le_mul_of_nonneg_right (hf''_ge ξ hξ.2.le) (by linarith : 0 ≤ s1 - T)
      have hcalc : c1 * (s1 - T) = f' s1 + 1 := by dsimp [T]; field_simp [hc1.ne']; ring
      linarith
    linarith [hpos_l T (by linarith)]
  let SR : Set ℝ := {r : ℝ | 0 ≤ r ∧ f' r ≤ 0}
  let SL : Set ℝ := {r : ℝ | r ≤ 0 ∧ f' r ≤ 0}
  let sp := sInf SR
  let sm := sSup SL
  have hsp_mem : sp ∈ SR := (isClosed_Ici.inter (isClosed_le hf'c continuous_const)).csInf_mem hR_ne ⟨0, fun r hr => hr.1⟩
  have hsm_mem : sm ∈ SL := (isClosed_Iic.inter (isClosed_le hf'c continuous_const)).csSup_mem hL_ne ⟨0, fun r hr => hr.1⟩
  have hsp_pos : 0 < sp := lt_of_le_of_ne hsp_mem.1 (by rintro h; rw [← h] at hsp_mem; linarith [hsp_mem.2, hf'0])
  have hsm_neg : sm < 0 := lt_of_le_of_ne hsm_mem.1 (by rintro h; rw [h] at hsm_mem; linarith [hsm_mem.2, hf'0])
  have hpos_open (r : ℝ) (hr : r ∈ Ioo sm sp) : 0 < f' r := by
    rcases le_or_gt 0 r with h0 | h0
    · by_contra hle; push Not at hle
      exact not_lt_of_ge (csInf_le (s := SR) ⟨0, fun x hx => hx.1⟩ ⟨h0, hle⟩) hr.2
    · by_contra hle; push Not at hle
      exact not_lt_of_ge (le_csSup (s := SL) ⟨0, fun x hx => hx.1⟩ ⟨h0.le, hle⟩) hr.1
  have hsp_lim : Tendsto (fun n : ℕ => sp - sp / ((n : ℝ) + 2)) atTop (𝓝 sp) := by
    have h0 : Tendsto (fun n : ℕ => sp / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using tendsto_const_nhds.sub h0
  have hsm_lim : Tendsto (fun n : ℕ => sm - sm / ((n : ℝ) + 2)) atTop (𝓝 sm) := by
    have h0 : Tendsto (fun n : ℕ => sm / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using tendsto_const_nhds.sub h0
  have hsp_in (n : ℕ) : sp - sp / ((n : ℝ) + 2) ∈ Ioo sm sp := by
    have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
    have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hsm_in (n : ℕ) : sm - sm / ((n : ℝ) + 2) ∈ Ioo sm sp := by
    have h1 : sm / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hsm_neg (by positivity)
    have h2 : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    exact ⟨by linarith, by linarith⟩
  have hf'_sp : f' sp = 0 :=
    le_antisymm hsp_mem.2 (ge_of_tendsto ((hf'c.tendsto sp).comp hsp_lim)
      (Eventually.of_forall fun n => (hpos_open _ (hsp_in n)).le))
  have hf'_sm : f' sm = 0 :=
    le_antisymm hsm_mem.2 (ge_of_tendsto ((hf'c.tendsto sm).comp hsm_lim)
      (Eventually.of_forall fun n => (hpos_open _ (hsm_in n)).le))
  have hode_sp : f'' sp = (f sp) ^ 3 - f sp ∧ -Wpot (f sp) = E0 := by
    have h1 : ∀ n : ℕ, f'' (sp - sp / ((n : ℝ) + 2)) = (f (sp - sp / ((n : ℝ) + 2))) ^ 3 - f (sp - sp / ((n : ℝ) + 2)) := fun n => by
      have hin := hsp_in n
      have hle0 : 0 ≤ sp - sp / ((n : ℝ) + 2) := by
        have : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
        linarith
      exact (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hle0
        (fun u hu => hpos_open u ⟨by linarith [hu.1], by linarith [hu.2, hin.2]⟩) _ ⟨hle0, le_rfl⟩).2.2.1
    have h2 : ∀ n : ℕ, (1 / 2) * (f' (sp - sp / ((n : ℝ) + 2))) ^ 2 - Wpot (f (sp - sp / ((n : ℝ) + 2))) = E0 := fun n => by
      have hin := hsp_in n
      have hle0 : 0 ≤ sp - sp / ((n : ℝ) + 2) := by
        have : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
        linarith
      exact (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hle0
        (fun u hu => hpos_open u ⟨by linarith [hu.1], by linarith [hu.2, hin.2]⟩) _ ⟨hle0, le_rfl⟩).2.2.2
    have ht1 := (hf''c.tendsto sp).comp hsp_lim
    have ht1' := (((hfc.pow 3).sub hfc).tendsto sp).comp hsp_lim
    have heq1 : f'' sp = (f sp) ^ 3 - f sp :=
      tendsto_nhds_unique ht1 (ht1'.congr fun n => (h1 n).symm)
    have hWc : Continuous Wpot := by unfold Wpot; exact ((continuous_const.sub (continuous_id.pow 2)).pow 2).div_const 4
    have ht2 := ((((continuous_const (y := (1 / 2 : ℝ))).mul (hf'c.pow 2)).sub (hWc.comp hfc)).tendsto sp).comp hsp_lim
    have heq2 : (1 / 2) * (f' sp) ^ 2 - Wpot (f sp) = E0 :=
      tendsto_nhds_unique ht2 ((tendsto_const_nhds (x := E0)).congr fun n => (h2 n).symm)
    rw [hf'_sp] at heq2
    exact ⟨heq1, by linarith⟩
  have hode_sm : f'' sm = (f sm) ^ 3 - f sm ∧ -Wpot (f sm) = E0 := by
    have h1 : ∀ n : ℕ, f'' (sm - sm / ((n : ℝ) + 2)) = (f (sm - sm / ((n : ℝ) + 2))) ^ 3 - f (sm - sm / ((n : ℝ) + 2)) := fun n => by
      have hin := hsm_in n
      have hge0 : sm - sm / ((n : ℝ) + 2) ≤ 0 := by
        have : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        linarith
      exact (horizontal_ode_on_pos hW hpde hK hA0 hB0 hge0 le_rfl
        (fun u hu => hpos_open u ⟨by linarith [hu.1, hin.1], by linarith [hu.2]⟩) _ ⟨le_rfl, hge0⟩).2.2.1
    have h2 : ∀ n : ℕ, (1 / 2) * (f' (sm - sm / ((n : ℝ) + 2))) ^ 2 - Wpot (f (sm - sm / ((n : ℝ) + 2))) = E0 := fun n => by
      have hin := hsm_in n
      have hge0 : sm - sm / ((n : ℝ) + 2) ≤ 0 := by
        have : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        linarith
      exact (horizontal_ode_on_pos hW hpde hK hA0 hB0 hge0 le_rfl
        (fun u hu => hpos_open u ⟨by linarith [hu.1, hin.1], by linarith [hu.2]⟩) _ ⟨le_rfl, hge0⟩).2.2.2
    have ht1 := (hf''c.tendsto sm).comp hsm_lim
    have ht1' := (((hfc.pow 3).sub hfc).tendsto sm).comp hsm_lim
    have heq1 : f'' sm = (f sm) ^ 3 - f sm :=
      tendsto_nhds_unique ht1 (ht1'.congr fun n => (h1 n).symm)
    have hWc : Continuous Wpot := by unfold Wpot; exact ((continuous_const.sub (continuous_id.pow 2)).pow 2).div_const 4
    have ht2 := ((((continuous_const (y := (1 / 2 : ℝ))).mul (hf'c.pow 2)).sub (hWc.comp hfc)).tendsto sm).comp hsm_lim
    have heq2 : (1 / 2) * (f' sm) ^ 2 - Wpot (f sm) = E0 :=
      tendsto_nhds_unique ht2 ((tendsto_const_nhds (x := E0)).congr fun n => (h2 n).symm)
    rw [hf'_sm] at heq2
    exact ⟨heq1, by linarith⟩
  have hf_lt : f sm < f sp :=
    strictMonoOn_of_deriv_pos (convex_Icc sm sp) hfc.continuousOn
      (fun r hr => by rw [(hfd r).deriv]; exact hpos_open r (by rwa [interior_Icc] at hr))
      ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
  have hsq_eq : (f sm) ^ 2 = (f sp) ^ 2 := by
    have h1 : (1 - (f sp) ^ 2) ^ 2 = (1 - (f sm) ^ 2) ^ 2 := by
      unfold Wpot at hode_sp hode_sm; linarith [hode_sp.2, hode_sm.2]
    have ha : 0 ≤ 1 - (f sp) ^ 2 := by rw [← sq_abs (f sp)]; nlinarith [abs_nonneg (f sp), hf1 sp]
    have hb : 0 ≤ 1 - (f sm) ^ 2 := by rw [← sq_abs (f sm)]; nlinarith [abs_nonneg (f sm), hf1 sm]
    nlinarith
  have hfsp_pos : 0 < f sp := by nlinarith
  have hfsm_neg : f sm < 0 := by nlinarith
  have hfsp_lt1 : (f sp) ^ 2 < 1 := by
    have hWpos : 0 < Wpot (f sp) := by linarith [hode_sp.2]
    unfold Wpot at hWpos
    have hle1 : (f sp) ^ 2 ≤ 1 := by rw [← sq_abs (f sp)]; nlinarith [abs_nonneg (f sp), hf1 sp]
    by_contra hge; have : (f sp) ^ 2 = 1 := le_antisymm hle1 (by linarith)
    rw [this] at hWpos; norm_num at hWpos
  have hmb_pos : 0 < -f'' sp := by rw [hode_sp.1]; nlinarith
  have hma_pos : 0 < f'' sm := by
    have hsm_lt1 : (f sm) ^ 2 < 1 := by rw [hsq_eq]; exact hfsp_lt1
    rw [hode_sm.1]; nlinarith
  have hcond_sp : ∀ᶠ s in 𝓝 sp, 0 < -f'' s ∧ 24 * (f' s) ^ 2 < (-f'' s) ^ 2 := by
    have h1 : ContinuousAt (fun s => -f'' s) sp := hf''c.neg.continuousAt
    have h2 : ContinuousAt (fun s => (-f'' s) ^ 2 - 24 * (f' s) ^ 2) sp :=
      ((hf''c.neg.pow 2).sub (continuous_const.mul (hf'c.pow 2))).continuousAt
    have hv2 : 0 < (-f'' sp) ^ 2 - 24 * (f' sp) ^ 2 := by rw [hf'_sp]; nlinarith [sq_pos_of_pos hmb_pos]
    filter_upwards [(continuousAt_const (y := (0 : ℝ))).eventually_lt h1 hmb_pos,
      (continuousAt_const (y := (0 : ℝ))).eventually_lt h2 hv2] with s hs1 hs2
    exact ⟨hs1, by linarith⟩
  have hcond_sm : ∀ᶠ s in 𝓝 sm, 0 < f'' s ∧ 24 * (f' s) ^ 2 < (f'' s) ^ 2 := by
    have h1 : ContinuousAt f'' sm := hf''c.continuousAt
    have h2 : ContinuousAt (fun s => (f'' s) ^ 2 - 24 * (f' s) ^ 2) sm :=
      ((hf''c.pow 2).sub (continuous_const.mul (hf'c.pow 2))).continuousAt
    have hv2 : 0 < (f'' sm) ^ 2 - 24 * (f' sm) ^ 2 := by rw [hf'_sm]; nlinarith [sq_pos_of_pos hma_pos]
    filter_upwards [(continuousAt_const (y := (0 : ℝ))).eventually_lt h1 hma_pos,
      (continuousAt_const (y := (0 : ℝ))).eventually_lt h2 hv2] with s hs1 hs2
    exact ⟨hs1, by linarith⟩
  obtain ⟨Nb, hNb⟩ := Filter.eventually_atTop.mp (hsp_lim.eventually hcond_sp)
  obtain ⟨Na, hNa⟩ := Filter.eventually_atTop.mp (hsm_lim.eventually hcond_sm)
  let b := sp - sp / ((Nb : ℝ) + 2)
  let a := sm - sm / ((Na : ℝ) + 2)
  have hb_in : b ∈ Ioo sm sp := hsp_in Nb
  have ha_in : a ∈ Ioo sm sp := hsm_in Na
  have ha0 : a ≤ 0 := by
    have : sm ≤ sm / ((Na : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    dsimp [a]; linarith
  have h0b : 0 ≤ b := by
    have : sp / ((Nb : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
    dsimp [b]; linarith
  have hab : a < b := by
    have ha_neg : a < 0 := by
      have h1 : sm / ((Na : ℝ) + 2) > sm := by
        rw [gt_iff_lt, lt_div_iff₀ (by positivity)]; nlinarith
      dsimp [a]; linarith
    linarith
  have hpos_ab : ∀ s ∈ Icc a b, 0 < f' s := fun s hs => hpos_open s ⟨by linarith [ha_in.1, hs.1], by linarith [hb_in.2, hs.2]⟩
  have hode_ab := horizontal_ode_on_pos hW hpde hK hA0 hB0 ha0 h0b hpos_ab
  exact quadratic_cap_contradiction hW hW1 hstab hab
    (fun s hs t => (hode_ab s hs).1 t) (fun s hs => (hode_ab s hs).2.2.1)
    (hpos_open a ha_in) (hNa Na le_rfl).1 (hNa Na le_rfl).2
    (hpos_open b hb_in) (hNb Nb le_rfl).1 (hNb Nb le_rfl).2

set_option maxHeartbeats 600000 in
private theorem nonconstant_1d_heteroclinic {W : Plane2 → ℝ} (hW : ContDiff ℝ 2 W)
    (hW1 : ∀ q, |W q| ≤ 1)
    (hpde : ∀ q, pd22 W 0 0 q + pd22 W 1 1 q + W q - (W q) ^ 3 = 0)
    (hK : ∀ q, K_sz W q = 0)
    (hstab : ∀ ψ : Plane2 → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      0 ≤ ∫ q : Plane2, (‖∇ ψ q‖ ^ 2 + (3 * (W q) ^ 2 - 1) * (ψ q) ^ 2))
    (hA0 : 0 < pd2 W 0 (mk2 0 0)) (hB0 : pd2 W 1 (mk2 0 0) = 0) :
    (∀ q : Plane2, W q = W (mk2 (q 0) 0)) ∧
    (∀ s : ℝ, 0 < pd2 W 0 (mk2 s 0)) ∧
    (∀ s : ℝ, (1 / 2) * (pd2 W 0 (mk2 s 0)) ^ 2 = Wpot (W (mk2 s 0))) := by
  let f (s : ℝ) : ℝ := W (mk2 s 0)
  let f' (s : ℝ) : ℝ := pd2 W 0 (mk2 s 0)
  let f'' (s : ℝ) : ℝ := pd22 W 0 0 (mk2 s 0)
  let E0 : ℝ := (1 / 2) * (f' 0) ^ 2 - Wpot (f 0)
  have hfd (s : ℝ) : HasDerivAt f (f' s) s := hasDerivAt_mk2_0 (hW.of_le (by norm_num)) s 0
  have hf'd (s : ℝ) : HasDerivAt f' (f'' s) s :=
    hasDerivAt_mk2_0 ((hW.fderiv_right (by norm_num)).clm_apply contDiff_const) s 0
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun s => (hfd s).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun s => (hf'd s).continuousAt
  have hf1 (s : ℝ) : |f s| ≤ 1 := hW1 (mk2 s 0)
  have hf'0 : 0 < f' 0 := hA0
  have hE0_le : E0 ≤ 0 := E0_le_zero_of_ode hW hW1 hpde hK hA0 hB0
  have hE0_ge : 0 ≤ E0 := E0_ge_zero_of_ode hW hW1 hpde hK hstab hA0 hB0
  have hE0_eq : E0 = 0 := le_antisymm hE0_le hE0_ge
  have h1m_pos_0 : 0 < 1 - f 0 ∧ 0 < 1 + f 0 := by
    have hW0 : Wpot (f 0) = (1 / 2) * (f' 0) ^ 2 := by dsimp [E0] at hE0_eq; linarith
    have hWpos : 0 < Wpot (f 0) := by rw [hW0]; positivity
    have hle1 : |f 0| ≤ 1 := hf1 0
    have hne1 : f 0 ≠ 1 := by rintro h; rw [h] at hWpos; unfold Wpot at hWpos; norm_num at hWpos
    have hnem1 : f 0 ≠ -1 := by rintro h; rw [h] at hWpos; unfold Wpot at hWpos; norm_num at hWpos
    have h1 := abs_le.mp hle1
    exact ⟨by linarith [lt_of_le_of_ne h1.2 hne1], by linarith [lt_of_le_of_ne h1.1 hnem1.symm]⟩
  have hpos_all (s : ℝ) : 0 < f' s := by
    rcases le_or_gt 0 s with hs | hs
    · by_contra hle; push Not at hle
      let S : Set ℝ := {r : ℝ | 0 ≤ r ∧ f' r ≤ 0}
      have hSne : S.Nonempty := ⟨s, hs, hle⟩
      let sp := sInf S
      have hsp_mem : sp ∈ S := (isClosed_Ici.inter (isClosed_le hf'c continuous_const)).csInf_mem hSne ⟨0, fun r hr => hr.1⟩
      have hsp_pos : 0 < sp := lt_of_le_of_ne hsp_mem.1 (by rintro h; rw [← h] at hsp_mem; linarith [hsp_mem.2, hf'0])
      have hpos_lt (r : ℝ) (hr0 : 0 ≤ r) (hrsp : r < sp) : 0 < f' r := by
        by_contra h; push Not at h; exact not_lt_of_ge (csInf_le (s := S) ⟨0, fun x hx => hx.1⟩ ⟨hr0, h⟩) hrsp
      let g (r : ℝ) : ℝ := (1 - f r) * Real.exp (Real.sqrt 2 * r)
      have hgd (r : ℝ) : HasDerivAt g ((-f' r + Real.sqrt 2 * (1 - f r)) * Real.exp (Real.sqrt 2 * r)) r := by
        have h1 := (hasDerivAt_const r (1 : ℝ)).fun_sub (hfd r)
        have h2 := ((hasDerivAt_id r).const_mul (Real.sqrt 2)).exp
        refine (h1.fun_mul h2).congr_deriv ?_; simp only [id_eq]; ring
      have hg_inc (r : ℝ) (hr0 : 0 ≤ r) (hrsp : r < sp) : g 0 ≤ g r := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc 0 r) (continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt).continuousOn
          (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_) ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
        rw [(hgd x).deriv]
        have hx0 : 0 ≤ x := (interior_subset hx).1
        have hxsp : x < sp := lt_of_le_of_lt (interior_subset hx).2 hrsp
        have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 le_rfl hx0
          (fun u hu => hpos_lt u hu.1 (lt_of_le_of_lt hu.2 hxsp)) x ⟨hx0, le_rfl⟩).2.2.2
        have hEq : (1 / 2) * (f' x) ^ 2 = Wpot (f x) := by dsimp [E0, f, f'] at hode hE0_eq ⊢; linarith
        have h1m : 0 ≤ 1 - (f x) ^ 2 := by rw [← sq_abs (f x)]; nlinarith [abs_nonneg (f x), hf1 x]
        have hf'_eq : f' x = (1 - (f x) ^ 2) / Real.sqrt 2 := by
          have hsq : (f' x) ^ 2 = ((1 - (f x) ^ 2) / Real.sqrt 2) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; unfold Wpot at hEq; linarith
          have hnn1 : 0 ≤ f' x := (hpos_lt x hx0 hxsp).le
          have hnn2 : 0 ≤ (1 - (f x) ^ 2) / Real.sqrt 2 := by positivity
          nlinarith
        have h1p : 1 + f x ≤ 2 := by linarith [(abs_le.mp (hf1 x)).2]
        have h1m0 : 0 ≤ 1 - f x := by linarith [(abs_le.mp (hf1 x)).2]
        have hle : f' x ≤ Real.sqrt 2 * (1 - f x) := by
          rw [hf'_eq, div_le_iff₀ (Real.sqrt_pos.mpr two_pos)]
          have : Real.sqrt 2 * (1 - f x) * Real.sqrt 2 = 2 * (1 - f x) := by
            have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2); nlinarith
          rw [this]; nlinarith
        exact mul_nonneg (by linarith) (Real.exp_pos _).le
      have hsp_lim : Tendsto (fun n : ℕ => sp - sp / ((n : ℝ) + 2)) atTop (𝓝 sp) := by
        have h0 : Tendsto (fun n : ℕ => sp / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.sub h0
      have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
      have hg_sp : g 0 ≤ g sp := ge_of_tendsto ((hgc.tendsto sp).comp hsp_lim) (Eventually.of_forall fun n => by
        have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
        have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
        exact hg_inc _ (by linarith) (by linarith))
      have h1m_sp : 0 < 1 - f sp := by
        have hg0 : 0 < g 0 := by dsimp [g]; simpa using h1m_pos_0.1
        have hpos_prod : 0 < (1 - f sp) * Real.exp (Real.sqrt 2 * sp) := lt_of_lt_of_le hg0 hg_sp
        exact pos_of_mul_pos_left hpos_prod (Real.exp_pos _).le
      have hf_ge0 : f 0 ≤ f sp := by
        refine ge_of_tendsto ((hfc.tendsto sp).comp hsp_lim) (Eventually.of_forall fun n => ?_)
        have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
        have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
        exact monotoneOn_of_deriv_nonneg (convex_Icc 0 (sp - sp / ((n : ℝ) + 2))) hfc.continuousOn
          (fun x _ => (hfd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by rw [(hfd x).deriv]; exact (hpos_lt x (interior_subset hx).1 (by linarith [(interior_subset hx).2])).le)
          ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
      have h1p_sp : 0 < 1 + f sp := by linarith [h1m_pos_0.2]
      have hW_sp_pos : 0 < Wpot (f sp) := by
        unfold Wpot
        have hprod : 0 < (1 - f sp) * (1 + f sp) := mul_pos h1m_sp h1p_sp
        have heq : 1 - (f sp) ^ 2 = (1 - f sp) * (1 + f sp) := by ring
        rw [heq]; positivity
      have hf'_sp : f' sp = 0 :=
        le_antisymm hsp_mem.2 (ge_of_tendsto ((hf'c.tendsto sp).comp hsp_lim) (Eventually.of_forall fun n => by
          have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
          have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
          exact (hpos_lt _ (by linarith) (by linarith)).le))
      have hWc : Continuous Wpot := by unfold Wpot; exact ((continuous_const.sub (continuous_id.pow 2)).pow 2).div_const 4
      have hE_sp : (1 / 2) * (f' sp) ^ 2 - Wpot (f sp) = 0 := by
        have ht := ((((continuous_const (y := (1 / 2 : ℝ))).mul (hf'c.pow 2)).sub (hWc.comp hfc)).tendsto sp).comp hsp_lim
        have hseq : ∀ n : ℕ, (1 / 2) * (f' (sp - sp / ((n : ℝ) + 2))) ^ 2 - Wpot (f (sp - sp / ((n : ℝ) + 2))) = 0 := fun n => by
          have h1 : 0 < sp / ((n : ℝ) + 2) := by positivity
          have h2 : sp / ((n : ℝ) + 2) ≤ sp := by rw [div_le_iff₀ (by positivity)]; nlinarith
          have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 (a := 0) (b := sp - sp / ((n : ℝ) + 2)) le_rfl (by linarith)
            (fun u hu => hpos_lt u hu.1 (by linarith [hu.2])) (sp - sp / ((n : ℝ) + 2)) ⟨by linarith, le_rfl⟩).2.2.2
          dsimp [E0, f, f'] at hode hE0_eq ⊢; linarith
        exact tendsto_nhds_unique ht ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n => (hseq n).symm)
      rw [hf'_sp] at hE_sp; linarith
    · by_contra hle; push Not at hle
      let S : Set ℝ := {r : ℝ | r ≤ 0 ∧ f' r ≤ 0}
      have hSne : S.Nonempty := ⟨s, hs.le, hle⟩
      let sm := sSup S
      have hsm_mem : sm ∈ S := (isClosed_Iic.inter (isClosed_le hf'c continuous_const)).csSup_mem hSne ⟨0, fun r hr => hr.1⟩
      have hsm_neg : sm < 0 := lt_of_le_of_ne hsm_mem.1 (by rintro h; rw [h] at hsm_mem; linarith [hsm_mem.2, hf'0])
      have hpos_gt (r : ℝ) (hrsm : sm < r) (hr0 : r ≤ 0) : 0 < f' r := by
        by_contra h; push Not at h; exact not_lt_of_ge (le_csSup (s := S) ⟨0, fun x hx => hx.1⟩ ⟨hr0, h⟩) hrsm
      let g (r : ℝ) : ℝ := (1 + f r) * Real.exp (-Real.sqrt 2 * r)
      have hgd (r : ℝ) : HasDerivAt g ((f' r - Real.sqrt 2 * (1 + f r)) * Real.exp (-Real.sqrt 2 * r)) r := by
        have h1 := (hasDerivAt_const r (1 : ℝ)).fun_add (hfd r)
        have h2 := ((hasDerivAt_id r).const_mul (-Real.sqrt 2)).exp
        refine (h1.fun_mul h2).congr_deriv ?_; simp only [id_eq]; ring
      have hg_dec (r : ℝ) (hrsm : sm < r) (hr0 : r ≤ 0) : g 0 ≤ g r := by
        refine antitoneOn_of_deriv_nonpos (convex_Icc r 0) (continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt).continuousOn
          (fun x _ => (hgd x).differentiableAt.differentiableWithinAt) (fun x hx => ?_) ⟨le_rfl, hr0⟩ ⟨hr0, le_rfl⟩ hr0
        rw [(hgd x).deriv]
        have hxsm : sm < x := lt_of_lt_of_le hrsm (interior_subset hx).1
        have hx0 : x ≤ 0 := (interior_subset hx).2
        have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 hx0 le_rfl
          (fun u hu => hpos_gt u (lt_of_lt_of_le hxsm hu.1) hu.2) x ⟨le_rfl, hx0⟩).2.2.2
        have hEq : (1 / 2) * (f' x) ^ 2 = Wpot (f x) := by dsimp [E0, f, f'] at hode hE0_eq ⊢; linarith
        have h1m : 0 ≤ 1 - (f x) ^ 2 := by rw [← sq_abs (f x)]; nlinarith [abs_nonneg (f x), hf1 x]
        have hf'_eq : f' x = (1 - (f x) ^ 2) / Real.sqrt 2 := by
          have hsq : (f' x) ^ 2 = ((1 - (f x) ^ 2) / Real.sqrt 2) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; unfold Wpot at hEq; linarith
          have hnn1 : 0 ≤ f' x := (hpos_gt x hxsm hx0).le
          have hnn2 : 0 ≤ (1 - (f x) ^ 2) / Real.sqrt 2 := by positivity
          nlinarith
        have h1p0 : 0 ≤ 1 + f x := by linarith [(abs_le.mp (hf1 x)).1]
        have h1m2 : 1 - f x ≤ 2 := by linarith [(abs_le.mp (hf1 x)).1]
        have hle : f' x ≤ Real.sqrt 2 * (1 + f x) := by
          rw [hf'_eq, div_le_iff₀ (Real.sqrt_pos.mpr two_pos)]
          have : Real.sqrt 2 * (1 + f x) * Real.sqrt 2 = 2 * (1 + f x) := by
            have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2); nlinarith
          rw [this]; nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
      have hsm_lim : Tendsto (fun n : ℕ => sm - sm / ((n : ℝ) + 2)) atTop (𝓝 sm) := by
        have h0 : Tendsto (fun n : ℕ => sm / ((n : ℝ) + 2)) atTop (𝓝 0) :=
          tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        simpa using tendsto_const_nhds.sub h0
      have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
      have hg_sm : g 0 ≤ g sm := ge_of_tendsto ((hgc.tendsto sm).comp hsm_lim) (Eventually.of_forall fun n => by
        have h1 : sm / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hsm_neg (by positivity)
        have h2 : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        exact hg_dec _ (by linarith) (by linarith))
      have h1p_sm : 0 < 1 + f sm := by
        have hg0 : 0 < g 0 := by dsimp [g]; simpa using h1m_pos_0.2
        have hpos_prod : 0 < (1 + f sm) * Real.exp (-Real.sqrt 2 * sm) := lt_of_lt_of_le hg0 hg_sm
        exact pos_of_mul_pos_left hpos_prod (Real.exp_pos _).le
      have hf_le0 : f sm ≤ f 0 := by
        refine le_of_tendsto ((hfc.tendsto sm).comp hsm_lim) (Eventually.of_forall fun n => ?_)
        have h1 : sm / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hsm_neg (by positivity)
        have h2 : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
        exact monotoneOn_of_deriv_nonneg (convex_Icc (sm - sm / ((n : ℝ) + 2)) 0) hfc.continuousOn
          (fun x _ => (hfd x).differentiableAt.differentiableWithinAt)
          (fun x hx => by rw [(hfd x).deriv]; exact (hpos_gt x (by linarith [(interior_subset hx).1]) (interior_subset hx).2).le)
          ⟨le_rfl, by linarith⟩ ⟨by linarith, le_rfl⟩ (by linarith)
      have h1m_sm : 0 < 1 - f sm := by linarith [h1m_pos_0.1]
      have hW_sm_pos : 0 < Wpot (f sm) := by
        unfold Wpot
        have hprod : 0 < (1 - f sm) * (1 + f sm) := mul_pos h1m_sm h1p_sm
        have heq : 1 - (f sm) ^ 2 = (1 - f sm) * (1 + f sm) := by ring
        rw [heq]; positivity
      have hf'_sm : f' sm = 0 :=
        le_antisymm hsm_mem.2 (ge_of_tendsto ((hf'c.tendsto sm).comp hsm_lim) (Eventually.of_forall fun n => by
          have h1 : sm / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hsm_neg (by positivity)
          have h2 : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
          exact (hpos_gt _ (by linarith) (by linarith)).le))
      have hWc : Continuous Wpot := by unfold Wpot; exact ((continuous_const.sub (continuous_id.pow 2)).pow 2).div_const 4
      have hE_sm : (1 / 2) * (f' sm) ^ 2 - Wpot (f sm) = 0 := by
        have ht := ((((continuous_const (y := (1 / 2 : ℝ))).mul (hf'c.pow 2)).sub (hWc.comp hfc)).tendsto sm).comp hsm_lim
        have hseq : ∀ n : ℕ, (1 / 2) * (f' (sm - sm / ((n : ℝ) + 2))) ^ 2 - Wpot (f (sm - sm / ((n : ℝ) + 2))) = 0 := fun n => by
          have h1 : sm / ((n : ℝ) + 2) < 0 := div_neg_of_neg_of_pos hsm_neg (by positivity)
          have h2 : sm ≤ sm / ((n : ℝ) + 2) := by rw [le_div_iff₀ (by positivity)]; nlinarith
          have hode := (horizontal_ode_on_pos hW hpde hK hA0 hB0 (a := sm - sm / ((n : ℝ) + 2)) (b := 0) (by linarith) le_rfl
            (fun u hu => hpos_gt u (by linarith [hu.1]) hu.2) (sm - sm / ((n : ℝ) + 2)) ⟨le_rfl, by linarith⟩).2.2.2
          dsimp [E0, f, f'] at hode hE0_eq ⊢; linarith
        exact tendsto_nhds_unique ht ((tendsto_const_nhds (x := (0 : ℝ))).congr fun n => (hseq n).symm)
      rw [hf'_sm] at hE_sm; linarith
  refine ⟨fun q => ?_, hpos_all, fun s => ?_⟩
  · have hode := horizontal_ode_on_pos hW hpde hK hA0 hB0 (min_le_right (q 0) 0) (le_max_right (q 0) 0)
      (fun r _ => hpos_all r) (q 0) ⟨min_le_left _ _, le_max_left _ _⟩
    have := hode.1 (q 1); rwa [mk2_eta] at this
  · have hode := horizontal_ode_on_pos hW hpde hK hA0 hB0 (min_le_right s 0) (le_max_right s 0)
      (fun r _ => hpos_all r) s ⟨min_le_left _ _, le_max_left _ _⟩
    have hEq := hode.2.2.2
    dsimp [E0, f, f'] at hEq hE0_eq ⊢; linarith

theorem energy_2d_linear_bound {u_plus : Plane2 → ℝ} (hu_plus : ContDiff ℝ 2 u_plus)
    (hu_le1 : ∀ y, |u_plus y| ≤ 1)
    (hpde2 : ∀ y, (Δ u_plus y) + u_plus y - (u_plus y) ^ 3 = 0)
    (hstab2 : ∀ φ : Plane2 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2))
    (hK0 : ∀ y, K_sz u_plus y = 0) :
    ∀ R : ℝ, 0 ≤ R → (∫ y in Q2 R, e2_en u_plus y) ≤ 4 * R := by
  by_cases hgrad0 : ∀ y : Plane2, pd2 u_plus 0 y = 0 ∧ pd2 u_plus 1 y = 0
  · -- Case 1: Constant solution u_plus ≡ c ∈ {-1, 1}
    have hconst (y : Plane2) : u_plus y = u_plus 0 := by
      have hd (t : ℝ) : HasDerivAt (fun r : ℝ => u_plus (r • y)) 0 t := by
        have h1 : HasDerivAt (fun r : ℝ => u_plus (0 + r • y)) (fderiv ℝ u_plus (0 + t • y) y) t :=
          line_deriv2 (hu_plus.of_le (by norm_num)) 0 y t
        simp only [zero_add] at h1
        refine h1.congr_deriv ?_
        have hy : y = y 0 • e2 0 + y 1 • e2 1 := by ext i; fin_cases i <;> simp [e2]
        conv_lhs => arg 2; rw [hy]
        rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        have h0 := (hgrad0 (t • y)).1; have h1' := (hgrad0 (t • y)).2
        dsimp [pd2] at h0 h1'; rw [h0, h1']; ring
      have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
        (fun t => (hd t).deriv) (1 : ℝ) (0 : ℝ)
      simpa using this
    let c := u_plus 0
    have hΔ0 : (Δ u_plus) 0 = 0 := by
      rw [laplacian_sum2 hu_plus]
      have h00 : pd22 u_plus 0 0 0 = 0 := by
        unfold pd22
        rw [show pd2 u_plus 0 = fun _ => 0 from funext fun y => (hgrad0 y).1]
        unfold pd2; rw [fderiv_const_apply]; simp
      have h11 : pd22 u_plus 1 1 0 = 0 := by
        unfold pd22
        rw [show pd2 u_plus 1 = fun _ => 0 from funext fun y => (hgrad0 y).2]
        unfold pd2; rw [fderiv_const_apply]; simp
      rw [h00, h11, add_zero]
    have hc_eq : c - c ^ 3 = 0 := by have := hpde2 0; rw [hΔ0, zero_add] at this; exact this
    have hc_ne0 : c ≠ 0 := by
      rintro hc0
      change u_plus 0 = 0 at hc0
      let φ (y : Plane2) : ℝ := cut1 20 (y 0) * cut1 20 (y 1)
      have hφ_c1 : ContDiff ℝ 1 φ :=
        ((contDiff_cut1 20).comp (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff).mul
          ((contDiff_cut1 20).comp (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff)
      have hφ_s : HasCompactSupport φ := by
        have hcomp : IsCompact (Q2 20) := by
          have h1 : Q2 20 = (EuclideanSpace.equiv (Fin 2) ℝ).symm '' Set.pi Set.univ (fun _ : Fin 2 => Icc (-20) 20) := by
            ext y; constructor
            · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
            · rintro ⟨g, hg, rfl⟩ i; simpa using hg i (Set.mem_univ i)
          rw [h1]
          exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
        refine HasCompactSupport.of_support_subset_isCompact hcomp ?_
        intro y hy; rw [Function.mem_support] at hy; intro i; rw [Set.mem_Icc, ← abs_le]
        by_contra! hgt; fin_cases i
        · exact hy (by simp [φ, cut1_zero (R := 20) (s := y 0) (by simpa using hgt.le)])
        · exact hy (by simp [φ, cut1_zero (R := 20) (s := y 1) (by simpa using hgt.le)])
      have hst := hstab2 φ hφ_c1 hφ_s
      have hpd0 (y : Plane2) : pd2 φ 0 y = deriv (cut1 20) (y 0) * cut1 20 (y 1) := by
        have h1 := hasDerivAt_mk2_0 hφ_c1 (y 0) (y 1); rw [mk2_eta] at h1
        have h2 : HasDerivAt (fun r => φ (mk2 r (y 1))) (deriv (cut1 20) (y 0) * cut1 20 (y 1)) (y 0) := by
          have heq : (fun r => φ (mk2 r (y 1))) = fun r => cut1 20 r * cut1 20 (y 1) := by ext r; simp [φ, mk2]
          rw [heq]; exact ((contDiff_cut1 20).differentiable one_ne_zero (y 0)).hasDerivAt.mul_const _
        exact h1.unique h2
      have hpd1 (y : Plane2) : pd2 φ 1 y = cut1 20 (y 0) * deriv (cut1 20) (y 1) := by
        have h1 := hasDerivAt_mk2_1 hφ_c1 (y 0) (y 1); rw [mk2_eta] at h1
        have h2 : HasDerivAt (fun r => φ (mk2 (y 0) r)) (cut1 20 (y 0) * deriv (cut1 20) (y 1)) (y 1) := by
          have heq : (fun r => φ (mk2 (y 0) r)) = fun r => cut1 20 (y 0) * cut1 20 r := by ext r; simp [φ, mk2]
          rw [heq]; exact ((contDiff_cut1 20).differentiable one_ne_zero (y 1)).hasDerivAt.const_mul _
        exact h1.unique h2
      have hgrad_c : Continuous (∇ φ) := (toDual ℝ Plane2).symm.continuous.comp (hφ_c1.continuous_fderiv one_ne_zero)
      have hgrad_s : HasCompactSupport (∇ φ) :=
        hφ_s.mono' fun y hy => support_fderiv_subset ℝ fun he => hy (by simp [gradient, he])
      have hint_tot : Integrable (fun y : Plane2 => ‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) :=
        ((hgrad_c.norm.pow 2).integrable_of_hasCompactSupport
          (hgrad_s.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0]))).add
        ((((continuous_const.mul (hu_plus.continuous.pow 2)).sub continuous_const).mul
          (hφ_c1.continuous.pow 2)).integrable_of_hasCompactSupport
          (hφ_s.mono' fun y hy => subset_closure fun h0 => hy (by simp [h0])))
      rw [integral_split2 hint_tot] at hst
      have hcut_int : Integrable (fun s : ℝ => (cut1 20 s) ^ 2) :=
        ((contDiff_cut1 20).continuous.pow 2).integrable_of_hasCompactSupport
          ((hasCompactSupport_cut1 20).mono' fun s hs => subset_closure fun h0 => hs (by simp [h0]))
      have hdcut_int : Integrable (fun s : ℝ => (deriv (cut1 20) s) ^ 2) := by
        refine (((contDiff_cut1 20).continuous_deriv le_rfl).pow 2).integrable_of_hasCompactSupport ?_
        refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -20) (b := 20)) ?_
        intro s hs; by_contra hnot
        have hge : 20 ≤ |s| := by
          rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
          rcases hnot with h1 | h2
          · rw [abs_of_neg (by linarith)]; linarith
          · rw [abs_of_pos (by linarith)]; linarith
        exact hs (by simp [(deriv_cut1_props 20 s).2.2 hge])
      let I0 := ∫ s : ℝ, (cut1 20 s) ^ 2
      let I1 := ∫ s : ℝ, (deriv (cut1 20) s) ^ 2
      have hfactor : (∫ t : ℝ, ∫ s : ℝ,
          (‖∇ φ (mk2 s t)‖ ^ 2 + (3 * (u_plus (mk2 s t)) ^ 2 - 1) * (φ (mk2 s t)) ^ 2)) =
          I0 * (2 * I1 - I0) := by
        have hinner (t : ℝ) : (∫ s : ℝ,
            (‖∇ φ (mk2 s t)‖ ^ 2 + (3 * (u_plus (mk2 s t)) ^ 2 - 1) * (φ (mk2 s t)) ^ 2)) =
            (cut1 20 t) ^ 2 * I1 + ((deriv (cut1 20) t) ^ 2 - (cut1 20 t) ^ 2) * I0 := by
          have heq : (fun s : ℝ => ‖∇ φ (mk2 s t)‖ ^ 2 + (3 * (u_plus (mk2 s t)) ^ 2 - 1) * (φ (mk2 s t)) ^ 2) =
              fun s => (cut1 20 t) ^ 2 * (deriv (cut1 20) s) ^ 2 +
                ((deriv (cut1 20) t) ^ 2 - (cut1 20 t) ^ 2) * (cut1 20 s) ^ 2 := by
            ext s; rw [norm_grad2_sq, Fin.sum_univ_two, hpd0, hpd1, hconst (mk2 s t), hc0]
            simp only [φ, mk2_0, mk2_1]
            ring
          rw [heq, integral_add (hdcut_int.const_mul _) (hcut_int.const_mul _),
            integral_const_mul, integral_const_mul]
        simp_rw [hinner]
        have hsub_int : Integrable (fun t : ℝ => ((deriv (cut1 20) t) ^ 2 - (cut1 20 t) ^ 2) * I0) :=
          (hdcut_int.sub hcut_int).mul_const I0
        rw [integral_add (hcut_int.mul_const I1) hsub_int,
          integral_mul_const, integral_mul_const, integral_sub hdcut_int hcut_int]
        dsimp [I0, I1]; ring
      rw [hfactor] at hst
      have hI0 : 38 ≤ I0 := by linarith [integral_cut1_sq_ge (L := 20) (by norm_num)]
      have hI1 : I1 ≤ 18 := integral_deriv_cut1_sq_le (L := 20) (by norm_num)
      nlinarith
    have hc_sq : c ^ 2 = 1 := by
      have : c * (1 - c ^ 2) = 0 := by linarith
      have := (mul_eq_zero.mp this).resolve_left hc_ne0
      linarith
    intro R hR
    have he0 (y : Plane2) : e2_en u_plus y = 0 := by
      unfold e2_en Wpot
      rw [Fin.sum_univ_two, (hgrad0 y).1, (hgrad0 y).2, hconst y]
      change (1 / 2) * (0 ^ 2 + 0 ^ 2) + (1 - c ^ 2) ^ 2 / 4 = 0
      rw [hc_sq]; norm_num
    simp only [he0, integral_zero]
    linarith
  · -- Case 2: Nonconstant solution! Rotate around p to get W, then shift back around 0!
    push Not at hgrad0
    obtain ⟨p, hp⟩ := hgrad0
    let a := pd2 u_plus 0 p
    let b := pd2 u_plus 1 p
    have hab_pos : 0 < a ^ 2 + b ^ 2 := by
      by_cases ha : a = 0
      · have hb : b ≠ 0 := hp ha
        positivity
      · positivity
    let r := Real.sqrt (a ^ 2 + b ^ 2)
    have hr_pos : 0 < r := Real.sqrt_pos.mpr hab_pos
    let c := a / r
    let s := b / r
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      dsimp [c, s]; rw [div_pow, div_pow, ← add_div, Real.sq_sqrt hab_pos.le, div_self hab_pos.ne']
    let rot := rot2_iso c s hcs
    let W (q : Plane2) : ℝ := u_plus (p + rot q)
    obtain ⟨hWc2, hW0, hW1, hWΔ, hWK⟩ := rot2_derivs hu_plus p c s hcs
    have hW_le1 (q : Plane2) : |W q| ≤ 1 := hu_le1 _
    have hW_pde (q : Plane2) : pd22 W 0 0 q + pd22 W 1 1 q + W q - (W q) ^ 3 = 0 := by
      rw [hWΔ q, ← laplacian_sum2 hu_plus]; exact hpde2 _
    have hW_K (q : Plane2) : K_sz W q = 0 := by rw [hWK q]; exact hK0 _
    have hW_stab : ∀ ψ : Plane2 → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        0 ≤ ∫ q : Plane2, (‖∇ ψ q‖ ^ 2 + (3 * (W q) ^ 2 - 1) * (ψ q) ^ 2) :=
      fun ψ hψ hψc => rot2_stability hstab2 p c s hcs hψ hψc
    have hW_A0 : 0 < pd2 W 0 (mk2 0 0) := by
      rw [hW0]; simp only [show mk2 0 0 = 0 by ext i; fin_cases i <;> simp [mk2], map_zero, add_zero]
      have : c * a + s * b = r := by
        dsimp [c, s, a, b]; field_simp [hr_pos.ne']; rw [Real.sq_sqrt hab_pos.le]
      dsimp [a, b] at this; linarith
    have hW_B0 : pd2 W 1 (mk2 0 0) = 0 := by
      rw [hW1]; simp only [show mk2 0 0 = 0 by ext i; fin_cases i <;> simp [mk2], map_zero, add_zero]
      dsimp [c, s, a, b]; ring
    obtain ⟨hW_1d, hW_pos, hW_eq⟩ :=
      nonconstant_1d_heteroclinic hWc2 hW_le1 hW_pde hW_K hW_stab hW_A0 hW_B0
    let q0 : Plane2 := rot.symm p
    let f (t : ℝ) : ℝ := W (mk2 t 0)
    let f' (t : ℝ) : ℝ := pd2 W 0 (mk2 t 0)
    have hV_eq (q : Plane2) : u_plus (rot q) = f (q 0 - q0 0) := by
      have hp_eq : rot q = p + rot (q - q0) := by
        rw [map_sub, LinearIsometryEquiv.apply_symm_apply]; abel
      rw [hp_eq]
      exact hW_1d (q - q0)
    have he2_rot (q : Plane2) : e2_en u_plus (rot q) = (f' (q 0 - q0 0)) ^ 2 := by
      have hp_eq : rot q = p + rot (q - q0) := by
        rw [map_sub, LinearIsometryEquiv.apply_symm_apply]; abel
      have hgrad_eq : (pd2 u_plus 0 (rot q)) ^ 2 + (pd2 u_plus 1 (rot q)) ^ 2 =
          (pd2 W 0 (q - q0)) ^ 2 + (pd2 W 1 (q - q0)) ^ 2 := by
        rw [hW0 (q - q0), hW1 (q - q0), ← hp_eq]
        linear_combination ((pd2 u_plus 0 (rot q)) ^ 2 + (pd2 u_plus 1 (rot q)) ^ 2) * hcs.symm
      have hW0_q : pd2 W 0 (q - q0) = f' (q 0 - q0 0) := by
        have h1 := hasDerivAt_mk2_0 (hWc2.of_le (by norm_num)) ((q - q0) 0) ((q - q0) 1)
        rw [mk2_eta] at h1
        have h2 : HasDerivAt (fun r => W (mk2 r ((q - q0) 1))) (f' (q 0 - q0 0)) ((q - q0) 0) := by
          have heq : (fun r => W (mk2 r ((q - q0) 1))) = f := funext fun r => hW_1d (mk2 r ((q - q0) 1))
          rw [heq]; exact hasDerivAt_mk2_0 (hWc2.of_le (by norm_num)) (q 0 - q0 0) 0
        exact h1.unique h2
      have hW1_q : pd2 W 1 (q - q0) = 0 := by
        have h1 := hasDerivAt_mk2_1 (hWc2.of_le (by norm_num)) ((q - q0) 0) ((q - q0) 1)
        rw [mk2_eta] at h1
        have h2 : HasDerivAt (fun r => W (mk2 ((q - q0) 0) r)) 0 ((q - q0) 1) := by
          have heq : (fun r => W (mk2 ((q - q0) 0) r)) = fun _ => f ((q - q0) 0) :=
            funext fun r => hW_1d (mk2 ((q - q0) 0) r)
          rw [heq]; exact hasDerivAt_const _ _
        exact h1.unique h2
      unfold e2_en
      rw [Fin.sum_univ_two, hgrad_eq, hW0_q, hW1_q, hV_eq q, ← hW_eq (q 0 - q0 0)]
      dsimp [f']; ring
    intro R hR
    have he2_cont : Continuous (e2_en u_plus) := by
      unfold e2_en Wpot
      have h1 (i : Fin 2) : Continuous (pd2 u_plus i) :=
        ((hu_plus.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
      exact (continuous_const.mul (continuous_finsetSum _ fun k _ => (h1 k).pow 2)).add
        (((continuous_const.sub (hu_plus.continuous.pow 2)).pow 2).div_const 4)
    have hsub : rot.symm '' Q2 R ⊆ Q2 (2 * R) := by
      rintro q ⟨y, hy, rfl⟩ i
      rw [Set.mem_Icc, ← abs_le]
      have h1 : |rot.symm y i| ≤ ‖rot.symm y‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (rot.symm y) i
      have h2 : ‖rot.symm y‖ = ‖y‖ := rot.symm.norm_map y
      have h3 : ‖y‖ ≤ |y 0| + |y 1| := by
        have hsq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]; simp [Real.norm_eq_abs]
        have : ‖y‖ ^ 2 ≤ (|y 0| + |y 1|) ^ 2 := by
          rw [hsq, add_sq, sq_abs, sq_abs]; nlinarith [abs_nonneg (y 0), abs_nonneg (y 1)]
        nlinarith [norm_nonneg y, abs_nonneg (y 0), abs_nonneg (y 1)]
      have h4 : |y 0| ≤ R := abs_le.mpr (hy 0)
      have h5 : |y 1| ≤ R := abs_le.mpr (hy 1)
      linarith
    have hpre : rot ⁻¹' Q2 R ⊆ Q2 (2 * R) := fun q hq => hsub ⟨rot q, hq, by simp⟩
    have hmp : MeasurePreserving rot volume volume := rot.measurePreserving
    have hchg : (∫ y in Q2 R, e2_en u_plus y) = ∫ q in rot ⁻¹' Q2 R, e2_en u_plus (rot q) :=
      (hmp.setIntegral_preimage_emb rot.toHomeomorph.measurableEmbedding (e2_en u_plus) (Q2 R)).symm
    rw [hchg]
    have hcomp_Q2 : IsCompact (Q2 (2 * R)) := by
      have h1 : Q2 (2 * R) = (EuclideanSpace.equiv (Fin 2) ℝ).symm ''
          Set.pi Set.univ (fun _ : Fin 2 => Icc (-(2 * R)) (2 * R)) := by
        ext y; constructor
        · intro hy; exact ⟨fun i => y i, fun i _ => hy i, by ext i; simp⟩
        · rintro ⟨g, hg, rfl⟩ i; simpa using hg i (Set.mem_univ i)
      rw [h1]
      exact (isCompact_univ_pi fun _ => isCompact_Icc).image (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous
    have hmono : (∫ q in rot ⁻¹' Q2 R, e2_en u_plus (rot q)) ≤
        ∫ q in Q2 (2 * R), e2_en u_plus (rot q) :=
      setIntegral_mono_set ((he2_cont.comp rot.continuous).continuousOn.integrableOn_compact hcomp_Q2)
        (ae_of_all _ fun q => by dsimp only; rw [he2_rot q]; exact sq_nonneg _) (Eventually.of_forall hpre)
    have hsp := setIntegral_Q2_split (R := 2 * R) (by linarith) (he2_cont.comp rot.continuous)
    dsimp only [Function.comp_def] at hsp
    rw [hsp] at hmono
    have h1d_int : ∀ t : ℝ, (∫ s in Icc (-(2 * R)) (2 * R), e2_en u_plus (rot (mk2 s t))) ≤ 4 / (3 * Real.sqrt 2) := by
      intro t
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      have hcongr : (∫ s in (-(2 * R))..(2 * R), e2_en u_plus (rot (mk2 s t))) =
          ∫ s in (-(2 * R))..(2 * R), (1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2 * f' (s - q0 0) := by
        apply intervalIntegral.integral_congr; intro s _
        dsimp only
        rw [he2_rot (mk2 s t)]
        simp only [mk2_0]
        have hEq := hW_eq (s - q0 0)
        have hpos := hW_pos (s - q0 0)
        have h1m : 0 ≤ 1 - (f (s - q0 0)) ^ 2 := by
          rw [← sq_abs (f (s - q0 0))]; nlinarith [abs_nonneg (f (s - q0 0)), hW_le1 (mk2 (s - q0 0) 0)]
        have hf'_eq : f' (s - q0 0) = (1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2 := by
          have hsq : (f' (s - q0 0)) ^ 2 = ((1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2) ^ 2 := by
            rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; unfold Wpot at hEq; dsimp [f, f'] at hEq ⊢; linarith
          have hnn2 : 0 ≤ (1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2 := by positivity
          nlinarith
        rw [sq, hf'_eq]
      rw [hcongr]
      let F (z : ℝ) : ℝ := (z - z ^ 3 / 3) / Real.sqrt 2
      have hFd (s : ℝ) : HasDerivAt (fun x => F (f (x - q0 0)))
          ((1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2 * f' (s - q0 0)) s := by
        have hF1 : HasDerivAt F ((1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2) (f (s - q0 0)) := by
          dsimp [F]
          exact (((hasDerivAt_id (f (s - q0 0))).fun_sub
            ((hasDerivAt_pow 3 (f (s - q0 0))).div_const 3)).div_const (Real.sqrt 2)).congr_deriv
            (by norm_num)
        have hsub : HasDerivAt (fun x : ℝ => x - q0 0) 1 s := (hasDerivAt_id s).sub_const (q0 0)
        have hf_d : HasDerivAt f (f' (s - q0 0)) (s - q0 0) :=
          hasDerivAt_mk2_0 (hWc2.of_le (by norm_num)) (s - q0 0) 0
        have hfs : HasDerivAt (fun x => f (x - q0 0)) (f' (s - q0 0)) s := by
          have h1 := hf_d.comp s hsub
          simpa only [Function.comp_def, mul_one] using h1
        exact hF1.comp s hfs
      have hfc_i : Continuous (fun s => (1 - (f (s - q0 0)) ^ 2) / Real.sqrt 2 * f' (s - q0 0)) := by
        have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun r =>
          (hasDerivAt_mk2_0 (hWc2.of_le (by norm_num)) r 0).continuousAt
        have hf'_cont : Continuous f' := continuous_iff_continuousAt.mpr fun r =>
          (hasDerivAt_mk2_0 ((hWc2.fderiv_right (by norm_num)).clm_apply contDiff_const) r 0).continuousAt
        have h1 : Continuous (fun s => f (s - q0 0)) := hf_cont.comp (continuous_id.sub continuous_const)
        have h2 : Continuous (fun s => f' (s - q0 0)) := hf'_cont.comp (continuous_id.sub continuous_const)
        exact (((continuous_const.sub (h1.pow 2)).div_const _).mul h2)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hFd s)
        (hfc_i.intervalIntegrable (μ := volume) _ _)]
      have hF_mono (z : ℝ) (hz : |z| ≤ 1) : F (-1) ≤ F z ∧ F z ≤ F 1 := by
        have hFd1 (x : ℝ) : HasDerivAt F ((1 - x ^ 2) / Real.sqrt 2) x :=
          (((hasDerivAt_id x).fun_sub ((hasDerivAt_pow 3 x).div_const 3)).div_const (Real.sqrt 2)).congr_deriv
            (by norm_num)
        have hm := monotoneOn_of_deriv_nonneg (convex_Icc (-1 : ℝ) 1)
          (continuous_iff_continuousAt.mpr fun x => (hFd1 x).continuousAt).continuousOn
          (fun x _ => (hFd1 x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [(hFd1 x).deriv]
            have h1 := interior_subset hx
            have hsq : x ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x, abs_le.mpr h1]
            exact div_nonneg (by linarith) (Real.sqrt_nonneg 2))
        have hz' := abs_le.mp hz
        exact ⟨hm ⟨le_rfl, by norm_num⟩ hz' hz'.1, hm hz' ⟨by norm_num, le_rfl⟩ hz'.2⟩
      have hlo : F (-1) ≤ F (f (-(2 * R) - q0 0)) :=
        (hF_mono (f (-(2 * R) - q0 0)) (hW_le1 (mk2 (-(2 * R) - q0 0) 0))).1
      have hhi : F (f (2 * R - q0 0)) ≤ F 1 :=
        (hF_mono (f (2 * R - q0 0)) (hW_le1 (mk2 (2 * R - q0 0) 0))).2
      have hdiff : F 1 - F (-1) = 4 / (3 * Real.sqrt 2) := by dsimp [F]; ring
      linarith
    have houter : (∫ t in Icc (-(2 * R)) (2 * R), ∫ s in Icc (-(2 * R)) (2 * R), e2_en u_plus (rot (mk2 s t))) ≤
        (4 * R) * (4 / (3 * Real.sqrt 2)) := by
      have hmk_c : Continuous (fun p : ℝ × ℝ => mk2 p.2 p.1) := by
        refine (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp ?_
        rw [continuous_pi_iff]; intro k; fin_cases k
        · exact continuous_snd
        · exact continuous_fst
      have hint_p : IntegrableOn (fun p : ℝ × ℝ => e2_en u_plus (rot (mk2 p.2 p.1)))
          (Icc (-(2 * R)) (2 * R) ×ˢ Icc (-(2 * R)) (2 * R)) volume :=
        ((he2_cont.comp rot.continuous).comp hmk_c).continuousOn.integrableOn_compact
          (isCompact_Icc.prod isCompact_Icc)
      have hint_t : IntegrableOn (fun t : ℝ => ∫ s in Icc (-(2 * R)) (2 * R), e2_en u_plus (rot (mk2 s t)))
          (Icc (-(2 * R)) (2 * R)) volume := by
        have hp : Integrable (fun p : ℝ × ℝ => e2_en u_plus (rot (mk2 p.2 p.1)))
            ((volume.restrict (Icc (-(2 * R)) (2 * R))).prod (volume.restrict (Icc (-(2 * R)) (2 * R)))) := by
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hint_p
        exact hp.integral_prod_left
      have hfin : volume (Icc (-(2 * R)) (2 * R)) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
      have hle := setIntegral_mono_on hint_t (integrableOn_const (C := 4 / (3 * Real.sqrt 2)) hfin)
        measurableSet_Icc (fun t _ => h1d_int t)
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith)] at hle
      calc _ ≤ (2 * R - -(2 * R)) * (4 / (3 * Real.sqrt 2)) := hle
        _ = (4 * R) * (4 / (3 * Real.sqrt 2)) := by ring
    have hconst_le : (4 * R) * (4 / (3 * Real.sqrt 2)) ≤ 4 * R := by
      have h43 : 4 / (3 * Real.sqrt 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        have hsq : (4 : ℝ) ^ 2 ≤ (3 * Real.sqrt 2) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
        nlinarith [Real.sqrt_nonneg 2]
      nlinarith
    linarith

end Mod4b

section Glue
open InnerProductSpace MeasureTheory Filter Set Metric
open scoped Topology Laplacian Gradient

theorem H1_proof : OMA.R_DeGiorgi_DeGiorgi_three_R1.H1 := by
  intro u i hu hpos'
  have hsol : IsBoundedSol u := ⟨hu.regular, hu.bounded, hu.solution⟩
  have hpos : ∀ x, 0 < pd3 u 0 x := fun x => by
    have h := hpos' x
    rw [(hu.regular.differentiable (by norm_num) x).lineDeriv_eq_fderiv] at h
    exact h
  obtain ⟨hu1, C1, C2, C3, hC1, hC2, hC3, hpd1, hpd2, hpd3_lip⟩ := Mod1.exists_C3_bounds hsol
  obtain ⟨u_plus, hu_plus_c2, hu_plus_le1, hpde2, hpd2_le, _hpd22_le, hconv⟩ :=
    Mod2.exists_limit_profile hsol hpos hC1 hC2 hC3 hu1 hpd1 hpd2 hpd3_lip
  obtain ⟨M, hM_nn, hcal⟩ := Mod3.cube_calibration_bound hsol hpos hC1 hu1 hpd1 hu_plus_c2
    (fun R hR ε hε => by
      obtain ⟨T0, hT0⟩ := hconv R hR ε hε
      exact ⟨T0, fun T hT x hx =>
        let h := hT0 T hT x hx
        ⟨h.1, h.2.1, h.2.2.1⟩⟩)
  have hweak3 : ∀ (e : Space) (η : Space → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ x : Space, inner ℝ (∇ (fun z => fderiv ℝ u z e) x) (∇ η x)) +
        (∫ x : Space, η x * ((3 * (u x) ^ 2 - 1) * fderiv ℝ u x e)) = 0 :=
    fun e η hη hηc => OMA.DeGiorgiWeak3.weak_partial hu e hη hηc
  have hstab2 : ∀ φ : Plane2 → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      0 ≤ ∫ y : Plane2, (‖∇ φ y‖ ^ 2 + (3 * (u_plus y) ^ 2 - 1) * (φ y) ^ 2) :=
    fun φ hφ hφc => Mod4a.stability_2d hu.regular hpos hweak3 hu_plus_c2.continuous
      (fun R hR ε hε => by
        obtain ⟨T0, hT0⟩ := hconv R hR ε hε
        exact ⟨T0, fun T hT x hx => (hT0 T hT x hx).1⟩) hφ hφc
  have hweak2 : ∀ (j : Fin 2) (η : Plane2 → ℝ), ContDiff ℝ 1 η → HasCompactSupport η →
      (∫ y : Plane2, inner ℝ (∇ (pd2 u_plus j) y) (∇ η y)) +
        (∫ y : Plane2, η y * ((3 * (u_plus y) ^ 2 - 1) * pd2 u_plus j y)) = 0 :=
    fun j η hη hηc => Mod4a.weak_partial_2d hu.regular hweak3 hu_plus_c2
      (fun R hR ε hε => by
        obtain ⟨T0, hT0⟩ := hconv R hR ε hε
        exact ⟨T0, fun T hT x hx =>
          let h := hT0 T hT x hx
          ⟨h.1, h.2.2.1, fun k => h.2.2.2.1 k.succ, h.2.2.2.2⟩⟩) j hη hηc
  have hK0 : ∀ y : Plane2, K_sz u_plus y = 0 :=
    Mod4a.sternberg_zumbrun_zero hu_plus_c2 hC1 hpd2_le hstab2 hweak2
  have hen2 : ∀ R : ℝ, 0 ≤ R → (∫ y in Q2 R, e2_en u_plus y) ≤ 4 * R :=
    Mod4b.energy_2d_linear_bound hu_plus_c2 hu_plus_le1 hpde2 hstab2 hK0
  have hQ3_bound (R : ℝ) (hR : 2 ≤ R) : (∫ x in Q3 R, e3_en u x) ≤ (8 + M) * R ^ 2 := by
    have h1 := hcal R hR
    have h2 := hen2 R (by linarith)
    nlinarith
  refine ⟨8 * (8 + M), fun R hR1 => ?_⟩
  let R' : ℝ := max R 2
  have hR'2 : 2 ≤ R' := le_max_right R 2
  have hR'le : R' ≤ 2 * R := max_le (by linarith) (by linarith)
  have hball_sub : Metric.ball (0 : Space) R ⊆ Q3 R' := by
    intro x hx k
    rw [Metric.mem_ball, dist_zero_right] at hx
    rw [Set.mem_Icc, ← abs_le]
    have h1 : |x k| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x k
    exact (h1.trans hx.le).trans (le_max_left R 2)
  have hpd_cont : Continuous (fun x : Space => (pd3 u i x) ^ 2) :=
    (((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2
  have he3_cont : Continuous (e3_en u) := by
    unfold e3_en Wpot
    have hc (k : Fin 3) : Continuous (pd3 u k) :=
      ((hu.regular.of_le (by norm_num)).continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact (continuous_const.mul (continuous_finsetSum _ fun k _ => (hc k).pow 2)).add
      (((continuous_const.sub (hu.regular.continuous.pow 2)).pow 2).div_const 4)
  have hpt (x : Space) : (pd3 u i x) ^ 2 ≤ 2 * e3_en u x := by
    unfold e3_en Wpot
    have hsum : (pd3 u i x) ^ 2 ≤ ∑ k : Fin 3, (pd3 u k x) ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (pd3 u k x)) (Finset.mem_univ i)
    have hW : 0 ≤ (1 - (u x) ^ 2) ^ 2 / 4 := by positivity
    linarith
  have hInt_pd : IntegrableOn (fun x : Space => (pd3 u i x) ^ 2) (Q3 R') volume :=
    hpd_cont.continuousOn.integrableOn_compact (isCompact_Q3 R')
  have hInt_e3 : IntegrableOn (e3_en u) (Q3 R') volume :=
    he3_cont.continuousOn.integrableOn_compact (isCompact_Q3 R')
  have h1 : (∫ x in Metric.ball (0 : Space) R, (pd3 u i x) ^ 2) ≤ ∫ x in Q3 R', (pd3 u i x) ^ 2 :=
    setIntegral_mono_set hInt_pd (ae_of_all _ fun x => sq_nonneg _) (Eventually.of_forall hball_sub)
  have h2 : (∫ x in Q3 R', (pd3 u i x) ^ 2) ≤ ∫ x in Q3 R', 2 * e3_en u x :=
    setIntegral_mono_on hInt_pd (hInt_e3.const_mul 2) (isCompact_Q3 R').isClosed.measurableSet (fun x _ => hpt x)
  rw [integral_const_mul] at h2
  have h3 := hQ3_bound R' hR'2
  have hR'sq : R' ^ 2 ≤ 4 * R ^ 2 := by nlinarith
  have h8M : 0 ≤ 8 + M := by linarith
  calc (∫ x in Metric.ball (0 : Space) R, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2)
      ≤ 2 * (∫ x in Q3 R', e3_en u x) := h1.trans h2
    _ ≤ 2 * ((8 + M) * R' ^ 2) := by linarith
    _ ≤ 2 * ((8 + M) * (4 * R ^ 2)) := by nlinarith
    _ = 8 * (8 + M) * R ^ 2 := by ring

end Glue

end OMA.DeGiorgiC

theorem OMA.solution : type_of% @DeGiorgi.DeGiorgi_three :=
  OMA.R_DeGiorgi_DeGiorgi_three_R1.main
    OMA.DeGiorgiC.H1_proof
    (fun u i hu hpos => OMA.DeGiorgiWeak3.solution u i hu hpos)
    OMA.SpaceLiouville.constant_of_weak_divergence
