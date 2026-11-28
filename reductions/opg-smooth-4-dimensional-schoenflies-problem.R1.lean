import OMAStatements.S_opg_smooth_4_dimensional_schoenflies_problem

/-!
# Rational polynomial paths for the smooth four-dimensional Schoenflies problem

A chord bound on a polynomial segment bounds every tangent vector from below.
At each time, smooth inverse coordinates on the current sphere extend to the whole
ambient space. They turn a small change of the time parameter into a smooth
perturbation of the identity with Lipschitz error strictly below one. Connectedness
of the unit interval then transports the ambient diffeomorphism class along the segment.

The two remaining inputs are Euclidean polynomial approximation (H1) and the existence
of a finite chain of rational polynomial segments with certified chord bounds (H2).

-- Credit: @yuka30240
-/

open Set Metric Function Filter
open scoped Manifold ContDiff NNReal Topology

namespace OMA.R_opg_smooth_4_dimensional_schoenflies_problem_R1

/-- Rational polynomial approximation in the value and first derivative on one fixed ball. -/
def H1 : Prop :=
  let E := EuclideanSpace ℝ (Fin 4)
  ∀ g : E → E, ContDiff ℝ ∞ g → HasCompactSupport g → ∀ δ : ℝ, 0 < δ →
    ∃ P : Fin 4 → MvPolynomial (Fin 4) ℚ,
      let error := fun x : E => WithLp.toLp 2 (fun i => MvPolynomial.aeval x.ofLp (P i)) - g x
      ∀ x ∈ closedBall (0 : E) 2, ‖error x‖ ≤ δ ∧ ‖fderiv ℝ error x‖ ≤ δ

/-- Link a round rational polynomial parametrization to the given one by finitely many
straight segments with a uniform lower chord bound on each segment. Squaring the
distance inequalities yields polynomial inequalities on pairs of unit vectors. -/
def H2 : Prop :=
  let E := EuclideanSpace ℝ (Fin 4)
  let S := sphere (0 : E) 1
  let Poly := Fin 4 → MvPolynomial (Fin 4) ℚ
  let ev := fun (P : Poly) (x : S) =>
    WithLp.toLp 2 (fun i => MvPolynomial.aeval x.val.ofLp (P i))
  let bound := fun (N : ℕ) (f : S → E) =>
    ∀ x y : S, dist x.val y.val ≤ (N : ℝ) * dist (f x) (f y)
  ∀ P, (∃ N, bound N (ev P)) →
    ∃ Q, range (ev Q) = S ∧
      Relation.ReflTransGen (fun A B => ∃ N, ∀ t ∈ Icc (0 : ℝ) 1,
        bound N (fun x => ev A x + t • (ev B x - ev A x))) Q P

/-- A smooth perturbation of the identity with Lipschitz error strictly below one
is globally invertible, with smooth inverse. -/
theorem small_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Nontrivial E] {u : E → E} {C : ℝ≥0}
    (hu : ContDiff ℝ ∞ u) (hlip : LipschitzWith C u) (hC : C < 1) :
    ∃ F : E ≃ₘ[ℝ] E, ∀ x, F x = x + u x := by
  let T : E → E := fun x => x + u x
  let I := ContinuousLinearEquiv.refl ℝ E
  have hT : ApproximatesLinearOn T (I : E →L[ℝ] E) univ C := by
    apply LipschitzOnWith.approximatesLinearOn
    simpa [T, I, Pi.sub_def] using hlip.lipschitzOnWith (s := (univ : Set E))
  have hI : C < ‖(I.symm : E →L[ℝ] E)‖₊⁻¹ := by
    simpa [I] using hC
  let e := hT.toHomeomorph T (Or.inr hI)
  have he (x : E) : e x = T x := rfl
  have differential (x : E) : ‖-fderiv ℝ u x‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz ℝ hlip).trans_lt (show (C : ℝ) < 1 from hC)
  let L := fun x => ContinuousLinearEquiv.ofUnit (Units.oneSub _ (differential x))
  have hL (x : E) : (L x : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E + fderiv ℝ u x := by
    change ((Units.oneSub _ (differential x) : (E →L[ℝ] E)ˣ) : E →L[ℝ] E) = _
    rw [Units.val_oneSub, sub_neg_eq_add, ContinuousLinearMap.one_def]
  have hs : ContDiff ℝ ∞ (e : E → E) := contDiff_id.add hu
  have hd (x : E) : HasFDerivAt e (L x : E →L[ℝ] E) x := by
    rw [hL]
    exact (hasFDerivAt_id x).add ((hu.differentiable (by simp)) x).hasFDerivAt
  exact ⟨⟨e.toEquiv, hs.contMDiff, (e.contDiff_symm hd hs).contMDiff⟩, he⟩

theorem polynomial_smooth (P : Fin 4 → MvPolynomial (Fin 4) ℚ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) =>
      WithLp.toLp 2 (fun i => MvPolynomial.aeval x.ofLp (P i))) := by
  apply (contDiff_piLp 2).2
  intro i
  change ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 4) => MvPolynomial.aeval x.ofLp (P i))
  induction P i using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const (c := (algebraMap ℚ ℝ a)) :
                ContDiff ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin 4) => algebraMap ℚ ℝ a))
  | add _ _ hp hq => simpa only [map_add] using hp.add hq
  | mul_X _ j hp =>
    simpa only [map_mul, MvPolynomial.aeval_X] using hp.mul (contDiff_piLp_apply (i := j) (p := 2))

/-- The manifold derivative in a sphere chart, with Euclidean target. -/
theorem sphere_chart_derivative {f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
    EuclideanSpace ℝ (Fin 4)} (hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f) (x) :
    HasFDerivAt (f ∘ (extChartAt (𝓡 3) x).symm)
      (show EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4) from
        mfderiv (𝓡 3) (𝓡 4) f x)
      (extChartAt (𝓡 3) x x) := by
  rw [← hasFDerivWithinAt_univ]
  have hd := ((hf.mdifferentiable (by simp) x).hasMFDerivAt).2
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    id_comp, modelWithCornersSelf_coe, range_id] at hd
  exact hd

/-- A lower bound on all chord lengths of a smooth sphere map implies injectivity on
each tangent space. Apply the chord inequality to difference quotients in a chart. -/
theorem regular_of_chords {f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
    EuclideanSpace ℝ (Fin 4)} {C : ℝ≥0}
    (hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f) (hc : AntilipschitzWith C f) (x) :
    Injective (mfderiv (𝓡 3) (𝓡 4) f x) := by
  let E := EuclideanSpace ℝ (Fin 4)
  let S := sphere (0 : E) 1
  let incl := (Subtype.val : S → E)
  let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] E := mfderiv (𝓡 3) (𝓡 4) incl x
  let G : EuclideanSpace ℝ (Fin 3) →L[ℝ] E := mfderiv (𝓡 3) (𝓡 4) f x
  have hD : Injective D := injective_mvfderiv_subtypeVal_sphere (n := 3) x
  change Injective G
  apply (LinearMap.ker_eq_bot (f := G.toLinearMap)).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hz
  change G v = 0 at hz
  let e := extChartAt (𝓡 3) x
  let curve := fun t : ℝ => e.symm (e x + t • (v : EuclideanSpace ℝ (Fin 3)))
  have h₁ : HasDerivAt (incl ∘ curve) (D v) 0 :=
    (sphere_chart_derivative (contMDiff_coe_sphere (n := 3)) x).hasLineDerivAt v
  have h₂ : HasDerivAt (f ∘ curve) (G v) 0 :=
    (sphere_chart_derivative hf x).hasLineDerivAt v
  have bound : ‖D v‖ ≤ (C : ℝ) * ‖G v‖ := by
    apply le_of_tendsto_of_tendsto' h₁.tendsto_slope_zero.norm
      (tendsto_const_nhds.mul h₂.tendsto_slope_zero.norm)
    intro t
    simp only [norm_smul, zero_add, Function.comp_apply]
    rw [mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [dist_eq_norm, Subtype.dist_eq, incl] using hc.le_mul_dist (curve t) (curve 0)
  rw [hz, norm_zero, mul_zero, norm_le_zero_iff] at bound
  exact hD (bound.trans (map_zero D).symm)

/-- At an invertible derivative, smoothness on a neighborhood gives a local inverse
which is smooth on a neighborhood of the image point. -/
theorem smooth_local_inverse {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {g : V → V} {a : V}
    (hg : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ g z)
    (hD : HasFDerivAt g (ContinuousLinearMap.id ℝ V) a) :
    ∃ r : V → V, (∀ᶠ z in 𝓝 (g a), ContDiffAt ℝ ∞ r z) ∧
      ∀ᶠ z in 𝓝 a, r (g z) = z := by
  let I := ContinuousLinearEquiv.refl ℝ V
  have h₀ := hg.self_of_nhds
  let e := h₀.toOpenPartialHomeomorph g (f' := I) hD (by simp)
  have src : a ∈ e.source := h₀.mem_toOpenPartialHomeomorph_source hD (f' := I) (by simp)
  have tgt : g a ∈ e.target := e.map_source src
  have cont : Tendsto e.symm (𝓝 (g a)) (𝓝 a) := by
    simpa only [show e.symm (g a) = a from e.left_inv src] using (e.continuousAt_symm tgt).tendsto
  have invertible : ∀ᶠ z in 𝓝 a,
      fderiv ℝ g z ∈ range ((↑) : (V ≃L[ℝ] V) → (V →L[ℝ] V)) := by
    apply (h₀.continuousAt_fderiv (by simp)).preimage_mem_nhds
    rw [hD.fderiv]
    exact ContinuousLinearEquiv.nhds I
  refine ⟨e.symm, ?_, ?_⟩
  rotate_left
  · filter_upwards [e.open_source.mem_nhds src] with z hz using e.left_inv hz
  filter_upwards [e.open_target.mem_nhds tgt, cont.eventually hg, cont.eventually invertible]
    with y hy hgy hunit
  obtain ⟨A, hA⟩ := hunit
  apply e.contDiffAt_symm hy (f₀' := A) _ hgy
  rw [hA]
  exact (hgy.differentiableAt (by simp)).hasFDerivAt

/-- Project the derivative to a left inverse, invert the square map in source
coordinates, then evaluate the data in that chart. -/
theorem local_extension {f u : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
    EuclideanSpace ℝ (Fin 4)} (hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f)
    (hu : ContMDiff (𝓡 3) (𝓡 4) ∞ u) (x)
    (hinj : Injective (mfderiv (𝓡 3) (𝓡 4) f x)) :
    ∃ k : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4),
      (∀ᶠ y in 𝓝 (f x), ContDiffAt ℝ ∞ k y) ∧ ∀ᶠ z in 𝓝 x, k (f z) = u z := by
  let V := EuclideanSpace ℝ (Fin 3)
  let E := EuclideanSpace ℝ (Fin 4)
  let e := extChartAt (𝓡 3) x
  let a : V := e x
  let p : V → E := f ∘ e.symm
  let q : V → E := u ∘ e.symm
  let D : V →L[ℝ] E := mfderiv (𝓡 3) (𝓡 4) f x
  let L : E →L[ℝ] V := D.toLinearMap.leftInverse.toContinuousLinearMap
  have left : L.comp D = ContinuousLinearMap.id ℝ V := by
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.leftInverse_apply_of_inj (f := D.toLinearMap) (LinearMap.ker_eq_bot.mpr hinj) v
  have germs : ∀ᶠ z in 𝓝 a, ContDiffAt ℝ ∞ p z ∧ ContDiffAt ℝ ∞ q z := by
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓡 3) x] with z hz
    have hs : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm z := by
      exact (contMDiffWithinAt_extChartAt_symm_target (I := 𝓡 3) x hz).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3) x).mem_nhds hz)
    exact ⟨((hf _).comp z hs).contDiffAt, ((hu _).comp z hs).contDiffAt⟩
  have hD : HasFDerivAt (L ∘ p) (ContinuousLinearMap.id ℝ V) a := by
    rw [← left]
    exact L.hasFDerivAt.comp a (sphere_chart_derivative hf x)
  obtain ⟨r, hr, hrp⟩ := smooth_local_inverse
    (germs.mono fun z hz => L.contDiff.contDiffAt.comp z hz.1) hD
  have hpx : p a = f x := congrArg f (e.left_inv (mem_extChartAt_source x))
  change ∀ᶠ y in 𝓝 (L (p a)), ContDiffAt ℝ ∞ r y at hr
  rw [hpx] at hr
  have hra : r (L (f x)) = a := by simpa only [comp_apply, hpx] using hrp.self_of_nhds
  have hrL : Tendsto (r ∘ L) (𝓝 (f x)) (𝓝 a) := by
    simpa only [comp_apply, hra] using
      (hr.self_of_nhds.continuousAt.comp L.continuous.continuousAt).tendsto
  refine ⟨q ∘ r ∘ L, ?_, ?_⟩
  · filter_upwards [L.continuous.continuousAt.tendsto.eventually hr,
      hrL.eventually germs] with y hy hq
    have hyr : ContDiffAt ℝ ∞ r (L y) := hy
    exact hq.2.comp y (hyr.comp y L.contDiff.contDiffAt)
  · filter_upwards [(continuousAt_extChartAt (I := 𝓡 3) x).tendsto.eventually hrp,
      extChartAt_source_mem_nhds (I := 𝓡 3) x] with z hz hsrc
    have he := e.left_inv hsrc
    change r (L (f (e.symm (e z)))) = e z at hz
    rw [he] at hz
    change u (e.symm (r (L (f z)))) = u z
    rw [hz, he]

/-- Extend smooth vector-valued data from an embedded sphere with compact support.
Local extensions agree on the image, so a partition of unity preserves their values. -/
theorem sphere_extension {f u : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
    EuclideanSpace ℝ (Fin 4)} (hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f)
    (hi : Injective f) (hd : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 4) f x))
    (hu : ContMDiff (𝓡 3) (𝓡 4) ∞ u) :
    ∃ k : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4),
      ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧ ∀ x, k (f x) = u x := by
  let E := EuclideanSpace ℝ (Fin 4)
  let T := fun y : E => {w : E | ∀ x, f x = y → w = u x}
  have conv (y) : Convex ℝ (T y) := by
    intro v hv w hw a b ha hb hab x hx
    rw [hv x hx, hw x hx, ← add_smul, hab, one_smul]
  have emb := hf.continuous.isClosedEmbedding hi
  have local_data (y : E) : ∃ U ∈ 𝓝 y, ∃ k : E → E,
      ContMDiffOn (𝓡 4) (𝓡 4) ∞ k U ∧ ∀ z ∈ U, k z ∈ T z := by
    by_cases hy : y ∈ range f
    · obtain ⟨x, rfl⟩ := hy
      obtain ⟨k, hs, heq⟩ := local_extension hf hu x (hd x)
      rw [emb.isEmbedding.isInducing.nhds_eq_comap x] at heq
      obtain ⟨W, hW, hw⟩ := Filter.mem_comap.mp heq
      refine ⟨W ∩ {z | ContDiffAt ℝ ∞ k z}, inter_mem hW hs, k, ?_, ?_⟩
      · intro z hz
        exact (show ContDiffAt ℝ ∞ k z from hz.2).contMDiffAt.contMDiffWithinAt
      · rintro z hz v rfl
        exact hw hz.1
    · refine ⟨(range f)ᶜ, emb.isClosed_range.isOpen_compl.mem_nhds hy,
        fun _ => 0, contMDiffOn_const, ?_⟩
      rintro z hz v rfl
      exact (hz (mem_range_self v)).elim
  obtain ⟨k, hk⟩ := exists_contMDiffMap_forall_mem_convex_of_local (𝓡 4)
    (t := T) (n := ⊤) conv local_data
  obtain ⟨R, hR, hball⟩ := (isCompact_range hf.continuous).isBounded.subset_ball_lt 0 (0 : E)
  let bump : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by simp⟩
  refine ⟨fun y => bump y • k y, bump.contDiff.smul k.contMDiff.contDiff,
    bump.hasCompactSupport.smul_right, ?_⟩
  intro x
  change bump (f x) • k (f x) = u x
  rw [bump.one_of_mem_closedBall (ball_subset_closedBall (hball (mem_range_self x))),
    one_smul]
  exact hk (f x) x rfl

/-- Cut off the polynomial approximation error. Its value and derivative bounds on
the radius-two ball give the requested global Lipschitz constant. -/
theorem approximation_error (approx : H1)
    {f : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → EuclideanSpace ℝ (Fin 4)}
    (hf : ContMDiff (𝓡 3) (𝓡 4) ∞ f) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (P : Fin 4 → MvPolynomial (Fin 4) ℚ) (u : EuclideanSpace ℝ (Fin 4) →
        EuclideanSpace ℝ (Fin 4)), ContDiff ℝ ∞ u ∧ LipschitzWith ε u ∧
      ∀ x, f x + u x.val = WithLp.toLp 2 (fun i => MvPolynomial.aeval x.val.ofLp (P i)) := by
  let E := EuclideanSpace ℝ (Fin 4)
  obtain ⟨g, hg, hc, hgf⟩ := sphere_extension (contMDiff_coe_sphere (n := 3)) Subtype.val_injective
    (fun x => injective_mvfderiv_subtypeVal_sphere (n := 3) x) hf
  let χ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  obtain ⟨B, hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport χ.hasCompactSupport
    (χ.contDiff : ContDiff ℝ ∞ _) (by simp)
  let δ : ℝ := ε / ((B : ℝ) + 1)
  have hden : 0 < (B : ℝ) + 1 := by positivity
  have hδ : 0 < δ := div_pos (show (0 : ℝ) < ε from hε) hden
  obtain ⟨P, hP⟩ := approx g hg hc δ hδ
  let err := fun x : E => WithLp.toLp 2 (fun i => MvPolynomial.aeval x.ofLp (P i)) - g x
  have he : ContDiff ℝ ∞ err := (polynomial_smooth P).sub hg
  let u := fun x => χ x • err x
  have hu : ContDiff ℝ ∞ u := χ.contDiff.smul he
  refine ⟨P, u, hu, ?_, ?_⟩
  · apply lipschitzWith_of_nnnorm_fderiv_le (hu.differentiable (by simp))
    intro x
    change ‖fderiv ℝ u x‖ ≤ (ε : ℝ)
    by_cases hx : x ∈ closedBall (0 : E) 2
    · obtain ⟨hv, hd⟩ := hP x hx
      have hχ : ‖χ x‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg χ.nonneg]; exact χ.le_one
      rw [show fderiv ℝ u x = χ x • fderiv ℝ err x + (fderiv ℝ χ x).smulRight (err x) from
        fderiv_fun_smul (χ.contDiff.differentiable (n := ∞) (by simp) x) (he.differentiable (by simp) x)]
      calc
        _ ≤ ‖χ x • fderiv ℝ err x‖ + ‖(fderiv ℝ χ x).smulRight (err x)‖ := norm_add_le _ _
        _ ≤ 1 * δ + (B : ℝ) * δ := by
          rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
          exact add_le_add (mul_le_mul hχ hd (norm_nonneg _) zero_le_one)
            (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hB) hv (norm_nonneg _) B.coe_nonneg)
        _ = (ε : ℝ) := by dsimp [δ]; field_simp; ring
    · have heq : u =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        change χ y • err y = 0
        rw [χ.zero_of_le_dist (le_of_lt (lt_of_not_ge hy)), zero_smul]
      simpa only [heq.fderiv_eq, fderiv_fun_const, Pi.zero_apply, norm_zero] using ε.coe_nonneg
  · intro x
    have hx : x.val ∈ closedBall (0 : E) χ.rIn := sphere_subset_closedBall x.property
    change f x + χ x.val • err x.val = _
    rw [χ.one_of_mem_closedBall hx, one_smul]
    dsimp only [err]
    rw [hgf x]
    abel

/-- A smooth map composed with a compactly supported smooth map is constant off a
compact set. Subtract its value there to obtain a global Lipschitz bound. -/
theorem lipschitz_compact_inner {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v k : E → E} (hv : ContDiff ℝ ∞ v) (hk : ContDiff ℝ ∞ k) (hc : HasCompactSupport k) :
    ∃ C, LipschitzWith C (v ∘ k) := by
  have hs : HasCompactSupport (fun x => v (k x) - v 0) :=
    hc.comp_left (g := fun y => v y - v 0) (sub_self _)
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs
    ((hv.comp hk).sub contDiff_const) (by simp)
  refine ⟨C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simpa only [Function.comp_apply, dist_sub_right] using hC.dist_le_mul x y

theorem transport_range {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) {f g : α → E} (F : E ≃ₘ[ℝ] E) (h : ∀ x, F (f x) = g x)
    (hround : ∃ A : E ≃ₘ[ℝ] E, A '' s = range f) :
    ∃ B : E ≃ₘ[ℝ] E, B '' s = range g := by
  obtain ⟨A, hA⟩ := hround
  refine ⟨A.trans F, ?_⟩
  rw [Diffeomorph.coe_trans, Set.image_comp, hA, ← Set.range_comp]
  exact congrArg range (funext h)

/-- The ambient diffeomorphism class is locally constant along a straight segment
which stays in the space of smooth embeddings. -/
theorem transport_segment
    (a b : EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hreg : ∃ N : ℕ, ∀ t ∈ Icc (0 : ℝ) 1,
      let f := fun x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 =>
        a x + t • (b x - a x)
      ∀ x y, dist x.val y.val ≤ (N : ℝ) * dist (f x) (f y)) :
    let E := EuclideanSpace ℝ (Fin 4)
    let S := sphere (0 : E) 1
    (∃ A : E ≃ₘ[ℝ] E, A '' S = range (fun x : S => a x)) →
    ∃ B : E ≃ₘ[ℝ] E, B '' S = range (fun x : S => b x) := by
  let E := EuclideanSpace ℝ (Fin 4)
  let S := sphere (0 : E) 1
  let f := fun (t : unitInterval) (x : S) => a x + (t : ℝ) • (b x - a x)
  let round := fun t => ∃ A : E ≃ₘ[ℝ] E, A '' S = range (f t)
  have stable : IsLocallyConstant round := by
    apply (IsLocallyConstant.iff_eventually_eq round).2
    intro t
    have smooth : ContMDiff (𝓡 3) (𝓡 4) ∞ (f t) :=
      (ha.add ((contDiff_const (c := (t : ℝ))).smul (hb.sub ha))).contMDiff.comp
        (contMDiff_coe_sphere (n := 3))
    obtain ⟨N, hN⟩ := hreg
    have lower : AntilipschitzWith (N : ℝ≥0) (f t) :=
      AntilipschitzWith.of_le_mul_dist (hN t t.property)
    obtain ⟨k, hk, hc, hcoords⟩ := sphere_extension smooth lower.injective
      (regular_of_chords smooth lower) (contMDiff_coe_sphere (n := 3))
    obtain ⟨L, hL⟩ := lipschitz_compact_inner (hb.sub ha) hk hc
    have nearby : ∀ᶠ s : unitInterval in 𝓝 t, ‖(s : ℝ) - (t : ℝ)‖₊ * L < 1 := by
      have cont : Continuous (fun s : unitInterval => ‖(s : ℝ) - (t : ℝ)‖₊ * L) := by fun_prop
      exact cont.continuousAt.eventually_lt continuousAt_const (by simp)
    filter_upwards [nearby] with s hs
    let w := fun y => ((s : ℝ) - (t : ℝ)) • (b (k y) - a (k y))
    obtain ⟨F, hF⟩ := small_perturbation (u := w)
      ((contDiff_const (c := (s : ℝ) - (t : ℝ))).smul ((hb.comp hk).sub (ha.comp hk)))
      ((lipschitzWith_smul ((s : ℝ) - (t : ℝ))).comp hL) hs
    have step (x : S) : F (f t x) = f s x := by
      rw [hF]
      dsimp only [w]
      rw [hcoords]
      simp only [f, sub_smul]
      abel
    apply propext
    exact ⟨transport_range S F.symm (fun x => by rw [← step, F.symm_apply_apply]),
      transport_range S F step⟩
  change (∃ A : E ≃ₘ[ℝ] E, A '' S = range (fun x : S => a x)) →
    ∃ B : E ≃ₘ[ℝ] E, B '' S = range (fun x : S => b x)
  intro hround
  have start : round 0 := by simpa [round, f] using hround
  have finish : round 1 := (stable.apply_eq_of_preconnectedSpace 0 1).mp start
  simpa [round, f, add_comm] using finish

theorem main : H1 → H2 → type_of% @OMA.S_opg_smooth_4_dimensional_schoenflies_problem.main := by
  intro approx chains f hf hinj htangent
  let E := EuclideanSpace ℝ (Fin 4)
  let S := sphere (0 : E) 1
  let Poly := Fin 4 → MvPolynomial (Fin 4) ℚ
  let eval := fun (p : Poly) (x : E) => WithLp.toLp 2 (fun i => MvPolynomial.aeval x.ofLp (p i))
  let ev := fun (p : Poly) (x : S) => eval p x.val
  let round := fun (p : Poly) => ∃ A : E ≃ₘ[ℝ] E, A '' S = range (ev p)

  obtain ⟨k, hk, hc, coords⟩ := sphere_extension hf hinj htangent (contMDiff_coe_sphere (n := 3))
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hk (by simp)
  have hpos : 0 < K + 1 := by positivity
  let ε := (K + 1)⁻¹
  have small : ε * K < 1 := (inv_mul_lt_one₀ hpos).2 (by simp)
  obtain ⟨P, u, hu, hlip, hP⟩ := approximation_error approx hf ε (inv_pos.mpr hpos)
  obtain ⟨F, hF⟩ := small_perturbation (hu.comp hk) (hlip.comp hK) small
  have move (x : S) : F (f x) = ev P x := by
    rw [hF, comp_apply, coords]
    exact hP x

  have lower : AntilipschitzWith K f := by
    apply AntilipschitzWith.of_le_mul_dist
    intro x y
    simpa only [coords, Subtype.dist_eq] using hK.dist_le_mul (f x) (f y)
  have perturbed := AntilipschitzWith.id.add_lipschitzWith (hlip.comp hK) (by simpa using small)
  have hbound : ∃ N : ℕ, ∀ x y : S, dist x.val y.val ≤ (N : ℝ) * dist (ev P x) (ev P y) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ((K * ((1 : ℝ≥0)⁻¹ - ε * K)⁻¹ : ℝ≥0) : ℝ)
    refine ⟨N, fun x y => ?_⟩
    have hxy := (perturbed.comp lower).le_mul_dist x y
    change dist x.val y.val ≤ _ * dist (f x + u (k (f x))) (f y + u (k (f y))) at hxy
    rw [coords, coords, hP, hP] at hxy
    exact hxy.trans (mul_le_mul_of_nonneg_right hN dist_nonneg)
  obtain ⟨Q, hQ, chain⟩ := chains P hbound
  have base : round Q := by
    refine ⟨Diffeomorph.refl (𝓡 4) E ∞, ?_⟩
    simpa [Diffeomorph.coe_refl] using hQ.symm
  have hpoly : round P := by
    clear hP move hbound
    induction chain with
    | refl => exact base
    | tail path edge ih =>
      exact transport_segment _ _ (polynomial_smooth _) (polynomial_smooth _) edge ih
  exact transport_range S F.symm (fun x => by rw [← move, F.symm_apply_apply]) hpoly

end OMA.R_opg_smooth_4_dimensional_schoenflies_problem_R1
