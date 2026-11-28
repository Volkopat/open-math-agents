import OMAReductions.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1

/-!
Four equilibria suffice as an upper bound for three noncollinear charges
when all nonsource equilibria are nondegenerate. The planar index count
reduces the proof to uniqueness of a planar extremum. In each admissible
barycentric chamber, the normal of the critical image parametrizes the
source boundary. The three-cusp bound makes that image simple. Local
uniqueness on the positive sheet follows by eliminating one transverse
force equation. Compactness then gives global injectivity on the sheet.
-/

section

namespace MaxwellIndexCount

open Arxiv.«2607.27197» InnerProductSpace Filter Set
open scoped BigOperators Gradient RealInnerProductSpace Topology

private abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The moment of a neutral nonzero charge distribution on independent sites is nonzero. -/
theorem neutral_dipole_ne_zero (a : Fin 3 → E) (q : Fin 3 → ℝ)
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (hQ : ∑ i, q i = 0) :
    ∑ i, q i • a i ≠ 0 := by
  intro h
  apply hq
  apply (affineIndependent_iff_of_fintype ℝ a).1 ha q hQ
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hQ (0 : E)]
  simpa [Finset.weightedVSubOfPoint_apply] using h

/-- Squared norm of the dipole field on the unit sphere. -/
theorem dipole_norm_sq (p e : E) (he : ‖e‖ = 1) :
    ‖p - (3 * ⟪e, p⟫_ℝ) • e‖ ^ 2 = ‖p‖ ^ 2 + 3 * ⟪e, p⟫_ℝ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he, real_inner_comm p e]
  ring

/-- A regular equilibrium is isolated in the full ambient space. -/
theorem equilibria_discrete (q : Fin 3 → ℝ) (a : Fin 3 → E)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) :
    IsDiscrete (equilibria q a) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  let V := potential q a
  let H := fderiv ℝ (fderiv ℝ V) x
  have hker : H.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    by_contra h
    obtain ⟨w, hw⟩ := hnd x hx v h
    apply hw
    simpa [iteratedFDeriv_two_apply, H, V] using congrArg (fun l : E →L[ℝ] ℝ => l w) hv
  have hdim := (toDual ℝ E).toLinearEquiv.finrank_eq
  let L := ContinuousLinearEquiv.ofBijective H hker
    ((LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank hdim).mp hker)
  have hs : ContDiffAt ℝ 2 V x := by
    apply ContDiffAt.sum
    intro i _
    exact contDiffAt_const.div (contDiffAt_id.dist ℝ contDiffAt_const
      (fun h => hx.1 ⟨i, h.symm⟩)) (dist_ne_zero.mpr fun h => hx.1 ⟨i, h.symm⟩)
  have hd : ContDiffAt ℝ 1 (fderiv ℝ V) x := hs.fderiv_right (by norm_num)
  have hl : HasStrictFDerivAt (fderiv ℝ V) (L : E →L[ℝ] (E →L[ℝ] ℝ)) x :=
    hd.hasStrictFDerivAt (by norm_num)
  let U := hl.toOpenPartialHomeomorph (fderiv ℝ V)
  have hxU : x ∈ U.source := hl.mem_toOpenPartialHomeomorph_source
  refine ⟨U.source, U.open_source, Set.ext fun y => ?_⟩
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  refine ⟨fun ⟨hyU, hy⟩ => U.injOn hyU hxU ?_, fun h => h ▸ ⟨hxU, hx⟩⟩
  change fderiv ℝ V y = fderiv ℝ V x
  exact (toDual ℝ E).symm.injective (hy.2.trans hx.2.symm)

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem norm_sub_derivative {a x : V} (hne : x ≠ a) :
    HasFDerivAt (fun y : V => ‖y - a‖) (‖x - a‖⁻¹ • innerSL ℝ (x - a)) x := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hs : HasFDerivAt (fun y : V => ‖y - a‖ ^ 2)
      (2 • innerSL ℝ (x - a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq

  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp [hn]
    norm_num

end

/-- Differentiate a single Coulomb term away from its source.
The differentiation argument follows @harshshah1618's Open Math Agents PR 289. -/
private theorem coulomb_hasGradient (q : ℝ) {a x : E} (hne : x ≠ a) :
    HasGradientAt (fun y : E => q / dist y a)
      ((-q / ‖x - a‖ ^ 3) • (x - a)) x := by
  have hn : ‖x - a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hd := norm_sub_derivative hne
  have hderiv := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hderiv using 1
  ext v
  simp [toDual_apply_apply, div_eq_mul_inv, smul_smul]
  field_simp [hn]
  simp

theorem potential_gradient (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E)
    (hx : x ∉ Set.range a) :
    HasGradientAt (potential q a) (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  unfold potential
  rw [map_sum]
  exact HasFDerivAt.fun_sum fun i _ =>
    (coulomb_hasGradient (q i) (fun h => hx ⟨i, h.symm⟩)).hasFDerivAt

/-- The explicit force vanishes exactly at the nonsource equilibria. -/
theorem mem_equilibria_iff (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) :
    x ∈ equilibria q a ↔ x ∉ Set.range a ∧
      (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) = 0 := by
  change (_ ∧ _) ↔ _
  exact and_congr_right fun hx => by rw [(potential_gradient q a x hx).gradient]

private theorem continuous_sum_at {W : Type*} [NormedAddCommGroup W] {X : Type*} [TopologicalSpace X] {x : X}
    {s : Finset (Fin 3)} {f : Fin 3 → X → W} (h : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := tendsto_finsetSum _ h

/-- Continuity of the remaining charges rules out accumulating equilibria at a site. -/
theorem eventually_not_equilibrium_at_site (q : Fin 3 → ℝ) (a : Fin 3 → E)
    (ha : Function.Injective a) (i : Fin 3) (hq : q i ≠ 0) :
    ∀ᶠ x in 𝓝 (a i), x ∉ equilibria q a := by
  let f (j : Fin 3) (x : E) := (-q j / ‖x - a j‖ ^ 3) • (x - a j)
  let rest (x : E) := ∑ j ∈ Finset.univ.erase i, f j x
  have hc : ContinuousAt rest (a i) := by
    apply continuous_sum_at
    intro j hj
    have hr : ‖a i - a j‖ ≠ 0 := norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr (ha.ne (Finset.ne_of_mem_erase hj).symm))
    dsimp [f]
    fun_prop (disch := exact pow_ne_zero _ hr)
  have hc' : ContinuousAt (fun x => ‖rest x‖ * ‖x - a i‖ ^ 2) (a i) :=
    hc.norm.mul ((continuousAt_id.sub continuousAt_const).norm.pow 2)
  have hne : ‖rest (a i)‖ * ‖a i - a i‖ ^ 2 ≠ |q i| := by simpa using (abs_pos.mpr hq).ne
  filter_upwards [hc'.eventually_ne hne] with x hx
  intro he
  obtain ⟨hsrc, hzero⟩ := (mem_equilibria_iff q a x).mp he
  have hn : ‖x - a i‖ ≠ 0 := norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr fun h => hsrc ⟨i,h.symm⟩)
  have heq : rest x = -f i x := eq_neg_of_add_eq_zero_left
    ((Finset.sum_erase_add Finset.univ (fun j => f j x) (Finset.mem_univ i)).trans hzero)
  apply hx
  rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
  field_simp

/-- Removing the three sites from the zero set still leaves a closed set. -/
theorem equilibria_closed (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : Function.Injective a)
    (hq : ∀ i, q i ≠ 0) : IsClosed (equilibria q a) := by
  apply isOpen_compl_iff.mp
  rw [isOpen_iff_mem_nhds]
  intro x hx
  by_cases hx' : x ∈ Set.range a
  · obtain ⟨i, rfl⟩ := hx'
    exact eventually_not_equilibrium_at_site q a ha i (hq i)
  have hc : ContinuousAt (fun x => ∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) x := by
    apply continuous_sum_at
    intro i _
    have hn : ‖x - a i‖ ≠ 0 := norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr fun h => hx' ⟨i, h.symm⟩)
    fun_prop (disch := exact pow_ne_zero _ hn)
  have hne : (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) ≠ 0 :=
    fun h => hx ((mem_equilibria_iff q a x).mpr ⟨hx', h⟩)
  exact (hc.eventually_ne hne).mono fun y hy he => hy ((mem_equilibria_iff q a y).mp he).2

section FarFieldExpansion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable def correction (b e : V) (t : ℝ) : ℝ :=
  let r := ‖e - t • b‖
  (2 * ⟪e, b⟫_ℝ - t * ‖b‖ ^ 2) * (r^2 + r + 1) / ((r+1) * r^3)

/-- Exact divided difference, including the first-order dipole correction. -/
private theorem radial_identity (b e : V) (t : ℝ) (he : ‖e‖ = 1) (hn : e - t • b ≠ 0) :
    1 / ‖e - t • b‖ ^ 3 = 1 + t * correction b e t := by
  let r := ‖e - t • b‖
  have hr : 0 < r := norm_pos_iff.mpr hn
  have hsq : r^2 = 1 - 2*t*⟪e,b⟫_ℝ + t^2*‖b‖^2 := by
    dsimp [r]
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he, real_inner_comm b e]
    ring
  change 1 / r^3 = 1 + t * ((2 * ⟪e,b⟫_ℝ - t * ‖b‖^2) * (r^2+r+1) / ((r+1)*r^3))
  field_simp [hr.ne', show r+1 ≠ 0 by positivity]
  linear_combination -(r^2+r+1) * hsq

private noncomputable def farField (q : Fin 3 → ℝ) (a : Fin 3 → V) (t : ℝ) (e : V) :=
  ∑ i, (-q i / ‖e - t • a i‖ ^ 3) • (e - t • a i)

private noncomputable def dipoleField (q : Fin 3 → ℝ) (a : Fin 3 → V) (t : ℝ) (e : V) :=
  ∑ i, ((q i / ‖e - t • a i‖^3) • a i - (q i * correction (a i) e t) • e)

private theorem neutral_farField (q : Fin 3 → ℝ) (a : Fin 3 → V) (hQ : ∑ i, q i = 0)
    (t : ℝ) (e : V) (he : ‖e‖ = 1) (hn : ∀ i, e - t • a i ≠ 0) :
    farField q a t e = t • dipoleField q a t e := by
  have h (i : Fin 3) : (-q i / ‖e-t • a i‖^3) • (e-t • a i) =
      t • ((q i / ‖e-t • a i‖^3) • a i - (q i * correction (a i) e t) • e) -
      q i • e := by
    have hi := radial_identity (a i) e t he (hn i)
    simp only [one_div] at hi
    simp only [smul_sub, smul_smul, div_eq_mul_inv, hi]
    module
  simp only [farField, h, Finset.sum_sub_distrib, ← Finset.smul_sum,
    ← Finset.sum_smul, hQ, zero_smul, sub_zero, dipoleField]

private theorem dipoleField_zero (q : Fin 3 → ℝ) (a : Fin 3 → V) (e : V) (he : ‖e‖ = 1) :
    dipoleField q a 0 e =
    (∑ i, q i • a i) - (3 * ⟪e, ∑ i, q i • a i⟫_ℝ) • e := by
  simp only [dipoleField, correction, zero_smul, sub_zero, he, one_pow, div_one,
    zero_mul, inner_sum, real_inner_smul_right, Finset.sum_sub_distrib,
    ← Finset.sum_smul, Finset.mul_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  ring

end FarFieldExpansion

/-- A single reciprocal-radius neighborhood works for every unit direction. -/
theorem farField_nonzero (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : AffineIndependent ℝ a)
    (hq : q 0 ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ e : E, ‖e‖ = 1 → t ≠ 0 →
      farField q a t e ≠ 0 := by
  have hc := isCompact_sphere (0 : E) (1 : ℝ)
  suffices h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ e ∈ Metric.sphere (0 : E) 1,
      ‖e‖ = 1 → t ≠ 0 → farField q a t e ≠ 0 by
    filter_upwards [h] with t ht e he
    exact ht e (by simpa using he) he
  apply hc.eventually_forall_of_forall_eventually
  intro e he
  have hu : ‖e‖ = 1 := by simpa using he
  have he0 : e ≠ 0 := by intro h; simp [h] at hu
  by_cases hQ : ∑ i, q i = 0
  · have hc' : ContinuousAt (fun z : ℝ × E => dipoleField q a z.1 z.2) (0, e) := by
      apply continuous_sum_at
      intro i _
      dsimp [correction]
      fun_prop (disch := simp [hu])
    have hne : dipoleField q a 0 e ≠ 0 := by
      rw [dipoleField_zero q a e hu]
      intro hz
      have hh := dipole_norm_sq (∑ i, q i • a i) e hu
      rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hh
      have hp := norm_pos_iff.mpr (neutral_dipole_ne_zero a q ha hq hQ)
      nlinarith [sq_pos_of_pos hp, sq_nonneg ⟪e, ∑ i, q i • a i⟫_ℝ]
    have hdir (i : Fin 3) : ∀ᶠ z : ℝ × E in 𝓝 (0,e), z.2 - z.1 • a i ≠ 0 := by
      apply ContinuousAt.eventually_ne (g := fun z : ℝ × E => z.2 - z.1 • a i) (by fun_prop)
      simpa using he0
    -- The divided-difference formula uses unit directions only.
    filter_upwards [hc'.eventually_ne hne, Filter.eventually_all.mpr hdir] with z hz hs hunit ht
    rw [neutral_farField q a hQ z.1 z.2 hunit hs]
    exact smul_ne_zero ht hz
  · have hc' : ContinuousAt (fun z : ℝ × E => farField q a z.1 z.2) (0, e) := by
      apply continuous_sum_at
      intro i _
      fun_prop (disch := simp [hu])
    have hne : farField q a 0 e ≠ 0 := by
      simpa [farField, hu, ← Finset.sum_smul] using smul_ne_zero (neg_ne_zero.mpr hQ) he0
    exact (hc'.eventually_ne hne).mono fun _ h _ _ => h

private theorem rescale_force {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (q : Fin 3 → ℝ) (a : Fin 3 → V) (x : V)
    (t : ℝ) (ht : 0 < t) :
    farField q a t (t • x) =
      (1 / t^2) • ∑ i, (-q i / ‖x - a i‖^3) • (x - a i) := by
  rw [farField, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht, smul_smul, smul_smul, mul_pow]
  congr 1
  by_cases hn : ‖x-a i‖ = 0
  · simp [hn]
  · field_simp

/-- Nondegenerate equilibria form a finite set, including for neutral charges. -/
theorem equilibria_finite (q : Fin 3 → ℝ) (a : Fin 3 → E)
    (ha : AffineIndependent ℝ a) (hq : ∀ i, q i ≠ 0)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) :
    (equilibria q a).Finite := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (farField_nonzero q a ha (hq 0))
  have hb : Bornology.IsBounded (equilibria q a) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨δ⁻¹, fun x hx => ?_⟩
    by_contra! hr
    have hr' : 0 < ‖x‖ := lt_trans (inv_pos.mpr hδ) hr
    let t := ‖x‖⁻¹
    have ht : 0 < t := inv_pos.mpr hr'
    have hsmall : t < δ := (inv_lt_comm₀ hr' hδ).mpr hr
    have htb : t ∈ Metric.ball (0:ℝ) δ := by simpa [Real.dist_eq, abs_of_pos ht] using hsmall
    have hunit : ‖t • x‖ = 1 := by simp [norm_smul, t, hr'.ne']
    have hne := hball htb (t • x) hunit ht.ne'
    apply hne
    rw [rescale_force q a x t ht, ((mem_equilibria_iff q a x).mp hx).2, smul_zero]
  exact ((Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨equilibria_closed q a ha.injective hq, hb⟩)).finite (equilibria_discrete q a hnd)

open scoped unitInterval

private noncomputable def angleLift (γ : C(unitInterval, Circle)) : C(unitInterval, ℝ) :=
  Circle.isCoveringMap_exp.liftPath γ (γ 0).val.arg (Circle.exp_arg _).symm

/-- Total change in a continuous choice of argument, measured in radians. -/
noncomputable def angleChange (γ : C(unitInterval, Circle)) : ℝ :=
  angleLift γ 1 - angleLift γ 0

private theorem lift_lifts (γ : C(unitInterval, Circle)) :
    Circle.exp ∘ angleLift γ = γ :=
  Circle.isCoveringMap_exp.liftPath_lifts ..

/-- The change in argument does not depend on the choice of lift. -/
theorem angleChange_of_lift (γ : C(unitInterval, Circle)) (θ : C(unitInterval, ℝ))
    (h : ∀ t, Circle.exp (θ t) = γ t) : angleChange γ = θ 1 - θ 0 := by
  let a := (γ 0).val.arg
  let F : C(unitInterval, ℝ) := ⟨fun t => θ t - θ 0 + a, by fun_prop⟩
  have hF : F = angleLift γ := by
    apply (Circle.isCoveringMap_exp.eq_liftPath_iff' _).mpr
    refine ⟨funext fun t => ?_, by simp [F, a]⟩
    change Circle.exp (θ t - θ 0 + a) = γ t
    rw [Circle.exp_add, Circle.exp_sub, h, h, Circle.exp_arg]
    simp
  change angleLift γ 1 - angleLift γ 0 = _
  rw [← hF]
  dsimp [F]
  ring

noncomputable def along (F : C(unitInterval × unitInterval, Circle))
    (p : unitInterval → unitInterval × unitInterval) (hp : Continuous p) :=
  F.comp (⟨p,hp⟩ : C(unitInterval, unitInterval × unitInterval))

/-- Every nonsingular grid cell contributes zero to the boundary sum.
The field may traverse any number of half-planes within the cell. -/
theorem square_angleChange (F : C(unitInterval × unitInterval, Circle)) :
    angleChange (along F (fun t => (t,0)) (by fun_prop)) -
    angleChange (along F (fun t => (t,1)) (by fun_prop)) +
    (angleChange (along F (fun t => (1,t)) (by fun_prop)) -
     angleChange (along F (fun t => (0,t)) (by fun_prop))) = 0 := by
  let γ := along F (fun t => (0,t)) (by fun_prop)
  have h₀ : ∀ t, F (0,t) = Circle.exp (angleLift γ t) := fun t =>
    (congrFun (lift_lifts γ) t).symm
  let Θ := Circle.isCoveringMap_exp.liftHomotopy F (angleLift γ) h₀
  have hΘ : ∀ z, Circle.exp (Θ z) = F z := fun z =>
    congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts F (angleLift γ) h₀) z
  have hedge (p : unitInterval → unitInterval × unitInterval) (hp : Continuous p) :
      angleChange (along F p hp) = Θ (p 1) - Θ (p 0) :=
    angleChange_of_lift _ (Θ.comp ⟨p,hp⟩) fun t => hΘ (p t)
  simp only [hedge]
  ring

/-- A continuous deformation of closed curves preserves their change in argument. -/
theorem angleChange_homotopy (F : C(unitInterval × unitInterval, Circle))
    (h : ∀ t, F (t,0) = F (t,1)) :
    angleChange (along F (fun t => (1,t)) (by fun_prop)) =
    angleChange (along F (fun t => (0,t)) (by fun_prop)) := by
  have he : along F (fun t => (t,0)) (by fun_prop) =
      along F (fun t => (t,1)) (by fun_prop) := ContinuousMap.ext h
  have hh := square_angleChange F
  rw [he, sub_self, zero_add, sub_eq_zero] at hh
  exact hh

/-- Multiplication of directions adds their changes in argument. -/
theorem angleChange_mul (γ η : C(unitInterval, Circle)) :
    angleChange (γ * η) = angleChange γ + angleChange η := by
  rw [angleChange_of_lift _ (angleLift γ + angleLift η)]
  · simp [angleChange]
    ring
  · intro t
    change Circle.exp (angleLift γ t + angleLift η t) = γ t * η t
    rw [Circle.exp_add]
    exact congrArg₂ (· * ·) (congrFun (lift_lifts γ) t) (congrFun (lift_lifts η) t)

/-- A model curve of any integral degree, with arbitrary initial direction. -/
theorem angleChange_model (k : ℤ) (a : ℝ) :
    angleChange (⟨fun t => Circle.exp (a + k * (2 * Real.pi) * (t : ℝ)), by fun_prop⟩ :
      C(unitInterval, Circle)) = k * (2 * Real.pi) := by
  rw [angleChange_of_lift _ (⟨fun t => a + k * (2 * Real.pi) * (t : ℝ), by fun_prop⟩ :
    C(unitInterval, ℝ)) (fun _ => rfl)]
  simp

/-- Convert the signed lower bound into an unsigned count, allowing the positive-index
points to be any subset of the extrema. -/
theorem encard_bound_of_signed_sum {X : Type*} (Z : Finset X) (extr : Set X)
    (pos : X → Prop) [DecidablePred pos] (hpos : ∀ x ∈ Z, pos x → x ∈ extr)
    (hindex : (-2 : ℤ) ≤ ∑ x ∈ Z, (if pos x then (1 : ℤ) else -1)) :
    (Z.card : ℕ∞) ≤ 2 * extr.encard + 2 := by
  classical
  let A := Z.filter pos
  let B := Z.filter (fun x => ¬ pos x)
  have hsplit : A.card + B.card = Z.card := Finset.card_filter_add_card_filter_not ..
  have hsum : (∑ x ∈ Z, (if pos x then (1 : ℤ) else -1)) = A.card - (B.card : ℤ) := by
    rw [Finset.sum_ite]
    simp [A, B, sub_eq_add_neg]
  have hb : Z.card ≤ 2 * A.card + 2 := by omega
  have hA : (A.card : ℕ∞) ≤ extr.encard := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    apply Set.encard_le_encard
    intro x hx
    obtain ⟨hx',hp⟩ := Finset.mem_filter.mp hx
    exact hpos x hx' hp
  calc
    (Z.card : ℕ∞) ≤ ((2 * A.card + 2 : ℕ) : ℕ∞) := by exact_mod_cast hb
    _ = 2 * (A.card : ℕ∞) + 2 := by norm_cast
    _ ≤ 2 * extr.encard + 2 := by gcongr

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private noncomputable def hessTerm (q : ℝ) (d : V) : V →L[ℝ] V :=
  (-q / ‖d‖^3) • ContinuousLinearMap.id ℝ V +
  ((3*q / ‖d‖^5) • innerSL ℝ d).smulRight d

private theorem force_derivative (q : ℝ) {a x : V} (hne : x ≠ a) :
    HasFDerivAt (fun y : V => (-q / ‖y-a‖^3) • (y-a)) (hessTerm q (x-a)) x := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hd := (norm_sub_derivative hne).pow 3
  have hs := ((hasDerivAt_inv (pow_ne_zero 3 hn)).comp_hasFDerivAt x hd).const_mul (-q)
  have hcoef : HasFDerivAt (fun y : V => -q / ‖y-a‖^3)
      ((3*q / ‖x-a‖^5) • innerSL ℝ (x-a)) x := by
    convert! hs using 1
    ext v
    simp [smul_smul, smul_eq_mul]
    field_simp [hn]
    ring_nf
    simp
  exact hcoef.smul ((hasFDerivAt_id x).sub_const a)

end

/-- The bilinear Hessian of the actual Coulomb potential, with both vector arguments
in the order used by the formal nondegeneracy hypothesis. -/
theorem potential_hessian (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E} (hx : x ∉ Set.range a)
    (v w : E) : iteratedFDeriv ℝ 2 (potential q a) x ![v,w] =
      ∑ i, ((-q i / ‖x-a i‖^3) * ⟪v,w⟫_ℝ +
        (3*q i / ‖x-a i‖^5) * ⟪x-a i,v⟫_ℝ * ⟪x-a i,w⟫_ℝ) := by
  let F (y : E) := ∑ i, (-q i / ‖y-a i‖^3) • (y-a i)
  have hd : HasFDerivAt F (∑ i, hessTerm (q i) (x-a i)) x :=
    HasFDerivAt.fun_sum fun i _ => force_derivative (q i) (fun h => hx ⟨i,h.symm⟩)
  let D := (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have hloc : fderiv ℝ (potential q a) =ᶠ[𝓝 x] D ∘ F := by
    filter_upwards [(Set.finite_range a).isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact (potential_gradient q a y hy).hasFDerivAt.fderiv
  have hb := (D.hasFDerivAt.comp x hd).congr_of_eventuallyEq hloc
  rw [iteratedFDeriv_two_apply, hb.fderiv]
  simp [D, hessTerm, toDual_apply_apply, inner_sub_left, mul_assoc]

/-- Restricting the Hessian to the direction of the site plane preserves nondegeneracy. -/
theorem planar_hessian_nondegenerate (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E}
    (hx : x ∉ Set.range a) (hP : x ∈ affineSpan ℝ (Set.range a))
    (hnd : HasNondegenerateHessianAt (potential q a) x)
    (v : E) (hv : v ∈ (affineSpan ℝ (Set.range a)).direction) (hne : v ≠ 0) :
    ∃ w ∈ (affineSpan ℝ (Set.range a)).direction,
      iteratedFDeriv ℝ 2 (potential q a) x ![v,w] ≠ 0 := by
  let P := affineSpan ℝ (Set.range a)
  obtain ⟨u, hu⟩ := hnd v hne
  obtain ⟨w, hw, n, hn, rfl⟩ := P.direction.exists_add_mem_mem_orthogonal u
  refine ⟨w, hw, fun h => hu ?_⟩
  have hn1 : ⟪v,n⟫_ℝ = 0 := hn v hv
  have hn2 (i : Fin 3) : ⟪x-a i,n⟫_ℝ = 0 := hn _ (P.vsub_mem_direction hP
    (subset_affineSpan ℝ _ (Set.mem_range_self i)))
  simpa only [potential_hessian q a hx, inner_add_right, hn1, hn2, add_zero] using h

/-- A coercive restriction of the ambient Hessian gives a minimum on an affine
subspace. This only uses the derivative of the gradient at the critical point. -/
theorem localMinOn_of_hessian_lower_bound {f : E → ℝ} {x : E} {P : AffineSubspace ℝ E}
    (hx : x ∈ P) (hd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) (hz : fderiv ℝ f x = 0)
    {H : E →L[ℝ] (E →L[ℝ] ℝ)} (hh : HasFDerivAt (fderiv ℝ f) H x)
    {c : ℝ} (hc : 0 < c) (hpos : ∀ v ∈ P.direction, c * ‖v‖^2 ≤ H v v) :
    IsLocalMinOn f P x := by
  have hr : ∀ᶠ y in 𝓝 x, y ∈ P → 0 ≤ fderiv ℝ f y (y-x) := by
    filter_upwards [hh.isLittleO.bound hc] with y h hy
    simp only [hz, sub_zero] at h
    let d := y-x
    have hq := hpos d (P.vsub_mem_direction hy hx)
    have hle := (fderiv ℝ f y - H d).le_opNorm d
    have habs := (abs_le.mp (show |(fderiv ℝ f y - H d) d| ≤ _ from hle)).1
    change -_ ≤ fderiv ℝ f y d - H d d at habs
    have hmul := mul_le_mul_of_nonneg_right h (norm_nonneg d)
    change 0 ≤ fderiv ℝ f y d
    change ‖fderiv ℝ f y - H d‖ * ‖d‖ ≤ c * ‖d‖ * ‖d‖ at hmul
    nlinarith
  obtain ⟨r,hr0,hball⟩ := Metric.mem_nhds_iff.mp (hd.and hr)
  apply Filter.mem_of_superset (inter_mem_nhdsWithin _ (Metric.ball_mem_nhds x hr0))
  rintro y ⟨hyP,hy⟩
  let L := AffineMap.lineMap (k := ℝ) x y
  have hL (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : L t ∈ Metric.ball x r :=
    (convex_ball x r).lineMap_mem (Metric.mem_ball_self hr0) hy ht
  have hder (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      HasDerivAt (f ∘ L) (fderiv ℝ f (L t) (y-x)) t :=
    (hball (hL t ht)).1.hasFDerivAt.comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
  obtain ⟨t,ht,h⟩ := exists_hasDerivAt_eq_slope (f ∘ L)
    (fun t => fderiv ℝ f (L t) (y-x)) zero_lt_one
    (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
    (fun t ht => hder t (Ioo_subset_Icc_self ht))
  have hp := (hball (hL t (Ioo_subset_Icc_self ht))).2 (AffineMap.lineMap_mem t hx hyP)
  have hdiff : L t - x = t • (y-x) := by simp [L, AffineMap.lineMap_apply_module']
  rw [hdiff, map_smul, smul_eq_mul] at hp
  have hs := nonneg_of_mul_nonneg_right hp ht.1
  rw [h] at hs
  simpa [L, Function.comp_def, sub_nonneg] using hs

/-- Positivity in all nonzero tangent directions is uniform on the unit sphere. -/
private theorem positive_coercive (K : Submodule ℝ E) (H : E →L[ℝ] (E →L[ℝ] ℝ))
    (hp : ∀ v ∈ K, v ≠ 0 → 0 < H v v) :
    ∃ c > (0 : ℝ), ∀ v ∈ K, c * ‖v‖^2 ≤ H v v := by
  let S := Metric.sphere (0:E) 1 ∩ (K : Set E)
  have hK : IsCompact S := (isCompact_sphere (0:E) 1).inter_right K.closed_of_finiteDimensional
  have hcont : Continuous (fun v : E => H v v) := by fun_prop
  obtain ⟨c,hc,hlow⟩ := hK.exists_forall_le' hcont.continuousOn
    (a := 0) (fun v hv => hp v hv.2 (fun h => by
      have hn : ‖v‖ = 1 := by simpa using hv.1
      simp [h] at hn))
  refine ⟨c,hc,fun v hv => ?_⟩
  by_cases hv0 : v = 0
  · simp [hv0]
  let u := ‖v‖⁻¹ • v
  have hu : u ∈ S := ⟨by simpa [u] using norm_smul_inv_norm (𝕜 := ℝ) hv0, K.smul_mem _ hv⟩
  have heq : ‖v‖ • u = v := by simp [u, smul_smul, norm_ne_zero_iff.mpr hv0]
  calc
    c * ‖v‖^2 ≤ H u u * ‖v‖^2 := by gcongr; exact hlow u hu
    _ = H (‖v‖ • u) (‖v‖ • u) := by simp [smul_eq_mul]; ring
    _ = H v v := by rw [heq]

/-- Second derivative test on the actual affine site plane. -/
theorem planar_min_of_positive_hessian (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E}
    (hx : x ∈ equilibria q a) (hP : x ∈ affineSpan ℝ (Set.range a))
    (hp : ∀ v ∈ (affineSpan ℝ (Set.range a)).direction, v ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (potential q a) x ![v,v]) :
    IsLocalMinOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x := by
  let H := fderiv ℝ (fderiv ℝ (potential q a)) x
  obtain ⟨c,hc,hpos⟩ := positive_coercive (affineSpan ℝ (Set.range a)).direction H
    (by simpa [H, iteratedFDeriv_two_apply] using hp)
  have hs : ContDiffAt ℝ 2 (potential q a) x := by
    apply ContDiffAt.sum
    intro i _
    exact contDiffAt_const.div (contDiffAt_id.dist ℝ contDiffAt_const
      (fun h => hx.1 ⟨i, h.symm⟩)) (dist_ne_zero.mpr fun h => hx.1 ⟨i,h.symm⟩)
  apply localMinOn_of_hessian_lower_bound hP _ _ _ hc hpos
  · filter_upwards [(Set.finite_range a).isClosed.isOpen_compl.mem_nhds hx.1] with y hy
    exact (potential_gradient q a y hy).differentiableAt
  · exact (toDual ℝ E).symm.injective (by simpa [gradient] using hx.2)
  · exact (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num) |>.hasFDerivAt

/-- The unit direction of a continuous nonvanishing complex field. -/
noncomputable def direction {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) (h : ∀ x, f x ≠ 0) :
    C(X, Circle) where
  toFun x := ⟨f x / (‖f x‖ : ℂ), mem_sphere_zero_iff_norm.mpr
    (by simp [norm_ne_zero_iff.mpr (h x)])⟩
  continuous_toFun := Continuous.subtype_mk (f.continuous.div (by fun_prop)
    (fun x => by simpa using norm_ne_zero_iff.mpr (h x))) _

/-- A perturbation smaller than a reference field on a closed curve preserves its index. -/
theorem angleChange_perturbation (f g : C(unitInterval, ℂ)) (hf : f 0 = f 1) (hg : g 0 = g 1)
    (h : ∀ t, ‖g t - f t‖ < ‖f t‖) (hf0 : ∀ t, f t ≠ 0) (hg0 : ∀ t, g t ≠ 0) :
    angleChange (direction g hg0) = angleChange (direction f hf0) := by
  let L : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun z => f z.2 + (z.1 : ℝ) • (g z.2 - f z.2), by fun_prop⟩
  have hL (z : unitInterval × unitInterval) : L z ≠ 0 := by
    have hmul : ‖(z.1 : ℝ) • (g z.2 - f z.2)‖ < ‖f z.2‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg z.1.2.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) z.1.2.2).trans_lt (h z.2)
    intro hz
    have heq : f z.2 = -((z.1 : ℝ) • (g z.2 - f z.2)) := eq_neg_of_add_eq_zero_left hz
    exact (ne_of_lt hmul) (by simpa using (congrArg norm heq).symm)
  let F := direction L hL
  have hclosed (t : unitInterval) : F (t,0) = F (t,1) := by
    apply Circle.ext
    apply congrArg (fun z : ℂ => z / (‖z‖ : ℂ))
    change f 0 + _ • (g 0 - f 0) = f 1 + _ • (g 1 - f 1)
    rw [hf, hg]
  have h₁ : along F (fun t => (1,t)) (by fun_prop) = direction g hg0 := by
    ext t : 2
    apply congrArg (fun z : ℂ => z / (‖z‖ : ℂ))
    change f t + (1 : ℝ) • (g t - f t) = g t
    simp
  have h₀ : along F (fun t => (0,t)) (by fun_prop) = direction f hf0 := by
    ext t : 2
    apply congrArg (fun z : ℂ => z / (‖z‖ : ℂ))
    change f t + (0 : ℝ) • (g t - f t) = f t
    simp
  simpa only [h₀,h₁] using angleChange_homotopy F hclosed

/-- A nonzero complex scalar times the standard degree-k loop has index k. -/
noncomputable def modelLoop (c : ℂ) (k : ℤ) : C(unitInterval, ℂ) :=
  ⟨fun t => c * ((Circle.exp (k * (2 * Real.pi) * (t : ℝ))) : ℂ), by fun_prop⟩

theorem modelLoop_ne_zero {c : ℂ} (hc : c ≠ 0) (k : ℤ) : ∀ t, modelLoop c k t ≠ 0 :=
  fun _ => mul_ne_zero hc (Circle.coe_ne_zero _)

theorem modelLoop_closed (c : ℂ) (k : ℤ) : modelLoop c k 0 = modelLoop c k 1 := by
  change c * ↑(Circle.exp (_ * (0:ℝ))) = c * ↑(Circle.exp (_ * (1:ℝ)))
  rw [mul_zero, mul_one, Circle.exp_int_mul_two_pi, Circle.exp_zero]

theorem modelLoop_angleChange {c : ℂ} (hc : c ≠ 0) (k : ℤ) :
    angleChange (direction (modelLoop c k) (modelLoop_ne_zero hc k)) = k * (2 * Real.pi) := by
  let c₀ : Circle := ⟨c / (‖c‖ : ℂ), mem_sphere_zero_iff_norm.mpr
    (by simp [norm_ne_zero_iff.mpr hc])⟩
  let a := (c₀ : ℂ).arg
  convert angleChange_model k a using 2
  apply ContinuousMap.ext
  intro t
  apply Circle.ext
  change (c * ↑(Circle.exp _) / ↑‖c * ↑(Circle.exp _)‖ : ℂ) =
    ↑(Circle.exp (a + _))
  rw [norm_mul, Circle.norm_coe, mul_one, Circle.exp_add, Circle.coe_mul,
    show Circle.exp a = c₀ from Circle.exp_arg c₀]
  change _ = (c / (‖c‖ : ℂ)) * _
  ring

/-- Dominant Fourier mode test for the index of an elliptic linear field or a dipole. -/
theorem angleChange_of_dominant_mode (g : C(unitInterval, ℂ)) (hg : g 0 = g 1)
    {c : ℂ} (hc : c ≠ 0) (k : ℤ) (hg0 : ∀ t, g t ≠ 0)
    (h : ∀ t, ‖g t - modelLoop c k t‖ < ‖modelLoop c k t‖) :
    angleChange (direction g hg0) = k * (2 * Real.pi) :=
  (angleChange_perturbation _ _ (modelLoop_closed c k) hg h _ hg0).trans
    (modelLoop_angleChange hc k)

/-- An orthonormal complex coordinate system on the direction space of the site plane. -/
noncomputable def planeAxes (a : Fin 3 → E) (ha : AffineIndependent ℝ a) :
    ℂ ≃ₗᵢ[ℝ] (affineSpan ℝ (Set.range a)).direction := by
  let K := (affineSpan ℝ (Set.range a)).direction
  have hr : Module.finrank ℝ K = 2 := by
    exact (congrArg (fun L : Submodule ℝ E => Module.finrank ℝ L)
      (direction_affineSpan ℝ (Set.range a))).trans (ha.finrank_vectorSpan (Fintype.card_fin 3))
  exact Complex.isometryOfOrthonormal ((stdOrthonormalBasis ℝ K).reindex (finCongr hr))

noncomputable def planePoint (a : Fin 3 → E) (ha : AffineIndependent ℝ a) (z : ℂ) : E :=
  (planeAxes a ha z : E) + a 0

theorem range_planePoint (a : Fin 3 → E) (ha : AffineIndependent ℝ a) :
    Set.range (planePoint a ha) = (affineSpan ℝ (Set.range a) : Set E) := by
  let P := affineSpan ℝ (Set.range a)
  have h₀ : a 0 ∈ P := subset_affineSpan ℝ _ (Set.mem_range_self _)
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    exact AffineSubspace.vadd_mem_of_mem_direction (planeAxes a ha z).2 h₀
  · intro hx
    let d : P.direction := ⟨x-a 0,P.vsub_mem_direction hx h₀⟩
    refine ⟨(planeAxes a ha).symm d, ?_⟩
    simp [planePoint, d]

theorem planePoint_isometry (a : Fin 3 → E) (ha : AffineIndependent ℝ a) :
    Isometry (planePoint a ha) := by
  apply Isometry.of_dist_eq
  intro z w
  rw [planePoint, planePoint, dist_add_right]
  exact (planeAxes a ha).dist_map z w

/-- A symmetric two-by-two form with positive determinant has constant strict sign. -/
theorem planar_quadratic_definite {A B C : ℝ} (hd : 0 < A*C-B^2) :
    (∀ x y : ℝ, (x,y) ≠ (0,0) → 0 < A*x^2 + 2*B*x*y + C*y^2) ∨
    (∀ x y : ℝ, (x,y) ≠ (0,0) → A*x^2 + 2*B*x*y + C*y^2 < 0) := by
  have hA : A ≠ 0 := by intro h; rw [h] at hd; nlinarith [sq_nonneg B]
  have hmul (x y : ℝ) (hne : (x,y) ≠ (0,0)) :
      0 < A * (A*x^2 + 2*B*x*y + C*y^2) := by
    have he : A*(A*x^2 + 2*B*x*y+C*y^2) = (A*x+B*y)^2 + (A*C-B^2)*y^2 := by ring
    rw [he]
    by_cases hy : y = 0
    · subst y
      have hx : x ≠ 0 := fun h => hne (by simp [h])
      simpa using sq_pos_of_ne_zero (mul_ne_zero hA hx)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hd (sq_pos_of_ne_zero hy))
  rcases lt_or_gt_of_ne hA with hn | hp
  · exact Or.inr fun x y h => neg_of_mul_pos_right (hmul x y h) hn.le
  · exact Or.inl fun x y h => pos_of_mul_pos_right (hmul x y h) hp.le

theorem planar_extr_of_definite_hessian (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E}
    (hx : x ∈ equilibria q a) (hP : x ∈ affineSpan ℝ (Set.range a))
    (hp : (∀ v ∈ (affineSpan ℝ (Set.range a)).direction, v ≠ 0 →
          0 < iteratedFDeriv ℝ 2 (potential q a) x ![v,v]) ∨
      (∀ v ∈ (affineSpan ℝ (Set.range a)).direction, v ≠ 0 →
          iteratedFDeriv ℝ 2 (potential q a) x ![v,v] < 0)) :
    IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x := by
  rcases hp with h | h
  · exact Or.inl (planar_min_of_positive_hessian q a hx hP h)
  have heq : potential (-q) a = -(potential q a) := by
    funext y
    simp only [potential, Pi.neg_apply, neg_div, Finset.sum_neg_distrib]
  have hx' : x ∈ equilibria (-q) a := by
    refine ⟨hx.1, ?_⟩
    have hz := hx.2
    change gradient (potential q a) x = 0 at hz
    change gradient (potential (-q) a) x = 0
    simpa [heq, gradient, fderiv_neg] using congrArg Neg.neg hz
  apply Or.inr
  have hm := planar_min_of_positive_hessian (-q) a hx' hP (by
    intro v hv hv0
    simpa [heq, iteratedFDeriv_neg_apply] using h v hv hv0)
  change IsLocalMaxOn (potential q a) _ x
  simpa [heq] using hm.neg

/-- Translating a model circle by less than its radius preserves its winding. -/
theorem translated_model_angleChange (b c : ℂ) (k : ℤ) (h : ‖b‖ < ‖c‖) :
    let g := ContinuousMap.const unitInterval b + modelLoop c k
    ∃ hg : ∀ t, g t ≠ 0, angleChange (direction g hg) = k * (2 * Real.pi) := by
  intro g
  have hr (t : unitInterval) : ‖modelLoop c k t‖ = ‖c‖ := by
    change ‖c * ((Circle.exp _) : ℂ)‖ = _
    rw [norm_mul, Circle.norm_coe, mul_one]
  have hg (t : unitInterval) : g t ≠ 0 := by
    intro hz
    have he : b = -modelLoop c k t := eq_neg_of_add_eq_zero_left hz
    have hh := congrArg norm he
    rw [norm_neg,hr] at hh
    exact h.ne hh
  refine ⟨hg, angleChange_of_dominant_mode g ?_ (norm_pos_iff.mp ((norm_nonneg _).trans_lt h))
    k hg ?_⟩
  · change b + modelLoop c k 0 = b + modelLoop c k 1
    rw [modelLoop_closed]
  · intro t
    change ‖b + modelLoop c k t - modelLoop c k t‖ < _
    simpa only [add_sub_cancel_right, hr] using h

/-- Complex Fourier decomposition of the dipole in an arbitrary orientation. -/
theorem complex_dipole (p : ℂ) (u : Circle) :
    p - (3 * ⟪(u:ℂ),p⟫_ℝ) • (u:ℂ) =
      -p/2 + (-3 * starRingEnd ℂ p / 2) * (u:ℂ)^2 := by
  have hn : (u:ℂ).re^2 + (u:ℂ).im^2 = 1 := by
    simpa [Complex.normSq_apply, pow_two] using Circle.normSq_coe u
  apply Complex.ext
  · simp [Complex.inner, Complex.mul_re, Complex.mul_im, pow_two]
    linear_combination -(3/2 * p.re) * hn
  · simp [Complex.inner, Complex.mul_re, Complex.mul_im, pow_two]
    linear_combination -(3/2 * p.im) * hn

noncomputable def siteCoordinate (a : Fin 3 → E) (ha : AffineIndependent ℝ a) (i : Fin 3) : ℂ :=
  (planeAxes a ha).symm ⟨a i-a 0,
    (affineSpan ℝ (Set.range a)).vsub_mem_direction (subset_affineSpan ℝ _ (Set.mem_range_self i))
      (subset_affineSpan ℝ _ (Set.mem_range_self 0))⟩

theorem planePoint_site (a : Fin 3 → E) (ha : AffineIndependent ℝ a) (i : Fin 3) :
    planePoint a ha (siteCoordinate a ha i) = a i := by
  simp [planePoint, siteCoordinate]

/-- The components of the full force in the orthonormal site coordinates. -/
theorem plane_force (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : AffineIndependent ℝ a) (z : ℂ) :
    (planeAxes a ha (∑ i, (-q i / ‖z-siteCoordinate a ha i‖^3) • (z-siteCoordinate a ha i)) : E) =
    ∑ i, (-q i / ‖planePoint a ha z-a i‖^3) • (planePoint a ha z-a i) := by
  rw [map_sum]
  simp only [Submodule.coe_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hdiff : (planeAxes a ha (z-siteCoordinate a ha i) : E) = planePoint a ha z-a i := by
    simp [planePoint, siteCoordinate, map_sub]
    abel
  have hd : ‖z-siteCoordinate a ha i‖ = ‖planePoint a ha z-a i‖ := by
    rw [← hdiff]
    exact ((planeAxes a ha).norm_map _).symm
  rw [map_smul, Submodule.coe_smul, hd, hdiff]

/-- Equilibria in the complex chart coincide with the regular-domain zeros of its force. -/
theorem plane_equilibrium_iff (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : AffineIndependent ℝ a)
    (z : ℂ) : planePoint a ha z ∈ equilibria q a ↔ z ∉ Set.range (siteCoordinate a ha) ∧
    (∑ i, (-q i / ‖z-siteCoordinate a ha i‖^3) • (z-siteCoordinate a ha i)) = 0 := by
  rw [mem_equilibria_iff, ← plane_force]
  have hs : planePoint a ha z ∈ Set.range a ↔ z ∈ Set.range (siteCoordinate a ha) := by
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨i,(planePoint_isometry a ha).injective ((planePoint_site a ha i).trans hi)⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i,(planePoint_site a ha i).symm⟩
  rw [hs]
  apply and_congr_right
  intro _
  constructor
  · intro h
    apply (planeAxes a ha).injective
    apply Subtype.ext
    simpa only [map_zero, Submodule.coe_zero] using h
  · intro h
    rw [h, map_zero, Submodule.coe_zero]

/-- A lower bound of minus two on the signed count suffices for the requested
cardinal inequality. The signed count here uses the actual planar extrema. -/
theorem bound_of_signed_equilibria (q : Fin 3 → ℝ) (a : Fin 3 → E)
    (ha : AffineIndependent ℝ a) (hq : ∀ i, q i ≠ 0)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) :
    let P := (affineSpan ℝ (Set.range a) : Set E)
    let Z : Finset E := by
      classical exact (equilibria_finite q a ha hq hnd).toFinset.filter (· ∈ P)
    let X := {x | x ∈ P ∧ x ∈ equilibria q a ∧ IsLocalExtrOn (potential q a) P x}
    (by classical exact (-2 : ℤ) ≤ ∑ x ∈ Z, (if x ∈ X then (1:ℤ) else -1)) →
    {x | x ∈ P ∧ x ∉ Set.range a ∧
      (∑ i, (-q i / ‖x-a i‖^3) • (x-a i)) = 0}.encard ≤ 2*X.encard + 2 := by
  classical
  intro P Z X h
  have heq : {x | x ∈ P ∧ x ∉ Set.range a ∧
      (∑ i, (-q i / ‖x-a i‖^3) • (x-a i)) = 0} = (Z : Set E) := by
    ext x
    simp [Z, mem_equilibria_iff, and_comm, and_assoc, and_left_comm]
  rw [heq, Set.encard_coe_eq_coe_finsetCard]
  exact encard_bound_of_signed_sum Z X (fun x => x ∈ X) (fun _ _ h => h) h

/-- A positive determinant of the planar Hessian gives a local extremum in the
precise restricted sense used by the count. Here u and v can be any spanning pair. -/
theorem planar_extr_of_positive_det (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E}
    (hx : x ∈ equilibria q a) (hP : x ∈ affineSpan ℝ (Set.range a)) (u v : E)
    (hspan : ∀ w ∈ (affineSpan ℝ (Set.range a)).direction, ∃ s t : ℝ, w = s • u + t • v)
    (hdet : 0 <
      iteratedFDeriv ℝ 2 (potential q a) x ![u,u] * iteratedFDeriv ℝ 2 (potential q a) x ![v,v] -
        (iteratedFDeriv ℝ 2 (potential q a) x ![u,v])^2) :
    IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x := by
  let H := fderiv ℝ (fderiv ℝ (potential q a)) x
  have symm' : iteratedFDeriv ℝ 2 (potential q a) x ![v,u] =
      iteratedFDeriv ℝ 2 (potential q a) x ![u,v] := by
    rw [potential_hessian q a hx.1, potential_hessian q a hx.1]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm v u]
    ring
  have symm : H v u = H u v := by simpa [H, iteratedFDeriv_two_apply] using symm'
  have hp : 0 < H u u * H v v - (H u v)^2 := by
    simpa [H, iteratedFDeriv_two_apply] using hdet
  have quad (s t : ℝ) :
      H (s • u + t • v) (s • u + t • v) =
        H u u * s^2 + 2 * H u v * s*t + H v v * t^2 := by
    simp [map_add, map_smul, smul_eq_mul, symm]
    ring
  apply planar_extr_of_definite_hessian q a hx hP
  rcases planar_quadratic_definite hp with hd | hd
  · left
    intro w hw hw0
    obtain ⟨s,t,rfl⟩ := hspan w hw
    have hn : (s,t) ≠ (0,0) := by rintro h; obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; simp at hw0
    have hval := hd s t hn
    rw [← quad] at hval
    simpa [H, iteratedFDeriv_two_apply] using hval
  · right
    intro w hw hw0
    obtain ⟨s,t,rfl⟩ := hspan w hw
    have hn : (s,t) ≠ (0,0) := by rintro h; obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; simp at hw0
    have hval := hd s t hn
    rw [← quad] at hval
    simpa [H, iteratedFDeriv_two_apply] using hval

/-- Decomposition of a real-linear map of the complex plane into its complex-linear
and conjugate-linear terms. -/
theorem complex_linear_decomposition (L : ℂ →L[ℝ] ℂ) (z : ℂ) :
    L z = ((L 1 - Complex.I * L Complex.I)/2)*z +
      ((L 1 + Complex.I * L Complex.I)/2)*(starRingEnd ℂ z) := by
  have he : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  conv_lhs => rw [he, map_add, map_smul, map_smul]
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- The determinant of a real-linear map is the difference of squared mode lengths. -/
theorem complex_linear_determinant (u v : ℂ) :
    ‖(u - Complex.I * v)/2‖^2 - ‖(u + Complex.I * v)/2‖^2 =
      u.re*v.im - u.im*v.re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- In complex plane coordinates, the dipole moment is nonzero for neutral charges. -/
theorem neutral_chart_moment (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : AffineIndependent ℝ a)
    (hq : q 0 ≠ 0) (hQ : ∑ i, q i = 0) : (∑ i, q i • siteCoordinate a ha i) ≠ 0 := by
  intro h
  have he := congrArg (fun z : ℂ => (planeAxes a ha z : E)) h
  simp only [map_sum, map_smul, map_zero, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
    siteCoordinate, LinearIsometryEquiv.apply_symm_apply, smul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_smul, hQ, zero_smul, sub_zero] at he
  exact neutral_dipole_ne_zero a q ha hq hQ he

/-- At all sufficiently small reciprocal radii the scaled field is dominated by
a single winding mode. The neutral case has a strictly dominant second mode. -/
theorem farField_dominant (q : Fin 3 → ℝ) (s : Fin 3 → ℂ)
    (hp : ∑ i, q i = 0 → (∑ i, q i • s i) ≠ 0) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ k : ℤ, 1 ≤ k ∧
    ∀ᶠ t in 𝓝 (0:ℝ), 0 < t → ∃ d : ℝ, 0 < d ∧ ∀ u : Circle,
      ‖d • (∑ i, (-q i / ‖(t⁻¹ • (u:ℂ))-s i‖^3) • ((t⁻¹ • (u:ℂ))-s i)) -
        c * (u:ℂ)^k‖ < ‖c‖ := by
  let Q := ∑ i, q i
  let p := ∑ i, q i • s i
  have hscale (t : ℝ) (ht : 0 < t) (u : Circle) :
      farField q s t (u:ℂ) =
        (1/t^2) • ∑ i, (-q i / ‖(t⁻¹ • (u:ℂ))-s i‖^3) • ((t⁻¹ • (u:ℂ))-s i) := by
    simpa [smul_smul, ht.ne'] using rescale_force q s (t⁻¹ • (u:ℂ)) t ht
  by_cases hQ : Q = 0
  · have hpn := hp hQ
    let c := -3 * starRingEnd ℂ p / 2
    have hgap : ‖-p/2‖ < ‖c‖ := by
      norm_num [c,norm_div,norm_mul,norm_neg,RCLike.norm_conj]
      nlinarith [norm_pos_iff.mpr hpn]
    refine ⟨c,norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap),2,by decide,?_⟩
    have hh : ∀ᶠ t in 𝓝 (0:ℝ), ∀ u ∈ (Set.univ : Set Circle),
        ‖dipoleField q s t (u:ℂ) - c*(u:ℂ)^2‖ < ‖c‖ ∧ ∀ i, (u:ℂ)-t • s i ≠ 0 := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro u _
      have hcont : ContinuousAt (fun z : ℝ × Circle => dipoleField q s z.1 (z.2:ℂ)) (0,u) := by
        apply continuous_sum_at
        intro i _
        unfold correction
        fun_prop (disch := simp [Circle.norm_coe])
      have hlim : ‖dipoleField q s 0 (u:ℂ) - c*(u:ℂ)^2‖ < ‖c‖ := by
        rw [dipoleField_zero _ _ _ (Circle.norm_coe _),complex_dipole]
        simpa [c,p] using hgap
      have hcont' : ContinuousAt (fun z : ℝ × Circle =>
          ‖dipoleField q s z.1 (z.2:ℂ) - c*(z.2:ℂ)^2‖) (0,u) := by fun_prop
      apply (hcont'.eventually_lt continuousAt_const hlim).and
      apply Filter.eventually_all.mpr
      intro i
      exact ContinuousAt.eventually_ne (g := fun z : ℝ × Circle => (z.2:ℂ)-z.1 • s i)
        (by fun_prop) (by simp)
    filter_upwards [hh] with t ht ht0
    refine ⟨t⁻¹*(1/t^2),by positivity,fun u => ?_⟩
    have he := hscale t ht0 u
    rw [neutral_farField _ _ hQ _ _ (Circle.norm_coe _) (ht u trivial).2] at he
    rw [mul_smul, ← he, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
    simpa using (ht u trivial).1
  · refine ⟨(-Q:ℝ),by exact_mod_cast neg_ne_zero.mpr hQ,1,le_rfl,?_⟩
    have hh : ∀ᶠ t in 𝓝 (0:ℝ), ∀ u ∈ (Set.univ : Set Circle),
        ‖farField q s t (u:ℂ) - (-Q:ℝ) • (u:ℂ)‖ < ‖(-Q:ℝ)‖ := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro u _
      have hcont : ContinuousAt (fun z : ℝ × Circle => farField q s z.1 (z.2:ℂ)) (0,u) := by
        apply continuous_sum_at
        intro i _
        fun_prop (disch := simp)
      have hc : ContinuousAt (fun z : ℝ × Circle => ‖farField q s z.1 (z.2:ℂ) -
          (-Q:ℝ) • (z.2:ℂ)‖) (0,u) := by fun_prop
      apply hc.eventually_lt continuousAt_const
      simp only [farField, zero_smul, sub_zero, Circle.norm_coe, one_pow, div_one,
        ← Finset.sum_smul, Finset.sum_neg_distrib, Q, sub_self, norm_zero]
      exact norm_pos_iff.mpr (neg_ne_zero.mpr hQ)
    filter_upwards [hh] with t ht ht0
    refine ⟨1/t^2,by positivity,fun u => ?_⟩
    rw [← hscale t ht0 u]
    simpa [Complex.real_smul] using ht u trivial

/-- The planar force derivative is the restriction of the ambient Hessian in
the orthonormal chart. Its determinant is nonzero at nondegenerate equilibria,
and a positive determinant gives a restricted extremum. -/
theorem chart_linearization (q : Fin 3 → ℝ) (a : Fin 3 → E) (ha : AffineIndependent ℝ a)
    {z : ℂ} (hz : planePoint a ha z ∈ equilibria q a)
    (hnd : HasNondegenerateHessianAt (potential q a) (planePoint a ha z)) :
    ∃ L : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w => ∑ i, (-q i / ‖w-siteCoordinate a ha i‖^3) • (w-siteCoordinate a ha i)) L z ∧
      let D := (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re
      D ≠ 0 ∧ (0 < D → IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E)
        (planePoint a ha z)) := by
  let s := siteCoordinate a ha
  let x := planePoint a ha z
  let T := planeAxes a ha
  let L := ∑ i, hessTerm (q i) (z-s i)
  have hp : x ∈ affineSpan ℝ (Set.range a) := by
    change x ∈ (affineSpan ℝ (Set.range a) : Set E)
    rw [← range_planePoint _ ha]
    exact ⟨z,rfl⟩
  have hsrc := ((plane_equilibrium_iff q a ha z).mp hz).1
  refine ⟨L, HasFDerivAt.fun_sum (fun i _ => force_derivative (q i) (fun e => hsrc ⟨i,e.symm⟩)),?_⟩
  have hT (u v : ℂ) : ⟪(T u : E),(T v : E)⟫_ℝ = ⟪u,v⟫_ℝ := T.inner_map_map u v
  have hx (i : Fin 3) : planePoint a ha z-a i = (T (z-s i) : E) := by
    simp [planePoint,T,s,siteCoordinate,map_sub]
    abel
  have hbil (u v : ℂ) :
      iteratedFDeriv ℝ 2 (potential q a) x ![(T u : E),(T v : E)] = ⟪L u,v⟫_ℝ := by
    rw [potential_hessian _ _ hz.1]
    simp only [L,sum_apply, sum_inner, hx, hT,
      show ∀ w : ℂ, ‖(T w : E)‖ = ‖w‖ from T.norm_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hessTerm,add_apply,smul_apply,
      ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,
      inner_add_left,real_inner_smul_left,smul_eq_mul,mul_assoc]
  have hs (u v : ℂ) : ⟪L u,v⟫_ℝ = ⟪L v,u⟫_ℝ := by
    rw [← hbil,← hbil,potential_hessian _ _ hz.1,potential_hessian _ _ hz.1]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (T u : E) (T v : E)]
    ring
  have hinj {w : ℂ} (hw : L w = 0) : w = 0 := by
    by_contra h
    have htw : (T w : E) ≠ 0 := by
      intro he
      apply h
      exact T.injective (Subtype.ext (he.trans (by simp)))
    obtain ⟨v,hv,hv'⟩ := planar_hessian_nondegenerate _ _ hz.1 hp hnd _ (T w).2 htw
    let v' := T.symm ⟨v,hv⟩
    have hV : (T v' : E) = v := by simp [v']
    exact hv' (by rw [← hV,hbil,hw,inner_zero_left])
  have hsym : (L 1).im = (L Complex.I).re := by simpa [Complex.inner] using hs 1 Complex.I
  have hrep (w : ℂ) : w = w.re • (1:ℂ) + w.im • Complex.I := by
    apply Complex.ext <;> simp
  constructor
  · intro he
    have hcol : L 1 ≠ 0 := fun h => one_ne_zero (hinj h)
    have hkernel (u v : ℝ) (h : u • L 1 + v • L Complex.I = 0) : u = 0 ∧ v = 0 := by
      have H := hinj (w := u • 1 + v • Complex.I) (by simpa only [map_add,map_smul] using h)
      exact ⟨by simpa using congrArg Complex.re H, by simpa using congrArg Complex.im H⟩
    have h1 := hkernel (-(L Complex.I).re) (L 1).re (by
      apply Complex.ext <;> simp <;> nlinarith only [he])
    have h2 := hkernel (-(L Complex.I).im) (L 1).im (by
      apply Complex.ext <;> simp <;> nlinarith only [he])
    exact hcol (Complex.ext (by simpa using h1.2) (by simpa using h2.2))
  · intro hd
    apply planar_extr_of_positive_det q a hz hp (T 1) (T Complex.I)
    · intro w hw
      let v := T.symm ⟨w,hw⟩
      refine ⟨v.re,v.im,?_⟩
      have he := congrArg (fun y : ℂ => (T y : E)) (hrep v)
      simpa only [map_add,map_smul,Submodule.coe_add,Submodule.coe_smul,v,
        LinearIsometryEquiv.apply_symm_apply] using he
    · rw [hbil,hbil,hbil]
      simpa [Complex.inner,hsym,pow_two] using hd

end MaxwellIndexCount

end

section

namespace MaxwellIndexCount

open Arxiv.«2607.27197» Filter Set InnerProductSpace
open scoped BigOperators Topology unitInterval RealInnerProductSpace

/-- Clearing the Coulomb denominators by a positive factor off the sites
turns the three poles into ordinary simple zeros. -/
noncomputable def regularForce (q : Fin 3 → ℝ) (s : Fin 3 → ℂ) (z : ℂ) : ℂ :=
  ∑ i, ((-q i) * ∏ j ∈ Finset.univ.erase i, ‖z-s j‖^3) • (z-s i)

theorem regularForce_continuous (q : Fin 3 → ℝ) (s : Fin 3 → ℂ) :
    Continuous (regularForce q s) := by
  unfold regularForce
  fun_prop

theorem regularForce_off_sites (q : Fin 3 → ℝ) (s : Fin 3 → ℂ) {z : ℂ}
    (hz : z ∉ range s) :
    regularForce q s z = (∏ j, ‖z-s j‖^3) •
      ∑ i, (-q i / ‖z-s i‖^3) • (z-s i) := by
  rw [regularForce, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i), smul_smul]
  congr 1
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => hz ⟨i,h.symm⟩)
  field_simp [hn]

theorem regularForce_site (q : Fin 3 → ℝ) (s : Fin 3 → ℂ) (i : Fin 3) :
    regularForce q s (s i) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = i
  · simp [hj]
  · have he : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hj,Finset.mem_univ _⟩
    have hh : (∏ k ∈ Finset.univ.erase j, ‖s i - s k‖^3) = 0 :=
      Finset.prod_eq_zero he (by simp)
    simp [hh]

theorem regularForce_zero_iff (q : Fin 3 → ℝ) (a : Fin 3 → EuclideanSpace ℝ (Fin 3))
    (ha : AffineIndependent ℝ a) (z : ℂ) :
    regularForce q (siteCoordinate a ha) z = 0 ↔
      z ∈ range (siteCoordinate a ha) ∨ planePoint a ha z ∈ equilibria q a := by
  by_cases hz : z ∈ range (siteCoordinate a ha)
  · obtain ⟨i,rfl⟩ := hz
    simp [regularForce_site]
  · rw [regularForce_off_sites _ _ hz, plane_equilibrium_iff, or_iff_right hz,
      and_iff_right hz, smul_eq_zero, or_iff_right]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h => hz ⟨i,h.symm⟩))

private theorem normCube_deriv_zero (b : ℂ) :
    HasFDerivAt (𝕜 := ℝ) (fun z : ℂ => ‖z-b‖^3) 0 b := by
  rw [hasFDerivAt_iff_isLittleO]
  simp only [sub_self, norm_zero, zero_pow (by decide : 3 ≠ 0), sub_zero,
    zero_apply]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have h : ContinuousAt (fun z : ℂ => ‖z-b‖^2) b := by fun_prop
  filter_upwards [h.eventually_lt (g := fun _ => ε) continuousAt_const (by simpa using hε)] with z hz
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _), pow_succ]
  exact mul_le_mul_of_nonneg_right hz.le (norm_nonneg _)

theorem regularForce_hasFDerivAt_site (q : Fin 3 → ℝ) (s : Fin 3 → ℂ)
    (hs : Function.Injective s) (i : Fin 3) :
    HasFDerivAt (regularForce q s)
      (((-q i) * ∏ j ∈ Finset.univ.erase i, ‖s i - s j‖^3) • ContinuousLinearMap.id ℝ ℂ)
      (s i) := by
  classical
  let f (j : Fin 3) (z : ℂ) := ((-q j) * ∏ k ∈ Finset.univ.erase j, ‖z-s k‖^3) • (z-s j)
  have own : HasFDerivAt (f i)
      (((-q i) * ∏ j ∈ Finset.univ.erase i, ‖s i - s j‖^3) • ContinuousLinearMap.id ℝ ℂ)
      (s i) := by
    have hc : DifferentiableAt ℝ (fun z : ℂ => (-q i) * ∏ j ∈ Finset.univ.erase i,
        ‖z-s j‖^3) (s i) := by
      apply DifferentiableAt.const_mul
      apply HasFDerivAt.differentiableAt
      apply HasFDerivAt.finsetProd
      intro j hj
      exact (((differentiableAt_id.sub_const _).norm ℝ
        (sub_ne_zero.mpr (hs.ne (Finset.ne_of_mem_erase hj).symm))).pow 3).hasFDerivAt
    simpa only [f,id_eq, sub_self, ContinuousLinearMap.smulRight_zero, add_zero] using hc.hasFDerivAt.fun_smul ((hasFDerivAt_id (𝕜 := ℝ) (s i)).sub_const (s i))
  have other (j : Fin 3) (hj : j ≠ i) : HasFDerivAt (𝕜 := ℝ) (f j) 0 (s i) := by
    let B := (Finset.univ.erase j).erase i
    have hi : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨Ne.symm hj,Finset.mem_univ _⟩
    let g (z : ℂ) := ((-q j) * ∏ k ∈ B, ‖z-s k‖^3) • (z-s j)
    have hg : DifferentiableAt ℝ g (s i) := by
      unfold g
      apply DifferentiableAt.smul (c := fun z : ℂ => (-q j) * ∏ k ∈ B, ‖z-s k‖^3) (f := fun z : ℂ => z-s j) _ (differentiableAt_id.sub_const (s j))
      apply DifferentiableAt.const_mul
      apply HasFDerivAt.differentiableAt
      apply HasFDerivAt.finsetProd
      intro k hk
      exact (((differentiableAt_id.sub_const _).norm ℝ
        (sub_ne_zero.mpr (hs.ne (Finset.ne_of_mem_erase hk).symm))).pow 3).hasFDerivAt
    have he : f j = fun z => ‖z-s i‖^3 • g z := by
      funext z
      simp only [f,g,B]
      rw [← Finset.prod_erase_mul _ _ hi, smul_smul]
      congr 1
      ring
    rw [he]
    simpa only [sub_self,norm_zero,zero_pow (by decide : 3 ≠ 0),zero_smul,ContinuousLinearMap.zero_smulRight,add_zero,zero_add] using (normCube_deriv_zero (s i)).fun_smul hg.hasFDerivAt
  have h := own.add (HasFDerivAt.fun_sum (u := Finset.univ.erase i)
    (fun j hj => other j (Finset.ne_of_mem_erase hj)))
  have he : regularForce q s = (f i + fun z => ∑ j ∈ Finset.univ.erase i, f j z) := by
    funext z
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [he]
  simpa only [Finset.sum_const_zero,add_zero] using h

/-- If the image near each isolated zero lies in a closed half-plane through
zero, a compactly supported perturbation can remove all zeros. -/
theorem remove_halfPlane_zeros (B : Finset ℂ) (F : C(ℂ,ℂ))
    (hzero : ∀ z, F z = 0 → z ∈ B)
    (hhalf : ∀ b ∈ B, ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in 𝓝 b, 0 ≤ ⟪c,F z⟫_ℝ) :
    ∃ G : C(ℂ,ℂ), (∀ z, G z ≠ 0) ∧ ∃ R : ℝ, ∀ z, R ≤ ‖z‖ → G z = F z := by
  classical
  induction B using Finset.induction_on generalizing F with
  | empty =>
    exact ⟨F,fun z hz => Finset.notMem_empty z (hzero z hz),0,fun _ _ => rfl⟩
  | @insert b B hb ih =>
    obtain ⟨c,hc,hh⟩ := hhalf b (Finset.mem_insert_self b B)
    have havoid : ∀ᶠ z in 𝓝 b, z ∉ B :=
      B.finite_toSet.isClosed.isOpen_compl.mem_nhds hb
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hh.and havoid)
    let ρ (z : ℂ) := max 0 (r/2-dist z b)
    let F' : C(ℂ,ℂ) := ⟨fun z => F z + ρ z • c, by dsimp [ρ]; fun_prop⟩
    have houter {z : ℂ} (hz : r/2 ≤ dist z b) : F' z = F z := by
      change F z + max 0 (r/2-dist z b) • c = F z
      rw [max_eq_left (sub_nonpos.mpr hz), zero_smul, add_zero]
    have hzero' (z : ℂ) (hz : F' z = 0) : z ∈ B := by
      by_cases h : r/2 ≤ dist z b
      · rw [houter h] at hz
        rcases Finset.mem_insert.mp (hzero z hz) with rfl | hm
        · simp at h
          linarith
        · exact hm
      · have ht := lt_of_not_ge h
        have hinner := (hball (Metric.mem_ball.mpr (lt_trans ht (by linarith)))).1
        have hρ : 0 < ρ z := lt_of_lt_of_le (sub_pos.mpr ht) (le_max_right _ _)
        have hp := mul_pos hρ (real_inner_self_pos.mpr hc)
        change F z + ρ z • c = 0 at hz
        have he := congrArg (fun w : ℂ => ⟪c,w⟫_ℝ) hz
        simp only [inner_add_right, real_inner_smul_right, inner_zero_right] at he
        linarith
    have hhalf' (d : ℂ) (hd : d ∈ B) :
        ∃ c : ℂ, c ≠ 0 ∧ ∀ᶠ z in 𝓝 d, 0 ≤ ⟪c,F' z⟫_ℝ := by
      obtain ⟨v,hv,hv'⟩ := hhalf d (Finset.mem_insert_of_mem hd)
      have hdist : r ≤ dist d b := le_of_not_gt fun h => (hball (Metric.mem_ball.mpr h)).2 hd
      have hn : ∀ᶠ z in 𝓝 d, r/2 < dist z b :=
        continuousAt_const.eventually_lt (continuous_id.dist continuous_const).continuousAt
          (by linarith)
      exact ⟨v,hv, (hv'.and hn).mono fun z h => (houter h.2.le).symm ▸ h.1⟩
    obtain ⟨G,hG,R,hR⟩ := ih F' hzero' hhalf'
    refine ⟨G,hG,max R (‖b‖+r),fun z hz => (hR z (le_of_max_le_left hz)).trans (houter ?_)⟩
    have ht := norm_sub_norm_le z b
    rw [dist_eq_norm]
    linarith [le_of_max_le_right hz]

/-- Every loop in a globally nonsingular planar field has zero angle change. -/
theorem angleChange_global_field (G : C(ℂ,ℂ)) (hG : ∀ z, G z ≠ 0)
    (γ : C(unitInterval,ℂ)) (hγ : γ 0 = γ 1) :
    angleChange ((direction G hG).comp γ) = 0 := by
  let D := direction G hG
  let H : C(unitInterval × unitInterval,Circle) :=
    D.comp ⟨fun p => (p.1 : ℝ) • γ p.2, by fun_prop⟩
  have hh := angleChange_homotopy H (fun t => by
    change D ((t:ℝ) • γ 0) = D ((t:ℝ) • γ 1)
    rw [hγ])
  have h1 : along H (fun t => (1,t)) (by fun_prop) = D.comp γ := by
    ext t : 1
    change D ((1:ℝ) • γ t) = D (γ t)
    rw [one_smul]
  have h0 : along H (fun t => (0,t)) (by fun_prop) = ContinuousMap.const _ (D 0) := by
    ext t : 1
    change D ((0:ℝ) • γ t) = D 0
    rw [zero_smul]
  rw [h1,h0] at hh
  rw [hh, angleChange_of_lift _ (ContinuousMap.const _ ((D 0 : ℂ).arg))]
  · simp
  · exact fun _ => Circle.exp_arg _

noncomputable def signedCoord (positive : Bool) (z : ℂ) : ℂ :=
  if positive then z else starRingEnd ℂ z

private theorem signedCoord_norm (p : Bool) (z : ℂ) : ‖signedCoord p z‖ = ‖z‖ := by
  cases p <;> simp [signedCoord]

private theorem signedCoord_continuous (p : Bool) : Continuous (signedCoord p) := by
  cases p <;> unfold signedCoord <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop

/-- A zero whose linear term has a dominant mode can be cancelled by a factor of
opposite orientation. Multiplication by a continuous nonzero cofactor preserves
the local half-plane condition. -/
theorem cancelled_zero_halfPlane (F A : ℂ → ℂ) (b c : ℂ) (p : Bool) (d : ℝ)
    (_hc : c ≠ 0) (hd : d < ‖c‖) (hA : ContinuousAt A b) (hA0 : A b ≠ 0)
    (h : ∀ᶠ z in 𝓝 b, ‖F z - c * signedCoord p (z-b)‖ ≤ d * ‖z-b‖) :
    ∀ᶠ z in 𝓝 b, 0 ≤ ⟪c*A b, F z * starRingEnd ℂ (signedCoord p (z-b)) * A z⟫_ℝ := by
  have hc' : ContinuousAt (fun z => d * ‖A z‖ + ‖c‖ * ‖A z-A b‖) b := by fun_prop
  have hh : d * ‖A b‖ + ‖c‖ * ‖A b-A b‖ < ‖c*A b‖ := by
    simpa [norm_mul] using mul_lt_mul_of_pos_right hd (norm_pos_iff.mpr hA0)
  filter_upwards [h, hc'.eventually_lt continuousAt_const hh] with z hz he
  let w := signedCoord p (z-b)
  let v := c*A b
  let u := F z * starRingEnd ℂ w * A z
  let r := ‖z-b‖
  have hw : ‖w‖ = r := signedCoord_norm _ _
  have hsq : w * starRingEnd ℂ w = ((r^2:ℝ):ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
  have hid : u - (r^2) • v =
      (F z - c*w) * starRingEnd ℂ w * A z + (r^2) • (c*(A z-A b)) := by
    dsimp [u,v]
    simp only [Complex.ofReal_pow] at *
    linear_combination c * A z * hsq
  have hbound : ‖u - (r^2) • v‖ ≤ (r^2) * ‖v‖ := by
    rw [hid]
    calc
      _ ≤ _ := norm_add_le _ _
      _ = ‖F z - c*w‖ * (r*‖A z‖) + r^2*(‖c‖*‖A z-A b‖) := by
        simp [hw, Real.norm_eq_abs, mul_assoc]
      _ ≤ (d*r) * (r*‖A z‖) + r^2*(‖c‖*‖A z-A b‖) :=
        add_le_add_left (mul_le_mul_of_nonneg_right hz (mul_nonneg (norm_nonneg _) (norm_nonneg _))) _
      _ = r^2 * (d*‖A z‖ + ‖c‖*‖A z-A b‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left he.le (sq_nonneg r)
  have hh' := (real_inner_le_norm v ((r^2) • v-u)).trans
      (mul_le_mul_of_nonneg_left ((norm_sub_rev _ _).le.trans hbound) (norm_nonneg v))
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hh'
  change 0 ≤ ⟪v,u⟫_ℝ
  linarith only [hh']

/-- A single orientation factor at each zero cancels all local winding.
The resulting field extends without zeros after a bounded perturbation. -/
theorem cancel_signed_zeros (B : Finset ℂ) (p : ℂ → Bool) (F : C(ℂ,ℂ))
    (hz : ∀ z, F z = 0 → z ∈ B)
    (hm : ∀ b ∈ B, ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧
      ∀ᶠ z in 𝓝 b, ‖F z-c*signedCoord (p b) (z-b)‖ ≤ d*‖z-b‖) :
    ∃ G : C(ℂ,ℂ), (∀ z, G z ≠ 0) ∧ ∃ R : ℝ, ∀ z, R ≤ ‖z‖ →
      G z = F z * ∏ b ∈ B, starRingEnd ℂ (signedCoord (p b) (z-b)) := by
  classical
  let K (b z : ℂ) := starRingEnd ℂ (signedCoord (p b) (z-b))
  have hK (b : ℂ) : Continuous (K b) := by
    exact Complex.continuous_conj.comp ((signedCoord_continuous _).comp (continuous_id.sub continuous_const))
  have hn {b z : ℂ} (h : z ≠ b) : K b z ≠ 0 := by
    have hnorm : ‖K b z‖ = ‖z-b‖ := by simp [K,signedCoord_norm]
    exact norm_ne_zero_iff.mp (hnorm ▸ norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))
  let T : C(ℂ,ℂ) := ⟨fun z => F z * ∏ b ∈ B, K b z, by fun_prop⟩
  apply remove_halfPlane_zeros B T
  · intro z h
    by_contra h'
    exact (mul_ne_zero (fun h => h' (hz z h)) (Finset.prod_ne_zero_iff.mpr
      (fun b hb => hn (b := b) (z := z) (fun e => h' (e.symm ▸ hb))))) h
  · intro b hb
    let A (z : ℂ) := ∏ j ∈ B.erase b, K j z
    obtain ⟨c,d,hc,hd,hm⟩ := hm b hb
    have hA : Continuous A := by dsimp [A]; fun_prop
    have hA0 : A b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
      hn (Finset.ne_of_mem_erase hj).symm
    refine ⟨c*A b,mul_ne_zero hc hA0,?_⟩
    filter_upwards [cancelled_zero_halfPlane F A b c (p b) d hc hd hA.continuousAt hA0 hm] with z h
    convert h using 2
    change F z * ∏ j ∈ B, K j z = F z * K b z * A z
    rw [← Finset.prod_erase_mul _ _ hb]
    dsimp [A]
    ring

/-- Angle change of a complex path after normalization. -/
noncomputable def loopAngle (f : C(unitInterval,ℂ)) : ℝ := by
  classical exact if h : ∀ t, f t ≠ 0 then angleChange (direction f h) else 0

theorem loopAngle_mul (f g : C(unitInterval,ℂ)) (hf : ∀ t, f t ≠ 0) (hg : ∀ t, g t ≠ 0) :
    loopAngle (f*g) = loopAngle f + loopAngle g := by
  have hfg : ∀ t, (f*g) t ≠ 0 := fun t => mul_ne_zero (hf t) (hg t)
  have he : direction (f*g) hfg = direction f hf * direction g hg := by
    ext t : 2
    change f t * g t / (↑‖f t * g t‖ : ℂ) = f t / ↑‖f t‖ * (g t / ↑‖g t‖)
    rw [norm_mul,Complex.ofReal_mul]
    ring
  simp [loopAngle,hf,hg,he,angleChange_mul]

private theorem loopAngle_prod {ι : Type*} (B : Finset ι) (f : ι → C(unitInterval,ℂ))
    (hf : ∀ b ∈ B, ∀ t, f b t ≠ 0) :
    loopAngle (∏ b ∈ B, f b) = ∑ b ∈ B, loopAngle (f b) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    have he : (1 : C(unitInterval,ℂ)) = modelLoop 1 0 := by ext; simp [modelLoop]
    rw [he]
    simp [loopAngle, modelLoop_ne_zero one_ne_zero,modelLoop_angleChange one_ne_zero]
  | @insert a B ha ih =>
    have hB := fun b hb => hf b (Finset.mem_insert_of_mem hb)
    rw [Finset.prod_insert ha,Finset.sum_insert ha,loopAngle_mul,ih hB]
    · exact hf a (Finset.mem_insert_self _ _)
    · intro t
      simpa using Finset.prod_ne_zero_iff.mpr (fun b hb => hB b hb t)

private theorem conjugate_modelLoop (r : ℝ) (t : unitInterval) :
    starRingEnd ℂ (modelLoop (r:ℂ) 1 t) = modelLoop (r:ℂ) (-1) t := by
  change starRingEnd ℂ ((r:ℂ) * ↑(Circle.exp _)) = (r:ℂ) * ↑(Circle.exp _)
  rw [map_mul,Complex.conj_ofReal,← Circle.coe_inv_eq_conj,← Circle.exp_neg]
  congr 3
  push_cast
  ring

/-- On a circle enclosing b, a linear factor about b contributes one turn
and its conjugate contributes minus one turn. -/
theorem cancelFactor_angle (b : ℂ) {r : ℝ} (hr : ‖b‖ < r) (p : Bool) :
    let γ := modelLoop (r:ℂ) 1
    let f : C(unitInterval,ℂ) := ⟨fun t => starRingEnd ℂ (signedCoord p (γ t-b)),
      Complex.continuous_conj.comp ((signedCoord_continuous _).comp (γ.continuous.sub continuous_const))⟩
    (∀ t, f t ≠ 0) ∧ loopAngle f = (if p then (-1:ℤ) else 1) * (2*Real.pi) := by
  intro γ f
  have hr0 := lt_of_le_of_lt (norm_nonneg b) hr
  have aux (v : ℂ) (hv : ‖v‖ = ‖b‖) (k : ℤ)
      (he : f = ContinuousMap.const _ (-v) + modelLoop (r:ℂ) k) :
      (∀ t, f t ≠ 0) ∧ loopAngle f = k * (2*Real.pi) := by
    obtain ⟨hn,hh⟩ := translated_model_angleChange (-v) (r:ℂ) k
      (by simpa [hv,abs_of_pos hr0] using hr)
    rw [he]
    exact ⟨hn,by simpa only [loopAngle, dif_pos hn] using hh⟩
  cases p
  · apply aux b rfl 1
    ext t : 1
    simp [f,signedCoord,γ,sub_eq_add_neg,add_comm]
  · apply aux (starRingEnd ℂ b) (RCLike.norm_conj _) (-1)
    ext t : 1
    simp [f,signedCoord,γ,conjugate_modelLoop,sub_eq_add_neg,add_comm]

/-- Planar index balance on sufficiently large circles, derived from cancellation
of the individual signed factors at all zeros of a continuous field. -/
theorem signed_index_balance (B : Finset ℂ) (p : ℂ → Bool) (F : C(ℂ,ℂ))
    (hz : ∀ z, F z = 0 → z ∈ B)
    (hm : ∀ b ∈ B, ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧
      ∀ᶠ z in 𝓝 b, ‖F z-c*signedCoord (p b) (z-b)‖ ≤ d*‖z-b‖) :
    ∃ R : ℝ, ∀ r ≥ R, loopAngle (F.comp (modelLoop (r:ℂ) 1)) =
      (∑ b ∈ B, if p b then (1:ℤ) else -1) * (2*Real.pi) := by
  classical
  obtain ⟨G,hG,S,hS⟩ := cancel_signed_zeros B p F hz hm
  let M := ∑ b ∈ B, ‖b‖
  refine ⟨max S (M+1),fun r hr => ?_⟩
  have hM : M+1 ≤ r := le_of_max_le_right hr
  have hpos : 0 < r := by
    have h : 0 ≤ M := Finset.sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hb (b : ℂ) (hm : b ∈ B) : ‖b‖ < r := by
    have h := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun i _ => norm_nonneg i) hm
    change ‖b‖ ≤ M at h
    linarith
  let γ := modelLoop (r:ℂ) 1
  have hγ (t : unitInterval) : ‖γ t‖ = r := by
    change ‖(r:ℂ) * ((Circle.exp _) : ℂ)‖ = r
    rw [norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  let K (b : ℂ) : C(unitInterval,ℂ) := ⟨fun t => starRingEnd ℂ (signedCoord (p b) (γ t-b)),
    Complex.continuous_conj.comp ((signedCoord_continuous _).comp (γ.continuous.sub continuous_const))⟩
  have hKn (b : ℂ) (hm : b ∈ B) := (cancelFactor_angle b (hb b hm) (p b)).1
  have hnF (t : unitInterval) : F.comp γ t ≠ 0 := by
    intro he
    have h := hb _ (hz _ he)
    rw [hγ] at h
    exact lt_irrefl _ h
  have hE : G.comp γ = (F.comp γ) * ∏ b ∈ B, K b := by
    ext t : 1
    simpa [K] using hS (γ t) ((hγ t).symm ▸ le_of_max_le_left hr)
  have h0 : loopAngle (G.comp γ) = 0 := by
    rw [loopAngle, dif_pos (show ∀ t, G.comp γ t ≠ 0 from fun t => hG _)]
    exact
      angleChange_global_field G hG γ (modelLoop_closed _ _)
  rw [hE,loopAngle_mul _ _ hnF (fun t => by
    rw [ContinuousMap.prod_apply]
    exact Finset.prod_ne_zero_iff.mpr (fun b hb => hKn b hb t)),loopAngle_prod B K hKn] at h0
  have hi (b : ℂ) (h : b ∈ B) :
      loopAngle (K b) = -((if p b then (1:ℤ) else -1):ℝ) * (2*Real.pi) := by
    rw [(cancelFactor_angle b (hb b h) (p b)).2]
    cases p b <;> norm_num
  rw [Finset.sum_congr rfl hi] at h0
  push_cast
  rw [← Finset.sum_mul, Finset.sum_neg_distrib] at h0
  change loopAngle (F.comp γ) = _
  norm_num at h0 ⊢
  linarith

/-- A nondegenerate real derivative at a zero selects its signed mode
uniformly throughout a neighborhood. -/
theorem derivative_dominates_mode (f : ℂ → ℂ) {z : ℂ} {L : ℂ →L[ℝ] ℂ}
    (hf : HasFDerivAt f L z) (hz : f z = 0)
    (D : ℝ) (hD : D = (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re)
    (hn : D ≠ 0) :
    ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧
      ∀ᶠ w in 𝓝 z, ‖f w - c*signedCoord (decide (0<D)) (w-z)‖ ≤ d*‖w-z‖ := by
  let A := (L 1 - Complex.I * L Complex.I)/2
  let B := (L 1 + Complex.I * L Complex.I)/2
  have hAB : ‖A‖^2 - ‖B‖^2 = D := (complex_linear_determinant _ _).trans hD.symm
  have approx (p : Bool) (c e : ℂ) (hgap : ‖e‖ < ‖c‖)
      (hlin : ∀ x, ‖L x - c*signedCoord p x‖ = ‖e‖*‖x‖) :
      ∃ d : ℝ, d < ‖c‖ ∧ ∀ᶠ w in 𝓝 z, ‖f w-c*signedCoord p (w-z)‖ ≤ d*‖w-z‖ := by
    let ε := (‖c‖-‖e‖)/2
    have hε : 0 < ε := half_pos (sub_pos.mpr hgap)
    refine ⟨ε+‖e‖,by dsimp [ε]; linarith,?_⟩
    filter_upwards [hf.isLittleO.bound hε] with w hw
    change ‖f w - f z - L (w-z)‖ ≤ ε*‖w-z‖ at hw
    rw [hz,sub_zero] at hw
    calc
      _ ≤ ‖f w-L (w-z)‖ + ‖L (w-z)-c*signedCoord p (w-z)‖ := by
        simpa only [dist_eq_norm] using dist_triangle (f w) (L (w-z)) (c*signedCoord p (w-z))
      _ ≤ _ := by rw [hlin,add_mul]; exact add_le_add_left hw _
  by_cases hp : 0 < D
  · have hgap : ‖B‖ < ‖A‖ := by nlinarith [norm_nonneg A,norm_nonneg B]
    obtain ⟨d,hd,hh⟩ := approx true A B hgap (fun x => by
      rw [complex_linear_decomposition L x]
      simp [A,B,signedCoord])
    exact ⟨A,d,norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap),hd,by simpa [hp] using hh⟩
  · have hgap : ‖A‖ < ‖B‖ := by nlinarith [norm_nonneg A,norm_nonneg B,lt_of_le_of_ne (le_of_not_gt hp) hn]
    obtain ⟨d,hd,hh⟩ := approx false B A hgap (fun x => by
      rw [complex_linear_decomposition L x]
      simp [A,B,signedCoord])
    exact ⟨B,d,norm_pos_iff.mp ((norm_nonneg _).trans_lt hgap),hd,by simpa [hp] using hh⟩

private theorem unit_direction_smul (v : ℂ) (d : ℝ) (hd : 0 < d) :
    (d • v) / (↑‖d • v‖ : ℂ) = v / ↑‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, Complex.ofReal_mul, Complex.real_smul]
  exact mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hd.ne')

/-- The actual regularized field winds at least once on every sufficiently large circle. -/
theorem outer_index_lower (q : Fin 3 → ℝ) (s : Fin 3 → ℂ)
    (hp : ∑ i, q i = 0 → (∑ i, q i • s i) ≠ 0) :
    let F : C(ℂ,ℂ) := ⟨regularForce q s, regularForce_continuous q s⟩
    ∀ᶠ r : ℝ in atTop, 2*Real.pi ≤ loopAngle (F.comp (modelLoop (r:ℂ) 1)) := by
  intro F
  obtain ⟨c,hc,k,hk,hh⟩ := farField_dominant q s hp
  filter_upwards [tendsto_inv_atTop_zero.eventually hh, eventually_gt_atTop (∑ i, ‖s i‖)] with r hr hR
  have hr0 : 0 < r := (Finset.sum_nonneg fun i _ => norm_nonneg (s i)).trans_lt hR
  obtain ⟨d,hd,hm⟩ := hr (inv_pos.mpr hr0)
  let γ := modelLoop (r:ℂ) 1
  let u (t : unitInterval) := Circle.exp (2*Real.pi*(t:ℝ))
  have hγ (t : unitInterval) : γ t = r • (u t:ℂ) := by
    change (r:ℂ) * ↑(Circle.exp ((1:ℤ)*(2*Real.pi)*(t:ℝ))) = (r:ℂ)* ↑(u t)
    simp [u]
  have hs (t : unitInterval) (i : Fin 3) : γ t ≠ s i := by
    have hnorm : ‖γ t‖ = r := by rw [hγ,norm_smul,Real.norm_eq_abs,abs_of_pos hr0,Circle.norm_coe,mul_one]
    intro he
    rw [he] at hnorm
    have h := Finset.single_le_sum (f := fun i => ‖s i‖) (fun i _ => norm_nonneg (s i)) (Finset.mem_univ i)
    linarith
  let f (z : ℂ) := ∑ i, (-q i / ‖z-s i‖^3) • (z-s i)
  let g : C(unitInterval,ℂ) := ⟨fun t => d • f (γ t),by
    apply continuous_const.fun_smul
    apply continuous_finsetSum
    intro i _
    fun_prop (disch := exact fun t => pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs t i))))⟩
  have hmode (t : unitInterval) : modelLoop c k t = c*(u t:ℂ)^k := by
    change c*↑(Circle.exp ((k:ℝ)*(2*Real.pi)*(t:ℝ))) = c*(u t:ℂ)^k
    rw [mul_assoc,Circle.exp_intCast_mul,Circle.coe_zpow]
  have hsmall (t : unitInterval) : ‖g t-modelLoop c k t‖ < ‖modelLoop c k t‖ := by
    change ‖d • f (γ t)-_‖ < _
    rw [hmode,hγ,norm_mul,norm_zpow,Circle.norm_coe,one_zpow,mul_one]
    simpa only [inv_inv] using hm (u t)
  have hg (t : unitInterval) : g t ≠ 0 := by
    intro he
    have hh := hsmall t
    simp [he] at hh
  have hv (t : unitInterval) : f (γ t) ≠ 0 := fun he => hg t (by change d • f (γ t) = 0; rw [he,smul_zero])
  let κ (t : unitInterval) := ∏ i, ‖γ t-s i‖^3
  have hκ (t : unitInterval) : 0 < κ t := Finset.prod_pos fun i _ =>
    pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hs t i))) _
  have hF (t : unitInterval) : F.comp γ t = κ t • f (γ t) :=
    regularForce_off_sites _ _ (by rintro ⟨i,hi⟩; exact hs t i hi.symm)
  have hn (t : unitInterval) : F.comp γ t ≠ 0 := by rw [hF]; exact smul_ne_zero (hκ t).ne' (hv t)
  have he : direction (F.comp γ) hn = direction g hg := by
    ext t : 2
    change F.comp γ t / ↑‖F.comp γ t‖ = (d • f (γ t)) / ↑‖d • f (γ t)‖
    rw [hF,unit_direction_smul _ _ (hκ t),unit_direction_smul _ _ hd]
  change 2*Real.pi ≤ loopAngle (F.comp γ)
  rw [loopAngle,dif_pos hn,he,angleChange_of_dominant_mode g
    (by change d • f (γ 0) = d • f (γ 1); rw [show γ 0 = γ 1 from modelLoop_closed _ _]) hc k hg hsmall]
  exact le_mul_of_one_le_left (by positivity) (by exact_mod_cast hk)

private abbrev Space := EuclideanSpace ℝ (Fin 3)

private theorem regular_equilibrium_mode (q : Fin 3 → ℝ) (a : Fin 3 → Space)
    (ha : AffineIndependent ℝ a) {z : ℂ} (hz : planePoint a ha z ∈ equilibria q a)
    (hnd : HasNondegenerateHessianAt (potential q a) (planePoint a ha z)) :
    ∃ p : Bool, (p = true → IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set Space)
      (planePoint a ha z)) ∧ ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧
      ∀ᶠ w in 𝓝 z, ‖regularForce q (siteCoordinate a ha) w - c*signedCoord p (w-z)‖ ≤ d*‖w-z‖ := by
  let s := siteCoordinate a ha
  let f (w : ℂ) := ∑ i, (-q i / ‖w-s i‖^3) • (w-s i)
  obtain ⟨hsrc,hzero⟩ := (plane_equilibrium_iff q a ha z).mp hz
  obtain ⟨L,hL,hD,hpos⟩ := chart_linearization q a ha hz hnd
  let D := (L 1).re * (L Complex.I).im - (L 1).im * (L Complex.I).re
  let κ (w : ℂ) := ∏ i, ‖w-s i‖^3
  have hs (i : Fin 3) : z ≠ s i := fun e => hsrc ⟨i,e.symm⟩
  have hk : 0 < κ z := Finset.prod_pos fun i _ => pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (hs i))) _
  have hκ : DifferentiableAt ℝ κ z := by
    apply HasFDerivAt.differentiableAt
    apply HasFDerivAt.finsetProd
    intro i _
    exact (((differentiableAt_id.sub_const _).norm ℝ (sub_ne_zero.mpr (hs i))).pow 3).hasFDerivAt
  have hder : HasFDerivAt (regularForce q s) (κ z • L) z := by
    have hprod := hκ.hasFDerivAt.smul hL
    simp only [hzero,ContinuousLinearMap.smulRight_zero,add_zero] at hprod
    apply hprod.congr_of_eventuallyEq
    filter_upwards [(Set.finite_range s).isClosed.isOpen_compl.mem_nhds hsrc] with w hw
    exact regularForce_off_sites _ _ hw
  have he : κ z ^2 * D = ((κ z • L) 1).re * ((κ z • L) Complex.I).im -
      ((κ z • L) 1).im * ((κ z • L) Complex.I).re := by
    simp [D,Complex.mul_re,Complex.mul_im]
    ring
  refine ⟨decide (0 < κ z ^2 * D),fun hp => hpos ?_,?_⟩
  · exact (mul_pos_iff_of_pos_left (sq_pos_of_pos hk)).mp (of_decide_eq_true hp)
  · exact derivative_dominates_mode _ hder ((regularForce_zero_iff q a ha z).mpr (Or.inr hz))
      _ he (mul_ne_zero (pow_ne_zero _ hk.ne') hD)

private theorem regular_site_mode (q : Fin 3 → ℝ) (s : Fin 3 → ℂ) (hs : Function.Injective s)
    (i : Fin 3) (hq : q i ≠ 0) :
    ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧ ∀ᶠ w in 𝓝 (s i),
      ‖regularForce q s w - c*signedCoord true (w-s i)‖ ≤ d*‖w-s i‖ := by
  let k := (-q i) * ∏ j ∈ Finset.univ.erase i, ‖s i-s j‖^3
  have hk : k ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hq) (Finset.prod_ne_zero_iff.mpr fun j hj =>
    pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hs.ne (Finset.ne_of_mem_erase hj).symm))))
  have he : k^2 = ((k • ContinuousLinearMap.id ℝ ℂ) 1).re * ((k • ContinuousLinearMap.id ℝ ℂ) Complex.I).im -
      ((k • ContinuousLinearMap.id ℝ ℂ) 1).im * ((k • ContinuousLinearMap.id ℝ ℂ) Complex.I).re := by
    simp [pow_two]
  simpa only [decide_eq_true (sq_pos_of_ne_zero hk)] using derivative_dominates_mode _
    (regularForce_hasFDerivAt_site q s hs i) (regularForce_site q s i) _ he (pow_ne_zero _ hk)

/-- The planar equilibrium count is at most twice the number of planar extrema plus two. -/
theorem index_count_bound :
    ∀ (q : Fin 3 → ℝ) (a : Fin 3 → EuclideanSpace ℝ (Fin 3)),
      AffineIndependent ℝ a → (∀ i, q i ≠ 0) →
      (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
      let P := (affineSpan ℝ (Set.range a) : Set (EuclideanSpace ℝ (Fin 3)))
      let e := {x | x ∈ P ∧ x ∈ equilibria q a ∧ IsLocalExtrOn (potential q a) P x}.encard
      {x | x ∈ P ∧ x ∉ Set.range a ∧
        (∑ i, (-q i / ‖x - a i‖ ^ 3) • (x - a i)) = 0}.encard ≤ 2 * e + 2 := by
  classical
  intro q a ha hq hnd
  apply bound_of_signed_equilibria q a ha hq hnd
  let s := siteCoordinate a ha
  let φ := planePoint a ha
  let P := (affineSpan ℝ (Set.range a) : Set Space)
  let X := {x | x ∈ P ∧ x ∈ equilibria q a ∧ IsLocalExtrOn (potential q a) P x}
  have hφ := (planePoint_isometry a ha).injective
  have hs : Function.Injective s := by
    intro i j he
    apply ha.injective
    simpa only [s,planePoint_site] using congrArg (planePoint a ha) he
  let Z := (equilibria_finite q a ha hq hnd).toFinset.filter (· ∈ P)
  let C := ((equilibria_finite q a ha hq hnd).preimage hφ.injOn).toFinset
  let S := Finset.univ.image s
  let B := S ∪ C
  let F : C(ℂ,ℂ) := ⟨regularForce q s,regularForce_continuous _ _⟩
  have hC (z : ℂ) : z ∈ C ↔ φ z ∈ equilibria q a := by simp [C,φ]
  have hS (z : ℂ) : z ∈ S ↔ z ∈ range s := by simp [S,Set.mem_range]
  have dis : Disjoint S C := Finset.disjoint_left.mpr fun z hz he =>
    ((plane_equilibrium_iff q a ha z).mp ((hC z).mp he)).1 ((hS z).mp hz)
  have hP (z : ℂ) : φ z ∈ P := by rw [show P = range φ from (range_planePoint a ha).symm]; exact ⟨z,rfl⟩
  have him : C.image φ = Z := by
    ext x
    simp only [Finset.mem_image, Z,Finset.mem_filter,Set.Finite.mem_toFinset,hC]
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨hz,hP z⟩
    · rintro ⟨hz,hp⟩
      rw [show P = range φ from (range_planePoint a ha).symm] at hp
      obtain ⟨z,rfl⟩ := hp
      exact ⟨z,hz,rfl⟩
  have hmode (z : ℂ) (hb : z ∈ B) : ∃ p : Bool, (p = true → z ∈ S ∨ φ z ∈ X) ∧
      ∃ c : ℂ, ∃ d : ℝ, c ≠ 0 ∧ d < ‖c‖ ∧ ∀ᶠ w in 𝓝 z,
      ‖F w - c*signedCoord p (w-z)‖ ≤ d*‖w-z‖ := by
    rcases Finset.mem_union.mp hb with hz | hz
    · obtain ⟨i,rfl⟩ := (hS z).mp hz
      exact ⟨true,fun _ => Or.inl hz,regular_site_mode q s hs i (hq i)⟩
    · have he := (hC z).mp hz
      obtain ⟨p,hp,hh⟩ := regular_equilibrium_mode q a ha he (hnd _ he)
      exact ⟨p,fun ht => Or.inr ⟨hP z,he,hp ht⟩,hh⟩
  let p (z : ℂ) := if hb : z ∈ B then (hmode z hb).choose else false
  have hspec (z : ℂ) (hb : z ∈ B) := (hmode z hb).choose_spec
  have hz (z : ℂ) (he : F z = 0) : z ∈ B := by
    simpa only [B,Finset.mem_union,hS,hC] using (regularForce_zero_iff q a ha z).mp he
  obtain ⟨R,hR⟩ := signed_index_balance B p F hz (fun z hb => by simpa [p,hb] using (hspec z hb).2)
  obtain ⟨r,hr,ho⟩ := ((eventually_ge_atTop R).and
    (outer_index_lower q s (neutral_chart_moment q a ha (hq 0)))).exists
  change 2*Real.pi ≤ loopAngle (F.comp (modelLoop (r:ℂ) 1)) at ho
  rw [hR r hr] at ho
  let v (z : ℂ) : ℤ := if p z then 1 else -1
  have htotal : (1:ℤ) ≤ ∑ z ∈ B, v z := by
    have hh : (1:ℝ) ≤ (↑(∑ z ∈ B, v z):ℝ) := (le_of_mul_le_mul_right (by simpa only [one_mul] using ho : 1*(2*Real.pi) ≤ _) (by positivity : 0 < 2*Real.pi))
    exact_mod_cast hh
  have hsumS : ∑ z ∈ S, v z ≤ 3 := calc
    _ ≤ ∑ _z ∈ S, (1:ℤ) := Finset.sum_le_sum fun z _ => by dsimp [v]; split <;> decide
    _ = 3 := by simp [S,Finset.card_image_of_injective _ hs]
  have hsumC : ∑ z ∈ C, v z ≤ ∑ z ∈ C, (if φ z ∈ X then (1:ℤ) else -1) := by
    apply Finset.sum_le_sum
    intro z he
    by_cases hx : φ z ∈ X
    · simp only [hx,if_true,v]; split <;> decide
    · have hb : z ∈ B := Finset.mem_union_right _ he
      have hn : p z ≠ true := by
        intro ht
        have ht' : (hmode z hb).choose = true := by simpa [p,hb] using ht
        exact ((hspec z hb).1 ht').elim (fun hs => Finset.disjoint_left.mp dis hs he) hx
      simp [v,hx,hn]
  rw [show B = S ∪ C from rfl,Finset.sum_union dis] at htotal
  change (-2:ℤ) ≤ ∑ x ∈ Z, (if x ∈ X then (1:ℤ) else -1)
  rw [← him,Finset.sum_image (fun _ _ _ _ h => hφ h)]
  change (-2:ℤ) ≤ ∑ z ∈ C, (if φ z ∈ X then (1:ℤ) else -1)
  omega

end MaxwellIndexCount

end

section

noncomputable section
open Set Filter Topology

namespace MaxwellCausticExtremum.ForceSection

abbrev Q := Fin 3 → ℝ
abbrev P := (Q × ℝ) × ℝ

def tangent (k : ℝ) : P := ((0,1),k)
def transverse : P := ((0,0),1)

private theorem between {I : Set ℝ} (hI : I.OrdConnected) (f d e j : ℝ → ℝ)
    (df : ∀ t ∈ I, HasDerivAt f (d t) t) (dd : ∀ t ∈ I, HasDerivAt d (e t) t)
    (de : ∀ t ∈ I, HasDerivAt e (j t) t)
    (sign : (∀ t ∈ I, 0<e t) ∨ (∀ t ∈ I, e t<0) ∨ (∀ t ∈ I, j t<0))
    {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) (da : 0 ≤ d a) (db : 0 ≤ d b)
    (eq : f a=f b) : a=b := by
  have noReturn (x y : ℝ) (hx : x ∈ I) (hy : y ∈ I) (hxy : x<y) (px : 0≤d x) (py : 0≤d y)
      (same : f x=f y) : False := by
    have inc := hI.out hx hy
    obtain ⟨m,hm,dm⟩ := exists_hasDerivAt_eq_zero hxy (fun t ht => (df t (inc ht)).continuousAt.continuousWithinAt)
      same (fun t ht => df t (inc (Ioo_subset_Icc_self ht)))
    have mI := inc (Ioo_subset_Icc_self hm)
    have slope {a b : ℝ} (aI : a ∈ I) (bI : b ∈ I) (ab : a<b) (g h : ℝ → ℝ)
        (dh : ∀ t ∈ I, HasDerivAt g (h t) t) : ∃ t ∈ Ioo a b, h t=(g b-g a)/(b-a) :=
      exists_hasDerivAt_eq_slope g h ab (fun t ht => (dh t (hI.out aI bI ht)).continuousAt.continuousWithinAt)
        (fun t ht => dh t (hI.out aI bI (Ioo_subset_Icc_self ht)))
    obtain ⟨l,hl,el⟩ := slope hx mI hm.1 d e dd
    obtain ⟨r,hr,er⟩ := slope mI hy hm.2 d e dd
    have lI := hI.out hx mI (Ioo_subset_Icc_self hl)
    have rI := hI.out mI hy (Ioo_subset_Icc_self hr)
    have le : e l≤0 := el.trans_le (div_nonpos_of_nonpos_of_nonneg (by linarith only [px,dm]) (by linarith only [hm.1]))
    have re : 0≤e r := er ▸ div_nonneg (by linarith only [py,dm]) (by linarith only [hm.2])
    rcases sign with pos|neg|curv
    · exact (pos _ lI).not_ge le
    · exact (neg _ rI).not_ge re
    · have lr := hl.2.trans hr.1
      obtain ⟨w,hw,ew⟩ := slope lI rI lr e j de
      have nw := curv w (hI.out lI rI (Ioo_subset_Icc_self hw))
      exact nw.not_ge (ew ▸ div_nonneg (le.trans re |> sub_nonneg.mpr) (sub_nonneg.mpr lr.le))
  rcases lt_trichotomy a b with h|h|h
  · exact (noReturn a b ha hb h da db eq).elim
  · exact h
  · exact (noReturn b a hb ha h db da eq.symm).elim

/-- The last three fields are consecutive derivatives of the remaining
force component along the transverse equation. At the base either its second
derivative is nonzero, or its third derivative is negative. -/
theorem local_unique (B A d e j k : P → ℝ) (b : P) (zero : B b=0)
    (smooth : ContDiffAt ℝ 1 B b)
    (unit : fderiv ℝ B b transverse=1)
    (jets : ∀ᶠ p in 𝓝 b,
      DifferentiableAt ℝ B p ∧ DifferentiableAt ℝ A p ∧ DifferentiableAt ℝ d p ∧ DifferentiableAt ℝ e p ∧
      fderiv ℝ B p transverse ≠ 0 ∧ fderiv ℝ B p (tangent (k p))=0 ∧
      fderiv ℝ A p (tangent (k p))=d p ∧ fderiv ℝ d p (tangent (k p))=e p ∧
      fderiv ℝ e p (tangent (k p))=j p)
    (turn : (∀ᶠ p in 𝓝 b, 0<e p) ∨ (∀ᶠ p in 𝓝 b, e p<0) ∨ (∀ᶠ p in 𝓝 b, j p<0)) :
    ∃ U ∈ 𝓝 b, ∀ p ∈ U, ∀ q ∈ U, p.1.1=q.1.1 → B p=0 → B q=0 →
      0≤d p → 0≤d q → A p=A q → p=q := by
  let L := (fderiv ℝ B b).comp (ContinuousLinearMap.inr ℝ (Q × ℝ) ℝ)
  have id : L=ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro t
    change fderiv ℝ B b ((0,0),t)=t
    rw [show (((0,0),t) : P)=t • transverse by simp [transverse],map_smul,unit]; simp
  have inv : L.IsInvertible := id ▸ ContinuousLinearMap.isInvertible_equiv (f := ContinuousLinearEquiv.refl ℝ ℝ)
  let f := smooth.implicitFunction (by simp) inv
  have cf : ContDiffAt ℝ 1 f b.1 := smooth.contDiffAt_implicitFunction (by simp) inv
  have fb : f b.1=b.2 := smooth.implicitFunction_apply_self (by simp) inv
  let graph (u : Q × ℝ) : P := (u,f u)
  have atb : graph b.1=b := Prod.ext rfl fb
  have tend : Tendsto graph (𝓝 b.1) (𝓝 b) := by
    rw [← atb]; exact continuousAt_id.prodMk cf.continuousAt
  have imp : ∀ᶠ u in 𝓝 b.1, B (graph u)=0 :=
    (smooth.eventually_apply_implicitFunction (by simp) inv).mono (fun _ h => h.trans zero)
  have localF : ∀ᶠ p in 𝓝 b, B p=0 → f p.1=p.2 :=
    (smooth.eventually_apply_eq_iff_implicitFunction (by simp) inv).mono
      (fun _ he hz => he.mp (hz.trans zero.symm))
  have jetG : ∀ᶠ u : Q × ℝ in 𝓝 b.1,
      HasDerivAt (fun t => A (graph (u.1,t))) (d (graph u)) u.2 ∧
      HasDerivAt (fun t => d (graph (u.1,t))) (e (graph u)) u.2 ∧
      HasDerivAt (fun t => e (graph (u.1,t))) (j (graph u)) u.2 := by
    filter_upwards [tend jets,imp.eventually_nhds,cf.eventually (by simp)] with u hp hi diff
    obtain ⟨dB,dA,dd,de,nv,zt,at',dt,et⟩ := hp
    let v := fderiv ℝ f u (0,1)
    have param : HasDerivAt (fun t : ℝ => (u.1,t)) (0,1) u.2 := (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
    have slope : HasDerivAt (fun t => f (u.1,t)) v u.2 :=
      (diff.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt u.2 param
    have curve : HasDerivAt (fun t => graph (u.1,t)) (tangent v) u.2 := param.prodMk slope
    have along : ∀ᶠ t in 𝓝 u.2, B (graph (u.1,t))=0 := param.continuousAt hi
    have z := (dB.hasFDerivAt.comp_hasDerivAt u.2 curve).unique
      ((hasDerivAt_const u.2 (0:ℝ)).congr_of_eventuallyEq along)
    have C : tangent v=tangent (k (graph u))+(v-k (graph u)) • transverse := by
      simp [tangent,transverse]
    rw [C,map_add,map_smul,zt,zero_add,smul_eq_mul] at z
    have ve := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_right nv)
    rw [ve] at curve
    exact ⟨(dA.hasFDerivAt.comp_hasDerivAt u.2 curve).congr_deriv at',
      (dd.hasFDerivAt.comp_hasDerivAt u.2 curve).congr_deriv dt,
      (de.hasFDerivAt.comp_hasDerivAt u.2 curve).congr_deriv et⟩
  let good (D : P → Prop) (ev : ∀ᶠ p in 𝓝 b, D p)
      (kind : (∀ p, D p → 0<e p) ∨ (∀ p, D p → e p<0) ∨ (∀ p, D p → j p<0)) :
      ∃ U ∈ 𝓝 b, ∀ p ∈ U, ∀ q ∈ U, p.1.1=q.1.1 → B p=0 → B q=0 →
        0≤d p → 0≤d q → A p=A q → p=q := by
    obtain ⟨U,hU,V,hV,all⟩ := mem_nhds_prod_iff.mp (jetG.and (tend ev))
    obtain ⟨lo,hi,hx,inc⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
    let N := (Prod.fst ⁻¹' (U ×ˢ Ioo lo hi)) ∩ {p : P | B p=0 → f p.1=p.2}
    refine ⟨N,inter_mem (continuous_fst.continuousAt.preimage_mem_nhds
      (prod_mem_nhds hU (Ioo_mem_nhds hx.1 hx.2))) localF,?_⟩
    rintro ⟨⟨a,x⟩,y⟩ hp ⟨⟨a',x'⟩,y'⟩ hq same Bp Bq dp dq eq
    change a=a' at same
    subst a'
    have cu (t : ℝ) (ht : t ∈ Ioo lo hi) := all (show (a,t) ∈ U ×ˢ V from ⟨hp.1.1,inc ht⟩)
    have gy := hp.2 Bp
    have gy' := hq.2 Bq
    change f (a,x)=y at gy
    change f (a,x')=y' at gy'
    subst y; subst y'
    have ex : x=x' := between inferInstance (fun t => A (graph (a,t))) (fun t => d (graph (a,t)))
      (fun t => e (graph (a,t))) (fun t => j (graph (a,t)))
      (fun t ht => (cu t ht).1.1) (fun t ht => (cu t ht).1.2.1) (fun t ht => (cu t ht).1.2.2)
      (kind.imp (fun h t ht => h _ (cu t ht).2) (fun h => h.imp
        (fun h t ht => h _ (cu t ht).2) (fun h t ht => h _ (cu t ht).2))) hp.1.2 hq.1.2 dp dq eq
    rw [ex]
  rcases turn with h|h|h
  · exact good _ h (Or.inl (fun _ H => H))
  · exact good _ h (Or.inr (Or.inl (fun _ H => H)))
  · exact good _ h (Or.inr (Or.inr (fun _ H => H)))

end MaxwellCausticExtremum.ForceSection

end
end

section

namespace MaxwellCusp.Spatial

abbrev Triple := Fin 3 → ℝ

def minor (x y : Triple) (i j : Fin 3) := x i*y j - y i*x j

def K (x y : Triple) (i : Fin 3) :=
  2*x (i+1)*x (i+2) + y (i+1)*y (i+2)

/-- In an orthonormal null frame the three second moments determine each
weight. Projective minors are valid for vertical directions as well. -/
theorem weight_identity (l x y : Triple)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i = 0)
    (yy : ∑ i, l i*y i^2 = 2/3) (i : Fin 3) :
    3*l i*minor x y i (i+1)*minor x y i (i+2) = K x y i := by
  simp only [Fin.sum_univ_three] at xx xy yy
  let j := i+1
  let k := i+2
  have e : 3*(∑ n, l n * (x n*y j-y n*x j)*(x n*y k-y n*x k)) = K x y i := by
    simp only [Fin.sum_univ_three,K,j,k]
    linear_combination 3*y (i+1)*y (i+2)*xx -
      3*(x (i+1)*y (i+2)+y (i+1)*x (i+2))*xy + 3*x (i+1)*x (i+2)*yy
  fin_cases i <;> simp [Fin.sum_univ_three,minor,j,k] at e ⊢ <;> linarith only [e]

/-- The force equations make the three length scales equal. -/
theorem common_scale (l r x y : Triple) (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (sep : ∀ i j, i ≠ j → minor x y i j ≠ 0)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i = 0) (yy : ∑ i, l i*y i^2 = 2/3)
    (fx : ∑ i, l i*r i*x i = 0) (fy : ∑ i, l i*r i*y i = 0) :
    ∃ κ : ℝ, κ ≠ 0 ∧ ∀ i, r i*K x y i = κ := by
  have w := weight_identity l x y xx xy yy
  refine ⟨r 0*K x y 0,mul_ne_zero (hr 0) ?_,?_⟩
  · rw [← w]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hl 0))
      (sep _ _ (by decide))) (sep _ _ (by decide))
  · intro i
    rw [← w,← w]
    simp only [Fin.sum_univ_three] at fx fy
    fin_cases i
    · rfl
    · dsimp [minor]
      linear_combination 3*(x 1*y 0-y 1*x 0)*(y 2*fx-x 2*fy)
    · dsimp [minor]
      linear_combination 3*(x 2*y 0-y 2*x 0)*(y 1*fx-x 1*fy)

def D (x : Triple) := x 0*x 1*x 2
def A (x y : Triple) := y 0*x 1*x 2 + x 0*y 1*x 2 + x 0*x 1*y 2
def B (x y : Triple) := y 0*y 1*x 2 + y 0*x 1*y 2 + x 0*y 1*y 2
def C (y : Triple) := y 0*y 1*y 2

/-- Derivative of the null-null entry of the normalized Hessian. Here the
directions point from the field point towards the three sites; b is the
barycentric velocity and (u,v) the Cartesian velocity in the null frame. -/
noncomputable def nullDerivative (l b r x y : Triple) (u v : ℝ) :=
  3*∑ i, (b i*x i^2 + 2*l i*x i*(x i*(x i*u+y i*v)-u)/r i)

theorem gradient_identity (l b r x y : Triple) (κ u v : ℝ)
    (unit : ∀ i, x i^2+y i^2=1) (hr : ∀ i, r i ≠ 0)
    (scale : ∀ i, r i*K x y i = κ) (mass : ∑ i, b i = 0)
    (bx : ∑ i, b i*r i*x i = u) (by' : ∑ i, b i*r i*y i = v)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i = 0)
    (yy : ∑ i, l i*y i^2 = 2/3) :
    κ*nullDerivative l b r x y u v =
      2*(B x y-2*D x)*u + (C y-2*A x y)*v := by
  let α := 4*D x + 2*B x y
  let β := -2*A x y-C y
  have aff (i : Fin 3) : K x y i*(3*x i^2-1) = α*x i+β*y i := by
    have e := unit i
    have a : K x y i*(3*x i^2-1) - (α*x i+β*y i) =
        K x y i*(x i^2+y i^2-1) := by
      fin_cases i <;> dsimp [α,β,D,A,B,C,K] <;> ring
    linarith only [a,show K x y i*(x i^2+y i^2-1) = 0 by rw [e]; ring]
  have single (i : Fin 3) :
      3*κ*(b i*x i^2 + 2*l i*x i*(x i*(x i*u+y i*v)-u)/r i) =
      κ*b i + α*(b i*r i*x i) + β*(b i*r i*y i) +
      6*l i*(-(2*D x*y i^2+C y*x i*y i)*u+(2*D x*x i*y i+C y*x i^2)*v) := by
    have ku : K x y i*x i*y i^2 = 2*D x*y i^2+C y*x i*y i := by
      fin_cases i <;> dsimp [K,D,C] <;> ring
    have kv : K x y i*x i^2*y i = 2*D x*x i*y i+C y*x i^2 := by
      fin_cases i <;> dsimp [K,D,C] <;> ring
    rw [← scale i,← ku,← kv]
    field_simp [hr i]
    linear_combination b i*r i*(aff i) +
      6*l i*K x y i*x i*u*(unit i)
  have total := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => single i)
  simp only [Fin.sum_univ_three] at total mass bx by' xx xy yy
  unfold nullDerivative
  simp only [Fin.sum_univ_three]
  dsimp [α,β] at total
  linear_combination total + κ*mass + (4*D x+2*B x y)*bx + (-2*A x y-C y)*by' -
    12*D x*u*yy - 6*C y*u*xy + 12*D x*v*xy + 6*C y*v*xx

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

noncomputable section

/-- Squared-radius quotient for one summand of the Hessian along a line. -/
def summand (l b r x y u v t : ℝ) :=
  (l+t*b)*(r*x-t*u)^2 / ((r*x-t*u)^2+(r*y-t*v)^2)

private theorem summand_deriv (l b r x y u v : ℝ) (hr : r ≠ 0) (hu : x^2+y^2=1) :
    HasDerivAt (summand l b r x y u v)
      (b*x^2+2*l*x*(x*(x*u+y*v)-u)/r) 0 := by
  have line (a w : ℝ) : HasDerivAt (fun t : ℝ => a-t*w) (-w) 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const w).const_sub a)
  have wt : HasDerivAt (fun t : ℝ => l+t*b) b 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const b).const_add l)
  have dx := (line (r*x) u).pow 2
  have dy := (line (r*y) v).pow 2
  have rad : (r*x)^2+(r*y)^2=r^2 := by linear_combination r^2*hu
  have h := (wt.mul dx).div (dx.add dy) (by simpa [rad] using pow_ne_zero 2 hr)
  convert! h using 1
  simp [Pi.pow_apply,Pi.mul_apply,Pi.add_apply,rad]
  field_simp [hr]
  ring

def lineXX (l b r x y : Triple) (u v t : ℝ) :=
  3*(∑ i, summand (l i) (b i) (r i) (x i) (y i) u v t)-1

theorem lineXX_deriv (l b r x y : Triple) (u v : ℝ) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) :
    HasDerivAt (lineXX l b r x y u v) (nullDerivative l b r x y u v) 0 :=
  ((HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    summand_deriv (l i) (b i) (r i) (x i) (y i) u v (hr i) (unit i))).const_mul 3).sub_const 1

def lineXY (l b r x y : Triple) (u v t : ℝ) :=
  3*∑ i, (l i+t*b i)*(r i*x i-t*u)*(r i*y i-t*v) /
    ((r i*x i-t*u)^2+(r i*y i-t*v)^2)

def lineDet (l b r x y : Triple) (u v t : ℝ) :=
  lineXX l b r x y u v t * lineXX l b r y x v u t - lineXY l b r x y u v t ^ 2

/-- At the critical point the eigenvalues are zero and one. The product
rule therefore leaves precisely the derivative of the null-null entry. -/
theorem lineDet_deriv (l b r x y : Triple) (u v : ℝ) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (xx : ∑ i, l i*x i^2 = 1/3)
    (xy : ∑ i, l i*x i*y i = 0) (yy : ∑ i, l i*y i^2 = 2/3) :
    HasDerivAt (lineDet l b r x y u v) (nullDerivative l b r x y u v) 0 := by
  have rad (i : Fin 3) : (r i*x i)^2+(r i*y i)^2 = r i^2 := by
    linear_combination r i^2*unit i
  have initial (a c : Triple) (w z : ℝ) (e : ∀ i, a i^2+c i^2=1) :
      lineXX l b r a c w z 0 = 3*(∑ i, l i*a i^2)-1 := by
    unfold lineXX
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    have eq : (r i*a i)^2+(r i*c i)^2=r i^2 := by linear_combination r i^2*e i
    simp only [summand,zero_mul,add_zero,sub_zero,eq]
    field_simp [hr i]
  have rev (i : Fin 3) : y i^2+x i^2=1 := (add_comm ..).trans (unit i)
  have ha : lineXX l b r x y u v 0 = 0 := by rw [initial _ _ _ _ unit,xx]; norm_num
  have hc : lineXX l b r y x v u 0 = 1 := by rw [initial _ _ _ _ rev,yy]; norm_num
  have hb : lineXY l b r x y u v 0 = 0 := by
    unfold lineXY
    have he (i : Fin 3) : (l i+0*b i)*(r i*x i-0*u)*(r i*y i-0*v) /
        ((r i*x i-0*u)^2+(r i*y i-0*v)^2) = l i*x i*y i := by
      simp only [zero_mul,add_zero,sub_zero,rad]
      field_simp [hr i]
    simp only [he,xy,mul_zero]
  have db : DifferentiableAt ℝ (lineXY l b r x y u v) 0 := by
    unfold lineXY
    fun_prop (disch := simp [rad,hr])
  have d := ((lineXX_deriv l b r x y u v hr unit).mul
    (lineXX_deriv l b r y x v u hr rev)).sub (db.hasDerivAt.pow 2)
  convert! d using 1
  simp [ha,hb,hc]

end
end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

def mixedDerivative (x y : Triple) (u v : ℝ) := -4*A x y*u+(6*D x-B x y)*v

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

noncomputable def mixedEntryDerivative (l b r x y : Triple) (u v : ℝ) :=
  3*∑ i, (b i*x i*y i + l i*(2*x i*y i*(x i*u+y i*v)-u*y i-v*x i)/r i)

/-- Differential of the mixed Hessian entry, whose negative is the angular
speed of the null axis on the critical curve. -/
theorem mixed_identity (l b r x y : Triple) (κ u v : ℝ)
    (unit : ∀ i, x i^2+y i^2=1) (hr : ∀ i, r i ≠ 0)
    (scale : ∀ i, r i*K x y i = κ)
    (bx : ∑ i, b i*r i*x i = u) (by' : ∑ i, b i*r i*y i = v)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i = 0)
    (yy : ∑ i, l i*y i^2 = 2/3) :
    κ*mixedEntryDerivative l b r x y u v = mixedDerivative x y u v := by
  let P := fun i => -C y*x i^2 -
    (C y+2*A x y)*y i^2 + (2*D x+2*B x y)*x i*y i
  let Q := fun i => D x*y i^2 - (2*D x+B x y)*x i^2 +
    (C y+A x y)*x i*y i
  have affine (i : Fin 3) : 3*K x y i*x i*y i = 3*C y*x i+6*D x*y i := by
    fin_cases i <;> dsimp [C,D,K] <;> ring
  have pu (i : Fin 3) : K x y i*(2*x i^2*y i-y i) = P i := by
    have e : K x y i*(2*x i^2*y i-y i)-P i = K x y i*y i*(x i^2+y i^2-1) := by
      fin_cases i <;> dsimp [P,D,C,A,B,K] <;> ring
    rw [unit i] at e
    linarith only [e]
  have qv (i : Fin 3) : K x y i*(2*x i*y i^2-x i) = Q i := by
    have e : K x y i*(2*x i*y i^2-x i)-Q i = K x y i*x i*(x i^2+y i^2-1) := by
      fin_cases i <;> dsimp [Q,D,C,A,B,K] <;> ring
    rw [unit i] at e
    linarith only [e]
  have term (i : Fin 3) :
      3*κ*(b i*x i*y i + l i*(2*x i*y i*(x i*u+y i*v)-u*y i-v*x i)/r i) =
      3*C y*(b i*r i*x i) + 6*D x*(b i*r i*y i) + 3*l i*(P i*u+Q i*v) := by
    rw [← scale i,← pu,← qv]
    field_simp [hr i]
    linear_combination b i*r i*(affine i)
  have total := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => term i)
  simp only [Fin.sum_univ_three] at total bx by' xx xy yy
  simp only [mixedEntryDerivative,Fin.sum_univ_three,mixedDerivative]
  dsimp [P,Q] at total
  linear_combination total + 3*C y*bx + 6*D x*by' +
    3*u*(-C y*xx-(C y+2*A x y)*yy+(2*D x+2*B x y)*xy) +
    3*v*(D x*yy-(2*D x+B x y)*xx+(C y+A x y)*xy)

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

/-- Taking the squared modulus of the product of three complex direction
factors yields a positive formula for the gradient coefficients. -/
theorem gradient_norm (x y : Triple) :
    2*(B x y-2*D x)^2+(C y-2*A x y)^2 =
      (2*x 0^2+y 0^2)*(2*x 1^2+y 1^2)*(2*x 2^2+y 2^2) := by
  dsimp [A,B,C,D]
  ring

/-- The determinant has a nonzero spatial derivative in a null frame. -/
theorem regular_in_null_frame (l r x y : Triple) (b : ℝ → ℝ → Triple)
    (unit : ∀ i, x i^2+y i^2=1) (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (sep : ∀ i j, i ≠ j → minor x y i j ≠ 0)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3)
    (fx : ∑ i, l i*r i*x i=0) (fy : ∑ i, l i*r i*y i=0)
    (bm : ∀ u v, ∑ i, b u v i=0)
    (bx : ∀ u v, ∑ i, b u v i*r i*x i=u) (by' : ∀ u v, ∑ i, b u v i*r i*y i=v)
    :
    deriv (lineDet l (b 1 0) r x y 1 0) 0 ≠ 0 ∨
      deriv (lineDet l (b 0 1) r x y 0 1) 0 ≠ 0 := by
  obtain ⟨κ,_,scale⟩ := common_scale l r x y hl hr sep xx xy yy fx fy
  have grad (u v : ℝ) := gradient_identity l (b u v) r x y κ u v unit hr scale
    (bm u v) (bx u v) (by' u v) xx xy yy
  simp only [(lineDet_deriv l _ r x y _ _ hr unit xx xy yy).deriv]
  by_contra! ez
  have dx := grad 1 0
  have dy := grad 0 1
  rw [ez.1] at dx
  rw [ez.2] at dy
  have eb : B x y = 2*D x := by linarith
  have ec : C y = 2*A x y := by linarith
  have pos (i : Fin 3) : 0 < 2*x i^2+y i^2 := by nlinarith only [unit i,sq_nonneg (x i)]
  have e := gradient_norm x y
  rw [eb,ec] at e
  nlinarith only [e,mul_pos (mul_pos (pos 0) (pos 1)) (pos 2)]

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

noncomputable def cubicNull (l r x : Triple) :=
  ∑ i, l i*(15*x i^3-9*x i)/r i

noncomputable def cubicMixed (l r x y : Triple) :=
  ∑ i, l i*(15*x i^2*y i-3*y i)/r i

noncomputable def quarticNull (l r x : Triple) :=
  ∑ i, l i*(105*x i^4-90*x i^2+9)/r i^2

private theorem scaled_jets (l r x y : Triple) (κ : ℝ) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ) :
    κ*cubicNull l r x = ∑ i, l i*(K x y i*(6*x i^3-9*x i*y i^2)) ∧
    κ*cubicMixed l r x y = ∑ i, l i*(K x y i*(12*x i^2*y i-3*y i^3)) ∧
    κ^2*quarticNull l r x = ∑ i, l i*((K x y i)^2*(24*x i^4-72*x i^2*y i^2+9*y i^4)) := by
  unfold cubicNull cubicMixed quarticNull
  simp only [Finset.mul_sum]
  refine ⟨Finset.sum_congr rfl ?_,Finset.sum_congr rfl ?_,Finset.sum_congr rfl ?_⟩
  all_goals intro i _; rw [← scale i]; field_simp [hr i]
  · linear_combination 9*l i*K x y i*x i*(unit i)
  · linear_combination 3*l i*K x y i*y i*(unit i)
  · linear_combination l i*(K x y i)^2*(81*x i^2-9*y i^2-9)*(unit i)

/-- Homogeneous Coulomb jets, with no finite-slope condition. The nonzero
minor factors used to clear denominators are exactly the site separations. -/
theorem homogeneous_jets (l r x y : Triple) (κ : ℝ) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ)
    (sep : ∀ i j, i ≠ j → minor x y i j ≠ 0)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3) :
    κ*cubicNull l r x = 2*(B x y-2*D x) ∧ κ*cubicMixed l r x y = -4*A x y ∧
    κ^2*(quarticNull l r x-3*(cubicMixed l r x y)^2) =
      -2*(12*(A x y)^2-14*A x y*C y-4*(B x y)^2-12*B x y*D x+3*(C y)^2+48*(D x)^2) := by
  let m := 3*minor x y 0 1*minor x y 0 2*minor x y 1 2
  have nm : m ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (sep 0 1 (by decide))) (sep 0 2 (by decide))) (sep 1 2 (by decide))
  have w := weight_identity l x y xx xy yy
  have moments (t : Triple) :
      m*(∑ i, l i*t i) = K x y 0*minor x y 1 2*t 0-K x y 1*minor x y 0 2*t 1+
        K x y 2*minor x y 0 1*t 2 := by
    rw [← w 0,← w 1,← w 2]
    simp [Fin.sum_univ_three,m,minor]
    ring
  obtain ⟨hz,hm,hq⟩ := scaled_jets l r x y κ hr unit scale
  have n : κ*cubicNull l r x = 2*(B x y-2*D x) := by
    apply mul_left_cancel₀ nm
    rw [hz,moments]
    dsimp [m,minor,K,B,D]
    ring
  have v : κ*cubicMixed l r x y = -4*A x y := by
    apply mul_left_cancel₀ nm
    rw [hm,moments]
    dsimp [m,minor,K,A]
    ring
  refine ⟨n,v,?_⟩
  rw [show κ^2*(quarticNull l r x-3*(cubicMixed l r x y)^2) =
    κ^2*quarticNull l r x-3*(κ*cubicMixed l r x y)^2 by ring,v,hq]
  apply mul_left_cancel₀ nm
  rw [mul_sub,moments]
  dsimp [m,minor,K,A,B,C,D]
  ring

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

def gram (w p q : Triple) := ∑ i, w i*p i*q i

def gramDet (w p q : Triple) :=
  (3*gram w p p-1)*(3*gram w q q-1)-(3*gram w p q)^2

def rot (p q : Triple) (a b : ℝ) : Triple := fun i => a*p i+b*q i

private theorem gram_rot (w p q : Triple) (a b c d : ℝ) :
    gram w (rot p q a b) (rot p q c d) =
      a*c*gram w p p+(a*d+b*c)*gram w p q+b*d*gram w q q := by
  simp [gram,rot,Fin.sum_univ_three]
  ring

theorem gramDet_rotation (w p q : Triple) (a b : ℝ) (unit : a^2+b^2=1) :
    gramDet w (rot p q a b) (rot p q (-b) a) = gramDet w p q := by
  simp only [gramDet,gram_rot]
  linear_combination
    (9*((a^2+b^2)+1)*(gram w p p*gram w q q-(gram w p q)^2)-
      3*(gram w p p+gram w q q))*unit

private theorem null_vector (A B C : ℝ) (det : A*C-B^2=0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧ A*a+B*b=0 ∧ B*a+C*b=0 := by
  by_cases h : A=0
  · refine ⟨1,0,by norm_num,by simp [h],?_⟩
    simp [h] at det
    simp [det]
  let r := Real.sqrt (A^2+B^2)
  have pos : 0 < A^2+B^2 := by positivity
  have nr : r ≠ 0 := (Real.sqrt_pos.mpr pos).ne'
  have rs : r^2=A^2+B^2 := Real.sq_sqrt pos.le
  refine ⟨-B/r,A/r,?_,?_,?_⟩
  · field_simp [nr]
    linarith
  · field_simp [nr]
    ring
  · field_simp [nr]
    linarith

/-- Rotate a trace-one singular Hessian into diagonal form. The two
rotated displacement rows are otherwise unrestricted. -/
theorem exists_null_frame (w p q : Triple)
    (trace : 3*gram w p p+3*gram w q q=3) (det : gramDet w p q=0) :
    ∃ a b : ℝ, a^2+b^2=1 ∧
      gram w (rot p q a b) (rot p q a b)=1/3 ∧
      gram w (rot p q a b) (rot p q (-b) a)=0 ∧
      gram w (rot p q (-b) a) (rot p q (-b) a)=2/3 := by
  obtain ⟨a,b,unit,hx,hy⟩ := null_vector _ _ _ det
  refine ⟨a,b,unit,?_,?_,?_⟩
  all_goals rw [gram_rot]
  · linear_combination (a*hx+b*hy+unit)/3
  · linear_combination (-b*hx+a*hy)/3
  · linear_combination ((a^2+b^2)*trace-a*hx-b*hy+2*unit)/3

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

noncomputable def cartDet (l p q : Triple) :=
  gramDet (fun i => l i/(p i^2+q i^2)) p q

private theorem rot_sq (p q : Triple) (a b : ℝ) (h : a^2+b^2=1) (i : Fin 3) :
    rot p q a b i^2+rot p q (-b) a i^2=p i^2+q i^2 := by
  dsimp [rot]
  linear_combination (p i^2+q i^2)*h

theorem cartDet_rotation (l p q : Triple) (a b : ℝ) (h : a^2+b^2=1) :
    cartDet l (rot p q a b) (rot p q (-b) a)=cartDet l p q := by
  unfold cartDet
  simp only [rot_sq p q a b h]
  exact gramDet_rotation _ p q a b h

private theorem cart_lineDet (l d r x y : Triple) (u v t : ℝ) :
    cartDet (fun i => l i+t*d i) (fun i => r i*x i-t*u) (fun i => r i*y i-t*v) =
      lineDet l d r x y u v t := by
  have xx (w a b : ℝ) : w/(a^2+b^2)*a*a=w*a^2/(a^2+b^2) := by ring
  have yy (w a b : ℝ) : w/(a^2+b^2)*b*b=w*b^2/(b^2+a^2) := by rw [add_comm (b^2)]; ring
  have xy (w a b : ℝ) : w/(a^2+b^2)*a*b=w*a*b/(a^2+b^2) := by ring
  simp only [cartDet,gramDet,gram,lineDet,lineXX,lineXY,summand,xx,yy,xy]

private theorem unit_moment (l p q : Triple) (r x y : Triple) (a b c : ℝ)
    (eq : ∀ i, p i^2+q i^2=r i^2) (ex : ∀ i, r i*x i=rot p q a b i)
    (ey : ∀ i, r i*y i=rot p q (-b) a i) (nz : ∀ i, r i ≠ 0)
    (he : gram (fun i => l i/(p i^2+q i^2)) (rot p q a b) (rot p q (-b) a)=c) :
    ∑ i, l i*x i*y i=c := by
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← ex,← ey,eq]
  field_simp [nz i]

/-- Nonvanishing spatial derivative in arbitrary Cartesian coordinates.
p,q are the two site-minus-field-point displacement rows. The barycentric
velocity b is characterized by its three affine moment identities. -/
theorem cart_regular (l p q : Triple) (b : ℝ → ℝ → Triple)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ i, 0 < p i^2+q i^2)
    (sep : ∀ i j, i ≠ j → minor p q i j ≠ 0)
    (mass : ∑ i, l i=1) (fx : ∑ i, l i*p i=0) (fy : ∑ i, l i*q i=0)
    (bm : ∀ u v, ∑ i, b u v i=0)
    (bx : ∀ u v, ∑ i, b u v i*p i=u) (by' : ∀ u v, ∑ i, b u v i*q i=v)
    (critical : cartDet l p q=0) :
    ∃ U V : ℝ, deriv (fun t => cartDet (fun i => l i+t*b U V i)
      (fun i => p i-t*U) (fun i => q i-t*V)) 0 ≠ 0 := by
  let w (i : Fin 3) := l i/(p i^2+q i^2)
  have tr : gram w p p + gram w q q = 1 := by
    unfold gram
    rw [← Finset.sum_add_distrib,← mass]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    field_simp [(hr i).ne']
  obtain ⟨a,c,ac,hxx,hxy,hyy⟩ := exists_null_frame w p q (by linarith) critical
  let r (i : Fin 3) := Real.sqrt (p i^2+q i^2)
  let x (i : Fin 3) := rot p q a c i/r i
  let y (i : Fin 3) := rot p q (-c) a i/r i
  have nr (i : Fin 3) : r i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have sqr (i : Fin 3) : p i^2+q i^2=r i^2 := (Real.sq_sqrt (hr i).le).symm
  have rx (i : Fin 3) : r i*x i=rot p q a c i := by dsimp [x]; field_simp [nr i]
  have ry (i : Fin 3) : r i*y i=rot p q (-c) a i := by dsimp [y]; field_simp [nr i]
  have unit (i : Fin 3) : x i^2+y i^2=1 := by
    dsimp [x,y]
    field_simp [nr i]
    linarith only [rot_sq p q a c ac i,sqr i]
  have sep' (i j : Fin 3) (hne : i ≠ j) : minor x y i j ≠ 0 := by
    intro e
    apply sep i j hne
    dsimp [minor,x,y,rot] at e ⊢
    field_simp [nr i,nr j] at e
    linear_combination e-(p i*q j-q i*p j)*ac
  have square (z f : Triple) (hf : ∀ i, r i*z i=f i) :
      ∑ i, l i*z i^2=gram w f f := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [w]
    rw [← hf,sqr]
    field_simp [nr i]
  have xx := (square x _ rx).trans hxx
  have yy := (square y _ ry).trans hyy
  have xy := unit_moment l p q r x y a c _ sqr rx ry nr hxy
  have balance (g z : Triple) (e f U V : ℝ) (hz : ∀ i, r i*z i=rot p q e f i)
      (hp : ∑ i, g i*p i=U) (hq : ∑ i, g i*q i=V) :
      ∑ i, g i*r i*z i=e*U+f*V := by
    simp only [Fin.sum_univ_three,mul_assoc,hz,rot] at hp hq ⊢
    linear_combination e*hp+f*hq
  let vel (u v : ℝ) := b (a*u-c*v) (c*u+a*v)
  have Xv (u v : ℝ) : ∑ i, vel u v i*r i*x i=u := by
    rw [balance _ _ _ _ _ _ rx (bx ..) (by' ..)]
    linear_combination u*ac
  have Yv (u v : ℝ) : ∑ i, vel u v i*r i*y i=v := by
    rw [balance _ _ _ _ _ _ ry (bx ..) (by' ..)]
    linear_combination v*ac
  have forceX := balance l x a c 0 0 rx fx fy
  have forceY := balance l y (-c) a 0 0 ry fx fy
  have reg := regular_in_null_frame l r x y vel unit hl nr sep' xx xy yy
    (by simpa using forceX) (by simpa using forceY) (fun u v => bm _ _) Xv Yv
  have move (u v : ℝ) (h : deriv (lineDet l (vel u v) r x y u v) 0 ≠ 0) :
      ∃ U V : ℝ, deriv (fun t => cartDet (fun i => l i+t*b U V i)
        (fun i => p i-t*U) (fun i => q i-t*V)) 0 ≠ 0 := by
    refine ⟨a*u-c*v,c*u+a*v,?_⟩
    convert! h using 2
    funext t
    rw [← cartDet_rotation _ _ _ a c ac,← cart_lineDet]
    congr 1
    · funext i
      dsimp [rot]
      rw [rx]
      dsimp [rot]
      linear_combination -t*u*ac
    · funext i
      dsimp [rot]
      rw [ry]
      dsimp [rot]
      linear_combination -t*v*ac
  exact reg.elim (move 1 0) (move 0 1)

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

def siteDx (s x : ℝ) : Triple := ![-x,1-x,s-x]
def siteDy (h y : ℝ) : Triple := ![-y,-y,h-y]

noncomputable def bary (s h x y : ℝ) : Triple := ![1-x+(s-1)*y/h,x-s*y/h,y/h]

noncomputable def normalizedDet (s h : ℝ) (z : ℝ × ℝ) :=
  cartDet (bary s h z.1 z.2) (siteDx s z.1) (siteDy h z.2)

theorem normalized_gradient (s h x y : ℝ) (hh : h ≠ 0)
    (hl : ∀ i, bary s h x y i ≠ 0) (critical : normalizedDet s h (x,y)=0) :
    fderiv ℝ (normalizedDet s h) (x,y) ≠ 0 := by
  let l := bary s h x y
  let p := siteDx s x
  let q := siteDy h y
  let b (u v : ℝ) : Triple := ![-u+(s-1)*v/h,u-s*v/h,v/h]
  have sep (i j : Fin 3) (ne : i ≠ j) : minor p q i j ≠ 0 := by
    have h0 : minor p q 1 2 = h*l 0 := by
      simp [p,q,l,minor,siteDx,siteDy,bary]; field_simp; ring
    have h1 : minor p q 2 0 = h*l 1 := by
      simp [p,q,l,minor,siteDx,siteDy,bary]; field_simp; ring
    have h2 : minor p q 0 1 = h*l 2 := by
      simp [p,q,l,minor,siteDx,siteDy,bary]; field_simp; ring
    have rev (i j : Fin 3) : minor p q i j= -minor p q j i := by unfold minor; ring
    have n0 := mul_ne_zero hh (hl 0)
    have n1 := mul_ne_zero hh (hl 1)
    have n2 := mul_ne_zero hh (hl 2)
    fin_cases i <;> fin_cases j <;> first
      | contradiction
      | exact h0.trans_ne n0
      | exact h1.trans_ne n1
      | exact h2.trans_ne n2
      | exact (rev _ _).trans_ne (neg_ne_zero.mpr (h0.trans_ne n0))
      | exact (rev _ _).trans_ne (neg_ne_zero.mpr (h1.trans_ne n1))
      | exact (rev _ _).trans_ne (neg_ne_zero.mpr (h2.trans_ne n2))
  have hr (i : Fin 3) : 0 < p i^2+q i^2 := by
    by_contra! e
    have a : p i=0 := by nlinarith [sq_nonneg (q i)]
    have c : q i=0 := by nlinarith [sq_nonneg (p i)]
    exact sep i (i+1) (by fin_cases i <;> decide) (by simp [minor,a,c])
  obtain ⟨u,v,ne⟩ := cart_regular l p q b hl hr sep (by
    simp [l,bary,Fin.sum_univ_three]; field_simp; ring) (by
    simp [l,p,bary,siteDx,Fin.sum_univ_three]; field_simp; ring) (by
    simp [l,q,bary,siteDy,Fin.sum_univ_three]; field_simp; ring) (by
    intro u v; simp [b,Fin.sum_univ_three]; field_simp; ring) (by
    intro u v; simp [b,p,siteDx,Fin.sum_univ_three]; field_simp; ring) (by
    intro u v; simp [b,q,siteDy,Fin.sum_univ_three]; field_simp; ring) critical
  have path (t : ℝ) : normalizedDet s h (x+t*u,y+t*v) =
      cartDet (fun i => l i+t*b u v i) (fun i => p i-t*u) (fun i => q i-t*v) := by
    unfold normalizedDet
    congr 1
    · funext i
      fin_cases i <;> dsimp [l,b,bary] <;> ring
    · funext i
      fin_cases i <;> dsimp [p,siteDx] <;> ring
    · funext i
      fin_cases i <;> dsimp [q,siteDy] <;> ring
  have diff : DifferentiableAt ℝ (normalizedDet s h) (x,y) := by
    have radius (i : Fin 3) : siteDx s x i^2+siteDy h y i^2 ≠ 0 := (hr i).ne'
    have d1 (i : Fin 3) : DifferentiableAt ℝ (fun z : ℝ × ℝ => siteDx s z.1 i) (x,y) := by
      fin_cases i <;> dsimp [siteDx] <;> fun_prop
    have d2 (i : Fin 3) : DifferentiableAt ℝ (fun z : ℝ × ℝ => siteDy h z.2 i) (x,y) := by
      fin_cases i <;> dsimp [siteDy] <;> fun_prop
    have dl (i : Fin 3) : DifferentiableAt ℝ (fun z : ℝ × ℝ => bary s h z.1 z.2 i) (x,y) := by
      fin_cases i <;> dsimp [bary] <;> fun_prop
    unfold normalizedDet cartDet gramDet gram
    fun_prop (disch := exact radius _)
  have line (a w : ℝ) : HasDerivAt (fun t : ℝ => a+t*w) w 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const w).const_add a)
  have der := diff.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ)
    ((line x u).prodMk (line y v)) (by simp)
  intro zero
  apply ne
  have e := der.deriv
  change deriv (fun t => normalizedDet s h (x+t*u,y+t*v)) 0 = _ at e
  simpa only [path,zero,zero_apply] using e

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

/-- Same Cartesian presentation as Chart.detH. Retain the squared radii
as separate entries so that the chart determinant specializes by reflexivity. -/
noncomputable def chartHessian (s h x y : ℝ) :=
  let l := bary s h x y
  let r : Triple := ![x^2+y^2,(x-1)^2+y^2,(x-s)^2+(y-h)^2]
  let u : Triple := ![x,x-1,x-s]
  let v : Triple := ![y,y,y-h]
  (3*(∑ i, (l i/r i)*u i^2)-1)*(3*(∑ i, (l i/r i)*v i^2)-1)-
    (3*∑ i, (l i/r i)*u i*v i)^2

theorem chartHessian_eq (s h x y : ℝ) : chartHessian s h x y=normalizedDet s h (x,y) := by
  let u : Triple := ![x,x-1,x-s]
  let v : Triple := ![y,y,y-h]
  let r : Triple := ![x^2+y^2,(x-1)^2+y^2,(x-s)^2+(y-h)^2]
  have dx : siteDx s x = fun i => -u i := by funext i; fin_cases i <;> dsimp [siteDx,u] <;> ring
  have dy : siteDy h y = fun i => -v i := by
    funext i
    fin_cases i <;> dsimp [siteDy,v]
    ring
  have radius (i : Fin 3) : u i^2+v i^2=r i := by fin_cases i <;> rfl
  unfold normalizedDet cartDet gramDet gram
  rw [dx,dy]
  simp only [even_two.neg_pow,radius,mul_neg,neg_mul,neg_neg]
  simp only [chartHessian,pow_two,mul_assoc,u,v,r]

theorem chart_gradient (s h x y : ℝ) (hh : h ≠ 0) (hl : ∀ i, bary s h x y i ≠ 0)
    (critical : chartHessian s h x y=0) :
    fderiv ℝ (fun p : ℝ × ℝ => chartHessian s h p.1 p.2) (x,y) ≠ 0 := by
  simpa only [chartHessian_eq] using normalized_gradient s h x y hh hl
    ((chartHessian_eq s h x y).symm.trans critical)

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

/-- A quantitative version of the quartic obstruction at a cusp. -/
theorem cusp_quartic_negative (l r x y : Triple) (κ : ℝ) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ)
    (sep : ∀ i j, i ≠ j → minor x y i j ≠ 0)
    (xx : ∑ i, l i*x i^2 = 1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3)
    (cusp : cubicNull l r x=0) :
    quarticNull l r x-3*(cubicMixed l r x y)^2 < 0 := by
  obtain ⟨g,_,q⟩ := homogeneous_jets l r x y κ hr unit scale sep xx xy yy
  rw [cusp,mul_zero] at g
  have eb : B x y=2*D x := by linarith
  have pos (i : Fin 3) : 0 < 2*x i^2+y i^2 := by nlinarith only [unit i,sq_nonneg (x i)]
  have G := gradient_norm x y
  rw [eb] at G
  have strict : 0 < (C y-2*A x y)^2 := by
    nlinarith only [G,mul_pos (mul_pos (pos 0) (pos 1)) (pos 2)]
  have newton : 3*A x y*C y ≤ (B x y)^2 := by
    dsimp [A,B,C]
    nlinarith only [sq_nonneg (y 0*y 1*x 2-y 0*x 1*y 2),
      sq_nonneg (y 0*y 1*x 2-x 0*y 1*y 2),sq_nonneg (y 0*x 1*y 2-x 0*y 1*y 2)]
  rw [eb] at newton q
  have nq : κ^2*(quarticNull l r x-3*(cubicMixed l r x y)^2) < 0 := by
    nlinarith only [q,newton,strict,sq_nonneg (D x)]
  exact neg_of_mul_neg_right nq (sq_nonneg κ)

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

open scoped ContDiff

end MaxwellCusp.Spatial

end

section

noncomputable section
open Filter Topology
namespace MaxwellCausticExtremum.ForceSection

def fy (y r : ℝ) := y/r^3
def hv (s y r k : ℝ) := (3*s*y-k*r^2)/r^5
def hh (s r k : ℝ) := (3*s^2-(1+k^2)*r^2)/r^5
def yy (y r : ℝ) := (3*y^2-r^2)/r^5
def cv (s y r k : ℝ) := (15*s^2*y-3*r^2*((1+k^2)*y+2*k*s))/r^7
def cc (s r k : ℝ) := (15*s^3-9*r^2*(1+k^2)*s)/r^7
def qq (s r k : ℝ) := (105*s^4-90*r^2*(1+k^2)*s^2+9*r^4*(1+k^2)^2)/r^9

private theorem atom_derivatives {s y r k : ℝ → ℝ} {t m : ℝ} (hr : r t ≠ 0)
    (ds : HasDerivAt s (-(1+k t^2)+m*y t) t) (dy : HasDerivAt y (-k t) t)
    (dr : HasDerivAt r (-s t/r t) t) (dk : HasDerivAt k m t) :
    HasDerivAt (fun z => fy (y z) (r z)) (hv (s t) (y t) (r t) (k t)) t ∧
    HasDerivAt (fun z => hv (s z) (y z) (r z) (k z))
      (cv (s t) (y t) (r t) (k t)+m*yy (y t) (r t)) t ∧
    HasDerivAt (fun z => hh (s z) (r z) (k z))
      (cc (s t) (r t) (k t)+2*m*hv (s t) (y t) (r t) (k t)) t ∧
    HasDerivAt (fun z => cc (s z) (r z) (k z))
      (qq (s t) (r t) (k t)+3*m*cv (s t) (y t) (r t) (k t)) t := by
  have U := (dk.pow 2).const_add (1:ℝ)
  refine ⟨?_,?_,?_,?_⟩
  · convert! dy.div (dr.pow 3) (pow_ne_zero 3 hr) using 1
    dsimp [hv]; field_simp [hr]; ring
  · convert! ((((ds.const_mul 3).mul dy).sub (dk.mul (dr.pow 2))).div (dr.pow 5) (pow_ne_zero 5 hr)) using 1
    dsimp [cv,yy]; field_simp [hr]; ring
  · convert! ((((ds.pow 2).const_mul 3).sub (U.mul (dr.pow 2))).div (dr.pow 5) (pow_ne_zero 5 hr)) using 1
    dsimp [cc,hv]; field_simp [hr]; ring
  · convert! ((((ds.pow 3).const_mul 15).sub ((((dr.pow 2).const_mul 9).mul U).mul ds)).div (dr.pow 7) (pow_ne_zero 7 hr)) using 1
    dsimp [qq,cv]; field_simp [hr]; ring

/-- The force equations and their reduced derivatives for sites (aᵢ,bᵢ).
The first input of each field is the actual vector of charges. -/
structure Sites where
  a : Q
  b : Q

namespace Sites

def X (S : Sites) (p : P) (i : Fin 3) := S.a i-p.1.2
def Y (S : Sites) (p : P) (i : Fin 3) := S.b i-p.2
def R (S : Sites) (p : P) (i : Fin 3) := Real.sqrt ((S.X p i)^2+(S.Y p i)^2)
def sum (p : P) (f : Fin 3 → ℝ) := ∑ i, p.1.1 i*f i
def A (S : Sites) (p : P) := sum p fun i => fy (S.X p i) (S.R p i)
def B (S : Sites) (p : P) := sum p fun i => fy (S.Y p i) (S.R p i)
def M (S : Sites) (p : P) := sum p fun i => hv (S.X p i) (S.Y p i) (S.R p i) 0
def N (S : Sites) (p : P) := sum p fun i => yy (S.Y p i) (S.R p i)
def Pxx (S : Sites) (p : P) := sum p fun i => yy (S.X p i) (S.R p i)
def K (S : Sites) (p : P) := -S.M p/S.N p
def proj (S : Sites) (p : P) (i : Fin 3) := S.X p i+S.K p*S.Y p i
def cross (S : Sites) (p : P) := sum p fun i => hv (S.proj p i) (S.Y p i) (S.R p i) (S.K p)
def D (S : Sites) (p : P) := sum p fun i => hh (S.proj p i) (S.R p i) (S.K p)
def E (S : Sites) (p : P) := sum p fun i => cc (S.proj p i) (S.R p i) (S.K p)
def V (S : Sites) (p : P) := sum p fun i => cv (S.proj p i) (S.Y p i) (S.R p i) (S.K p)
def J (S : Sites) (p : P) := (sum p fun i => qq (S.proj p i) (S.R p i) (S.K p))-3*(S.V p)^2/S.N p

theorem cross_zero (S : Sites) (p : P) (hn : S.N p ≠ 0) : S.cross p=0 := by
  have eq : S.cross p=S.M p+S.K p*S.N p := by
    unfold cross M N sum proj hv yy
    simp only [Fin.sum_univ_three]; ring
  rw [eq,K,div_mul_cancel₀ _ hn,add_neg_cancel]

theorem determinant (S : Sites) (p : P) (hn : S.N p ≠ 0) :
    S.D p*S.N p=S.Pxx p*S.N p-(S.M p)^2 := by
  have eq : S.D p=S.Pxx p+2*S.K p*S.M p+(S.K p)^2*S.N p := by
    unfold D Pxx M N sum proj hv yy hh
    simp only [Fin.sum_univ_three]; ring
  rw [eq,K]
  field_simp [hn]; ring

theorem base_smooth (S : Sites) (p : P) (hr : ∀ i, 0 < S.R p i) :
    ContDiffAt ℝ 1 S.A p ∧ ContDiffAt ℝ 1 S.B p ∧ ContDiffAt ℝ 1 S.M p ∧
    ContDiffAt ℝ 1 S.N p := by
  have sm i : ContDiffAt ℝ 1 (fun z => S.R z i) p := by
    apply ContDiffAt.sqrt
    · unfold X Y; fun_prop
    · exact (Real.sqrt_pos.mp (hr i)).ne'
  unfold A B M N fy hv yy sum X Y
  refine ⟨?_,?_,?_,?_⟩ <;> fun_prop (disch := exact pow_ne_zero _ (hr _).ne')

private theorem all_smooth (S : Sites) (p : P) (hr : ∀ i, 0 < S.R p i) (hn : S.N p ≠ 0) :
    ContDiffAt ℝ 1 S.K p ∧ ContDiffAt ℝ 1 S.D p ∧ ContDiffAt ℝ 1 S.E p ∧ ContinuousAt S.J p := by
  obtain ⟨_,_,dm,dn⟩ := S.base_smooth p hr
  have k : ContDiffAt ℝ 1 S.K p := dm.neg.div dn hn
  have r i : ContDiffAt ℝ 1 (fun z => S.R z i) p := by
    apply ContDiffAt.sqrt
    · unfold X Y; fun_prop
    · exact (Real.sqrt_pos.mp (hr i)).ne'
  have u i : ContDiffAt ℝ 1 (fun z => S.proj z i) p := by
    unfold proj X Y; fun_prop
  have jj : ContDiffAt ℝ 1 S.J p := by
    unfold J V qq cv sum Y
    fun_prop (disch := first | exact hn | exact pow_ne_zero _ (hr _).ne')
  refine ⟨k,?_,?_,jj.continuousAt⟩
  · unfold D hh sum; fun_prop (disch := exact pow_ne_zero _ (hr _).ne')
  · unfold E cc sum; fun_prop (disch := exact pow_ne_zero _ (hr _).ne')

private def path (p : P) (k t : ℝ) : P := ((p.1.1,p.1.2+t),p.2+t*k)
private theorem path0 (p : P) (k : ℝ) : path p k 0=p := by simp [path]

private theorem spatialDeriv (S : Sites) (p : P) (hr : ∀ i, 0 < S.R p i) (hn : S.N p ≠ 0) :
    fderiv ℝ S.B p (tangent (S.K p))=0 ∧ fderiv ℝ S.A p (tangent (S.K p))=S.D p ∧
    fderiv ℝ S.D p (tangent (S.K p))=S.E p ∧ fderiv ℝ S.E p (tangent (S.K p))=S.J p := by
  let k := S.K p
  let w := path p k
  have w0 : w 0=p := path0 .. 
  have dy0 : HasDerivAt (fun t : ℝ => p.2+t*k) k 0 := by simpa using ((hasDerivAt_id (0:ℝ)).mul_const k).const_add p.2
  have dw : HasDerivAt w (tangent k) 0 := ((hasDerivAt_const 0 p.1.1).prodMk ((hasDerivAt_id (0:ℝ)).const_add p.1.2)).prodMk dy0
  have smooth := S.all_smooth p hr hn
  let m := fderiv ℝ S.K p (tangent k)
  have dk : HasDerivAt (S.K ∘ w) m 0 := (smooth.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 dw w0.symm
  have X' i : HasDerivAt (fun t => S.X (w t) i) (-1) 0 :=
    ((hasDerivAt_id (0:ℝ)).const_add p.1.2).const_sub _
  have Y' i : HasDerivAt (fun t => S.Y (w t) i) (-k) 0 :=
    dy0.const_sub _
  have R' i : HasDerivAt (fun t => S.R (w t) i) (-(S.proj p i)/S.R p i) 0 := by
    have eq := ((X' i).pow 2).add ((Y' i).pow 2)
    convert! eq.sqrt (by simpa [w0] using (Real.sqrt_pos.mp (hr i)).ne') using 1
    simp [w0,proj,R,k]; ring
  have U' i : HasDerivAt (fun t => S.proj (w t) i) (-(1+k^2)+m*S.Y p i) 0 := by
    convert! (X' i).add (dk.mul (Y' i)) using 1
    simp [w0,k]; ring
  have one i := atom_derivatives (t := 0) (s := fun t => S.proj (w t) i) (y := fun t => S.Y (w t) i)
    (r := fun t => S.R (w t) i) (k := S.K ∘ w) (m := m)
  simp only [Function.comp_apply,w0] at one
  have jet i := one i (hr i).ne' (U' i) (Y' i) (R' i) dk
  have sigma (f : Fin 3 → ℝ → ℝ) (d : Fin 3 → ℝ) (df : ∀ i, HasDerivAt (f i) (d i) 0) :
      HasDerivAt (fun t => sum (w t) (fun i => f i t)) (sum p d) 0 :=
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (df i).const_mul (p.1.1 i))
  have hB := sigma _ _ (fun i => (jet i).1)
  have hC := sigma _ _ (fun i => (jet i).2.1)
  have hD := sigma _ _ (fun i => (jet i).2.2.1)
  have hE := sigma _ _ (fun i => (jet i).2.2.2)
  have xforce i : HasDerivAt (fun t => fy (S.X (w t) i) (S.R (w t) i))
      (hh (S.proj p i) (S.R p i) k-k*hv (S.proj p i) (S.Y p i) (S.R p i) k) 0 := by
    convert! (X' i).div ((R' i).pow 3) (by simpa [w0] using pow_ne_zero 3 (hr i).ne') using 1
    simp only [w0,Pi.pow_apply]
    dsimp only [hh,hv,proj,k]
    field_simp [(hr i).ne']; ring
  have hA := sigma _ _ xforce
  have posN : ∀ᶠ t in 𝓝 (0:ℝ), S.N (w t) ≠ 0 := by
    have c := (S.base_smooth p hr).2.2.2.continuousAt
    exact dw.continuousAt (w0 ▸ c.eventually_ne hn)
  have flat : HasDerivAt (S.cross ∘ w) 0 0 :=
    (hasDerivAt_const 0 (0:ℝ)).congr_of_eventuallyEq (posN.mono fun t ht => S.cross_zero _ ht)
  have hz := hC.unique flat
  have rest : S.V p+m*S.N p=0 := by
    convert hz using 1
    dsimp [V,N,sum]; simp only [Fin.sum_univ_three]; ring
  have eq (f : P → ℝ) (v : ℝ) (df : DifferentiableAt ℝ f p) (d : HasDerivAt (f ∘ w) v 0) :
      fderiv ℝ f p (tangent k)=v := (df.hasFDerivAt.comp_hasDerivAt_of_eq 0 dw w0.symm).unique d
  have zero := S.cross_zero p hn
  have base := S.base_smooth p hr
  refine ⟨(eq _ _ (base.2.1.differentiableAt (by simp)) hB).trans zero,
    eq _ _ (base.1.differentiableAt (by simp)) (hA.congr_deriv ?_),
    eq _ _ (smooth.2.1.differentiableAt (by simp)) (hD.congr_deriv ?_),
    eq _ _ (smooth.2.2.1.differentiableAt (by simp)) (hE.congr_deriv ?_)⟩
  · dsimp only [sum,D,cross] at zero ⊢; simp only [Fin.sum_univ_three] at zero ⊢
    linear_combination -k*zero
  · dsimp only [sum,E,cross] at zero ⊢; simp only [Fin.sum_univ_three] at zero ⊢
    linear_combination 2*m*zero
  · have Q : sum p (fun i => qq (S.proj p i) (S.R p i) k+3*m*cv (S.proj p i) (S.Y p i) (S.R p i) k) =
        sum p (fun i => qq (S.proj p i) (S.R p i) k)+3*m*S.V p := by
      dsimp [sum,V,k]; simp only [Fin.sum_univ_three]; ring
    rw [Q,J]
    dsimp only [k]
    field_simp [hn]
    linear_combination 3*S.V p*rest

end Sites
end MaxwellCausticExtremum.ForceSection

namespace MaxwellCausticExtremum.ForceSection.Sites

theorem B_vertical (S : Sites) (p : P) (hr : ∀ i, 0 < S.R p i) :
    fderiv ℝ S.B p transverse=S.N p := by
  let w (t : ℝ) : P := (p.1,p.2+t)
  have w0 : w 0=p := by simp [w]
  have dw : HasDerivAt w transverse 0 := (hasDerivAt_const 0 p.1).prodMk ((hasDerivAt_id (0:ℝ)).const_add p.2)
  have Y' i : HasDerivAt (fun t => S.Y (w t) i) (-1) 0 := ((hasDerivAt_id (0:ℝ)).const_add p.2).const_sub _
  have X' i : HasDerivAt (fun t => S.X (w t) i) 0 0 := hasDerivAt_const (0:ℝ) (S.a i-p.1.2)
  have r' i : HasDerivAt (fun t => S.R (w t) i) (-(S.Y p i)/S.R p i) 0 := by
    have v := ((X' i).pow 2).add ((Y' i).pow 2)
    convert! v.sqrt (by simpa [w0] using (Real.sqrt_pos.mp (hr i)).ne') using 1
    simp [R,w0]; ring
  have y' i : HasDerivAt (fun t => fy (S.Y (w t) i) (S.R (w t) i)) (yy (S.Y p i) (S.R p i)) 0 := by
    convert! (Y' i).div ((r' i).pow 3) (by simpa [w0] using pow_ne_zero 3 (hr i).ne') using 1
    dsimp [yy]; simp only [w0]; field_simp [(hr i).ne']; ring
  exact (((S.base_smooth p hr).2.1.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 dw w0.symm).unique (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (y' i).const_mul (p.1.1 i)))

theorem unique_near (S : Sites) (b : P) (hr : ∀ i, 0 < S.R b i)
    (zero : S.B b=0) (one : S.N b=1) (jet : S.E b ≠ 0 ∨ S.J b<0) :
    ∃ U ∈ 𝓝 b, ∀ p ∈ U, ∀ q ∈ U, p.1.1=q.1.1 → S.B p=0 → S.B q=0 →
      0≤S.D p → 0≤S.D q → S.A p=S.A q → p=q := by
  have nb := one.trans_ne one_ne_zero
  have sm := S.all_smooth b hr nb
  apply local_unique S.B S.A S.D S.E S.J S.K b zero (S.base_smooth b hr).2.1
    ((S.B_vertical b hr).trans one)
  · have rad (i : Fin 3) : ∀ᶠ p in 𝓝 b, 0<S.R p i := by
      have cont : ContinuousAt (fun p => S.R p i) b := by unfold R X Y; fun_prop
      exact continuousAt_const.eventually_lt cont (hr i)
    filter_upwards [Filter.eventually_all.mpr rad,(S.base_smooth b hr).2.2.2.continuousAt.eventually_ne nb]
      with p hp hn
    have base := S.base_smooth p hp
    have all := S.all_smooth p hp hn
    exact ⟨base.2.1.differentiableAt (by simp),base.1.differentiableAt (by simp),
      all.2.1.differentiableAt (by simp),all.2.2.1.differentiableAt (by simp),
      (S.B_vertical p hp).trans_ne hn,S.spatialDeriv p hp hn⟩
  · rcases jet with h|h
    · rcases lt_or_gt_of_ne h with neg|pos
      · exact Or.inr (Or.inl (sm.2.2.1.continuousAt.eventually_lt continuousAt_const neg))
      · exact Or.inl (continuousAt_const.eventually_lt sm.2.2.1.continuousAt pos)
    · exact Or.inr (Or.inr (sm.2.2.2.eventually_lt continuousAt_const h))

/-- At the normalized singular equilibrium the reduced force slope is zero,
and its next two derivatives are the Coulomb cubic and reduced quartic. -/
theorem base_jets (S : Sites) (l r x y : Q) (hr : ∀ i, 0<r i) (unit : ∀ i, x i^2+y i^2=1)
    (ax : ∀ i, S.a i=r i*x i) (ay : ∀ i, S.b i=r i*y i)
    (mass : ∑ i,l i=1) (_xx : ∑ i,l i*x i^2=1/3) (xy : ∑ i,l i*x i*y i=0)
    (yy' : ∑ i,l i*y i^2=2/3) :
    let b : P := ((fun i => l i*r i^3,0),0)
    (∀ i, S.R b i=r i) ∧ S.N b=1 ∧ S.E b=MaxwellCusp.Spatial.cubicNull l r x ∧
      S.J b=MaxwellCusp.Spatial.quarticNull l r x-3*(MaxwellCusp.Spatial.cubicMixed l r x y)^2 := by
  let b : P := ((fun i => l i*r i^3,0),0)
  have Xb i : S.X b i=r i*x i := by simp [X,b,ax]
  have Yb i : S.Y b i=r i*y i := by simp [Y,b,ay]
  have Rb i : S.R b i=r i := by
    unfold R
    rw [Xb,Yb,show (r i*x i)^2+(r i*y i)^2=r i^2 by linear_combination (r i)^2*unit i,
      Real.sqrt_sq (hr i).le]
  have normalize (f g : Fin 3 → ℝ) (h : ∀ i, r i^3*f i=g i) :
      sum b f=∑ i,l i*g i := by
    apply Finset.sum_congr rfl; intro i _; dsimp [b]; rw [mul_assoc,h]
  have Nm : S.N b=1 := by
    unfold N
    rw [normalize _ (fun i => 3*y i^2-1) (by
      intro i; rw [Yb,Rb]; dsimp [yy]; field_simp [(hr i).ne'])]
    simp only [Fin.sum_univ_three] at mass yy' ⊢
    linear_combination 3*yy'-mass
  have Mz : S.M b=0 := by
    unfold M
    rw [normalize _ (fun i => 3*x i*y i) (by
      intro i; rw [Xb,Yb,Rb]; dsimp [hv]; field_simp [(hr i).ne']; ring)]
    simp only [Fin.sum_univ_three] at xy ⊢
    linear_combination 3*xy
  have kz : S.K b=0 := by simp [K,Mz]
  have pr i : S.proj b i=r i*x i := by simp [proj,kz,Xb]
  have cub : S.E b=MaxwellCusp.Spatial.cubicNull l r x := by
    unfold E MaxwellCusp.Spatial.cubicNull
    apply Finset.sum_congr rfl; intro i _
    dsimp only; rw [pr,Rb,kz]; dsimp [cc,b]; field_simp [(hr i).ne']; ring
  have vm : S.V b=MaxwellCusp.Spatial.cubicMixed l r x y := by
    unfold V MaxwellCusp.Spatial.cubicMixed
    apply Finset.sum_congr rfl; intro i _
    dsimp only; rw [pr,Rb,Yb,kz]; dsimp [cv,b]; field_simp [(hr i).ne']; ring
  refine ⟨Rb,Nm,cub,?_⟩
  change S.J b=_
  unfold J
  rw [Nm,div_one,vm]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  dsimp only; rw [pr,Rb,kz]; dsimp [qq,b]; field_simp [(hr i).ne']; ring

end MaxwellCausticExtremum.ForceSection.Sites

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Chart

/-- Squared distances to the vertices (0,0), (1,0), (s,h). -/
def radii (s h x y : ℝ) : Fin 3 → ℝ :=
  ![x^2+y^2, (x-1)^2+y^2, (x-s)^2+(y-h)^2]

/-- Barycentric coordinates in this chart. -/
def coordinates (s h x y : ℝ) : Fin 3 → ℝ :=
  ![1-x+(s-1)*y/h, x-s*y/h, y/h]

def detH (s h x y : ℝ) : ℝ :=
  let r := radii s h x y
  let l := coordinates s h x y
  let u : Fin 3 → ℝ := ![x,x-1,x-s]
  let v : Fin 3 → ℝ := ![y,y,y-h]
  (3*(∑ i, (l i/r i)*u i^2)-1) * (3*(∑ i, (l i/r i)*v i^2)-1) -
    (3*∑ i, (l i/r i)*u i*v i)^2

private theorem gram_det (w u v : Fin 3 → ℝ) :
    (∑ i, w i*u i^2)*(∑ i, w i*v i^2) - (∑ i, w i*u i*v i)^2 =
      w 0*w 1*(u 0*v 1-u 1*v 0)^2 +
      w 0*w 2*(u 0*v 2-u 2*v 0)^2 +
      w 1*w 2*(u 1*v 2-u 2*v 1)^2 := by
  simp only [Fin.sum_univ_three]
  ring

theorem detH_eq (s h x y : ℝ) (hh : h ≠ 0) (hr : ∀ i, radii s h x y i ≠ 0) :
    let l := coordinates s h x y
    let r := radii s h x y
    detH s h x y = 9*h^2*l 0*l 1*l 2*(∑ i, l i*r i)/(r 0*r 1*r 2)-2 := by
  let l := coordinates s h x y
  let r := radii s h x y
  let u : Fin 3 → ℝ := ![x,x-1,x-s]
  let v : Fin 3 → ℝ := ![y,y,y-h]
  let w (i : Fin 3) := l i / r i
  have hr' (i : Fin 3) : r i ≠ 0 := hr i
  have rl (i : Fin 3) : u i^2+v i^2 = r i := by fin_cases i <;> rfl
  have tr : (∑ i, w i*u i^2)+(∑ i, w i*v i^2) = 1 := by
    simp only [← Finset.sum_add_distrib, ← mul_add, rl, w, div_mul_cancel₀ _ (hr' _)]
    simp [Fin.sum_univ_three,l,coordinates]
    field_simp
    ring
  have c01 : u 0*v 1-u 1*v 0 = h*l 2 := by
    dsimp [u,v,l,coordinates]
    field_simp
    ring
  have c02 : u 0*v 2-u 2*v 0 = -h*l 1 := by
    dsimp [u,v,l,coordinates]
    field_simp
    ring
  have c12 : u 1*v 2-u 2*v 1 = h*l 0 := by
    dsimp [u,v,l,coordinates]
    field_simp
    ring
  have g := gram_det w u v
  rw [c01,c02,c12] at g
  change (3*(∑ i, w i*u i^2)-1)*(3*(∑ i, w i*v i^2)-1) -
    (3*∑ i, w i*u i*v i)^2 = _
  calc
    _ = 9*(w 0*w 1*(h*l 2)^2+w 0*w 2*(-h*l 1)^2+w 1*w 2*(h*l 0)^2)-2 := by
      linarith only [g,tr]
    _ = 9*h^2*l 0*l 1*l 2*(∑ i, l i*r i)/(r 0*r 1*r 2)-2 := by
      simp only [Fin.sum_univ_three,w]
      field_simp [hr']
      ring

def dx (s x : ℝ) (i : Fin 3) : ℝ := x - (![0,1,s] : Fin 3 → ℝ) i

def dy (h y : ℝ) (i : Fin 3) : ℝ := y - (![0,0,h] : Fin 3 → ℝ) i

theorem radii_eq (s h x y : ℝ) (i : Fin 3) :
    radii s h x y i = dx s x i ^ 2 + dy h y i ^ 2 := by
  fin_cases i <;> simp [radii,dx,dy]

def coordVelocity (s h u v : ℝ) : Fin 3 → ℝ :=
  ![-u+(s-1)*v/h, u-s*v/h, v/h]

theorem coordinates_line (s h x y u v t : ℝ) (i : Fin 3) :
    coordinates s h (x+t*u) (y+t*v) i =
      coordinates s h x y i + t*coordVelocity s h u v i := by
  fin_cases i <;> simp [coordinates,coordVelocity,div_eq_mul_inv] <;> ring

/-- The logarithm of the absolute prescribed charge at a chart point. -/
def logCharge (s h x y : ℝ) (i : Fin 3) : ℝ :=
  Real.log (coordinates s h x y i) + (3/2)*Real.log (radii s h x y i)

theorem logCharge_eq (s h x y : ℝ) (i : Fin 3) (hl : coordinates s h x y i ≠ 0)
    (hr : 0 < radii s h x y i) : logCharge s h x y i =
      Real.log |coordinates s h x y i * Real.sqrt (radii s h x y i)^3| := by
  rw [Real.log_abs,Real.log_mul hl (pow_ne_zero 3 (Real.sqrt_pos.mpr hr).ne'),
    Real.log_pow,Real.log_sqrt hr.le]
  unfold logCharge
  ring

def logVelocity (s h x y u v : ℝ) (i : Fin 3) : ℝ :=
  coordVelocity s h u v i / coordinates s h x y i +
    3*(dx s x i*u + dy h y i*v)/radii s h x y i

theorem logCharge_line_deriv (s h x y u v : ℝ) (i : Fin 3)
    (hl : coordinates s h x y i ≠ 0) (hr : radii s h x y i ≠ 0) :
    HasDerivAt (fun t => logCharge s h (x+t*u) (y+t*v) i) (logVelocity s h x y u v i) 0 := by
  have line (b m : ℝ) : HasDerivAt (fun t : ℝ => b+t*m) m 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const m).const_add b)
  have lc := (line (coordinates s h x y i) (coordVelocity s h u v i)).log
    (by simpa using hl)
  have rr := ((line (dx s x i) u).pow 2).add ((line (dy h y i) v).pow 2)
  have lr := rr.log (by simpa [radii_eq] using hr)
  have e (t : ℝ) : radii s h (x+t*u) (y+t*v) i =
      (dx s x i+t*u)^2+(dy h y i+t*v)^2 := by
    rw [radii_eq]
    unfold dx dy
    ring
  convert! lc.add (lr.const_mul (3/2:ℝ)) using 1
  · funext t
    simp only [logCharge,coordinates_line,e]
    rfl
  · simp [logVelocity,radii_eq]
    ring

/-- Derivative of the two logarithmic charge ratios (index zero is the reference). -/
theorem logRatio_line_deriv (s h x y u v : ℝ) (i : Fin 3)
    (hl : ∀ j, coordinates s h x y j ≠ 0) (hr : ∀ j, radii s h x y j ≠ 0) :
    HasDerivAt (fun t => logCharge s h (x+t*u) (y+t*v) i -
      logCharge s h (x+t*u) (y+t*v) 0)
      (logVelocity s h x y u v i - logVelocity s h x y u v 0) 0 :=
  (logCharge_line_deriv s h x y u v i (hl i) (hr i)).sub
    (logCharge_line_deriv s h x y u v 0 (hl 0) (hr 0))

private theorem weighted_velocity (l d k b r z : Fin 3 → ℝ) (e : ℝ)
    (hl : ∀ i, l i ≠ 0) (hk : ∀ i, k i = b i/l i + 3*z i/r i)
    (hm : ∑ i, l i*d i = 0) (hb : ∑ i, b i*d i = -e) :
    l 1*d 1*(k 1-k 0)+l 2*d 2*(k 2-k 0) =
      3*(∑ i, l i/r i*d i*z i)-e := by
  have h (i : Fin 3) : l i*d i*k i = b i*d i+3*(l i/r i*d i*z i) := by
    rw [hk]
    field_simp [hl i]
  simp only [Fin.sum_univ_three] at *
  linear_combination h 0 + h 1 + h 2 - k 0*hm + hb

/-- The matrix with columns λ₁d₁ and λ₂d₂ takes the logarithmic charge
differential to the normalized Coulomb Hessian, in both spatial coordinates. -/
theorem charge_differential (s h x y u v : ℝ) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h x y i ≠ 0) :
    let l := coordinates s h x y
    let k := logVelocity s h x y u v
    let a := dx s x
    let b := dy h y
    let z (i : Fin 3) := a i*u + b i*v
    let r := radii s h x y
    (l 1*a 1*(k 1-k 0)+l 2*a 2*(k 2-k 0) = 3*(∑ i, l i/r i*a i*z i)-u) ∧
    (l 1*b 1*(k 1-k 0)+l 2*b 2*(k 2-k 0) = 3*(∑ i, l i/r i*b i*z i)-v) := by
  dsimp only
  let z (i : Fin 3) := dx s x i*u + dy h y i*v
  have hv := weighted_velocity (coordinates s h x y) (k := logVelocity s h x y u v)
    (b := coordVelocity s h u v) (r := radii s h x y) (z := z)
  constructor
  · apply hv (dx s x) u hl (fun _ => rfl)
    all_goals
      simp [Fin.sum_univ_three,dx,coordinates,coordVelocity]
      field_simp
      ring
  · apply hv (dy h y) v hl (fun _ => rfl)
    all_goals
      simp [Fin.sum_univ_three,dy,coordinates,coordVelocity]
      field_simp
      ring

theorem charge_matrix_det (s h x y : ℝ) (hh : h ≠ 0) :
    let l := coordinates s h x y
    (l 1*dx s x 1)*(l 2*dy h y 2) - (l 2*dx s x 2)*(l 1*dy h y 1) =
      h*l 0*l 1*l 2 := by
  simp [coordinates,dx,dy]
  field_simp
  ring

def chargeMap (s h : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (logCharge s h p.1 p.2 1 - logCharge s h p.1 p.2 0,
   logCharge s h p.1 p.2 2 - logCharge s h p.1 p.2 0)

theorem chargeMap_fderiv (s h x y u v : ℝ)
    (hl : ∀ i, coordinates s h x y i ≠ 0) (hr : ∀ i, radii s h x y i ≠ 0) :
    fderiv ℝ (chargeMap s h) (x,y) (u,v) =
      (logVelocity s h x y u v 1 - logVelocity s h x y u v 0,
       logVelocity s h x y u v 2 - logVelocity s h x y u v 0) := by
  have dl (i : Fin 3) : DifferentiableAt ℝ (fun p : ℝ × ℝ => coordinates s h p.1 p.2 i) (x,y) := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop
  have dr (i : Fin 3) : DifferentiableAt ℝ (fun p : ℝ × ℝ => radii s h p.1 p.2 i) (x,y) := by
    fin_cases i <;> dsimp [radii] <;> fun_prop
  have dc (i : Fin 3) : DifferentiableAt ℝ (fun p : ℝ × ℝ => logCharge s h p.1 p.2 i) (x,y) :=
    ((dl i).log (hl i)).add (((dr i).log (hr i)).const_mul _)
  have df := ((dc 1).sub (dc 0)).prodMk ((dc 2).sub (dc 0))
  have line (b m : ℝ) : HasDerivAt (fun t : ℝ => b+t*m) m 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).mul_const m).const_add b)
  have hf : DifferentiableAt ℝ (chargeMap s h) (x,y) := df
  have he := hf.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ)
    ((line x u).prodMk (line y v)) (by simp)
  exact he.unique ((logRatio_line_deriv s h x y u v 1 hl hr).prodMk
    (logRatio_line_deriv s h x y u v 2 hl hr))

/-- Signed Jacobian in the two Cartesian directions of the chart. -/
def jacobian (s h x y : ℝ) : ℝ :=
  let D := fderiv ℝ (chargeMap s h) (x,y)
  (D (1,0)).1*(D (0,1)).2 - (D (0,1)).1*(D (1,0)).2

theorem jacobian_eq (s h x y : ℝ) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h x y i ≠ 0) (hr : ∀ i, radii s h x y i ≠ 0) :
    let l := coordinates s h x y
    h*l 0*l 1*l 2*jacobian s h x y = detH s h x y := by
  let l := coordinates s h x y
  let r := radii s h x y
  let a := dx s x
  let b := dy h y
  let D := fderiv ℝ (chargeMap s h) (x,y)
  let A := 3*(∑ i, l i/r i*a i^2)-1
  let B := 3*∑ i, l i/r i*a i*b i
  let C := 3*(∑ i, l i/r i*b i^2)-1
  have action (u v : ℝ) := charge_differential s h x y u v hh hl
  have h1 : l 1*a 1*(D (1,0)).1+l 2*a 2*(D (1,0)).2 = A := by
    simpa [D,chargeMap_fderiv s h x y 1 0 hl hr,A,a,l,r,pow_two,mul_assoc] using (action 1 0).1
  have h2 : l 1*b 1*(D (1,0)).1+l 2*b 2*(D (1,0)).2 = B := by
    simpa [D,chargeMap_fderiv s h x y 1 0 hl hr,B,a,b,l,r,mul_comm,mul_left_comm,mul_assoc] using (action 1 0).2
  have h3 : l 1*a 1*(D (0,1)).1+l 2*a 2*(D (0,1)).2 = B := by
    simpa [D,chargeMap_fderiv s h x y 0 1 hl hr,B,a,b,l,r,mul_assoc] using (action 0 1).1
  have h4 : l 1*b 1*(D (0,1)).1+l 2*b 2*(D (0,1)).2 = C := by
    simpa [D,chargeMap_fderiv s h x y 0 1 hl hr,C,b,l,r,pow_two,mul_assoc] using (action 0 1).2
  have da : a = ![x,x-1,x-s] := by funext i; fin_cases i <;> simp [a,dx]
  have db : b = ![y,y,y-h] := by funext i; fin_cases i <;> simp [b,dy]
  have det : detH s h x y = A*C-B^2 := by simp only [A,B,C,da,db]; rfl
  dsimp only
  rw [det, ← charge_matrix_det s h x y hh]
  change (l 1*a 1*(l 2*b 2)-l 2*a 2*(l 1*b 1)) *
    ((D (1,0)).1*(D (0,1)).2-(D (0,1)).1*(D (1,0)).2) = A*C-B^2
  calc
    _ = (l 1*a 1*(D (1,0)).1+l 2*a 2*(D (1,0)).2)*(l 1*b 1*(D (0,1)).1+l 2*b 2*(D (0,1)).2) -
        (l 1*a 1*(D (0,1)).1+l 2*a 2*(D (0,1)).2)*(l 1*b 1*(D (1,0)).1+l 2*b 2*(D (1,0)).2) := by ring
    _ = _ := by rw [h1,h4,h3,h2,pow_two]

theorem critical_iff (s h x y : ℝ) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h x y i ≠ 0) (hr : ∀ i, radii s h x y i ≠ 0) :
    jacobian s h x y = 0 ↔ detH s h x y = 0 := by
  rw [← jacobian_eq s h x y hh hl hr]
  simp [hh,hl]

end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum.Chart

theorem chargeMap_smooth (s h : ℝ) (p : ℝ × ℝ) (hl : ∀ i, coordinates s h p.1 p.2 i ≠ 0)
    (hr : ∀ i, radii s h p.1 p.2 i ≠ 0) : ContDiffAt ℝ ⊤ (chargeMap s h) p := by
  have dl (i : Fin 3) : ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => coordinates s h z.1 z.2 i) p := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop
  have dr (i : Fin 3) : ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => radii s h z.1 z.2 i) p := by
    fin_cases i <;> dsimp [radii] <;> fun_prop
  have dq (i : Fin 3) : ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => logCharge s h z.1 z.2 i) p :=
    ((dl i).log (hl i)).add (contDiffAt_const.mul ((dr i).log (hr i)))
  exact ((dq 1).sub (dq 0)).prodMk ((dq 2).sub (dq 0))

/-- The charge map satisfies the local homeomorphism hypothesis throughout
the open sheet, and also on regular points of the opposite sign. -/
theorem chargeMap_regular (s h : ℝ) (hh : h ≠ 0) :
    IsLocalHomeomorphOn (chargeMap s h) {p | (∀ i, coordinates s h p.1 p.2 i ≠ 0) ∧
      (∀ i, radii s h p.1 p.2 i ≠ 0) ∧ detH s h p.1 p.2 ≠ 0} := by
  rintro ⟨x,y⟩ ⟨hl,hr,hn⟩
  let L := fderiv ℝ (chargeMap s h) (x,y)
  let a := L (1,0)
  let b := L (0,1)
  have det : a.1*b.2-b.1*a.2 ≠ 0 := fun z => hn ((critical_iff s h x y hh hl hr).mp z)
  have inj : Function.Injective L := by
    apply (injective_iff_map_eq_zero L).mpr
    rintro ⟨u,v⟩ eq
    have e : u • a + v • b = 0 := by
      rw [← L.map_smul u (1,0),← L.map_smul v (0,1),← map_add]
      simpa using eq
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    change u*a.1+v*b.1=0 at e1
    change u*a.2+v*b.2=0 at e2
    have h1 : (a.1*b.2-b.1*a.2)*u=0 := by linear_combination b.2*e1-b.1*e2
    have h2 : (a.1*b.2-b.1*a.2)*v=0 := by linear_combination a.1*e2-a.2*e1
    exact Prod.ext ((mul_eq_zero.mp h1).resolve_left det) ((mul_eq_zero.mp h2).resolve_left det)
  let e := (LinearEquiv.ofBijective L.toLinearMap
    ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have de : HasStrictFDerivAt (chargeMap s h) (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (x,y) :=
    (chargeMap_smooth s h (x,y) hl hr).hasStrictFDerivAt (by simp)
  exact ⟨de.toOpenPartialHomeomorph _,de.mem_toOpenPartialHomeomorph_source,rfl⟩

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Chart

abbrev Plane := ℝ × ℝ
abbrev Triple := Fin 3 → ℝ

/-- The spatial gradient components of a fixed linear combination of the
three logarithmic charges. A covector on charge ratios has coefficient sum zero. -/
def normalEquations (s h : ℝ) (c : Triple) (z : Plane) : Plane :=
  (∑ i, c i*logVelocity s h z.1 z.2 1 0 i, ∑ i, c i*logVelocity s h z.1 z.2 0 1 i)

private theorem velocity_linear (s h x y u v : ℝ) (i : Fin 3) :
    logVelocity s h x y u v i =
      u*logVelocity s h x y 1 0 i+v*logVelocity s h x y 0 1 i := by
  fin_cases i <;> dsimp [logVelocity,coordVelocity] <;> ring

theorem normalEquations_apply (s h : ℝ) (c : Triple) (z : Plane) (u v : ℝ) :
    u*(normalEquations s h c z).1+v*(normalEquations s h c z).2 =
      ∑ i, c i*logVelocity s h z.1 z.2 u v i := by
  unfold normalEquations
  simp only [Fin.sum_univ_three]
  rw [velocity_linear s h z.1 z.2 u v 0,velocity_linear s h z.1 z.2 u v 1,
    velocity_linear s h z.1 z.2 u v 2]
  ring

/-- The incidence equations test the actual differential of the charge map. -/
theorem normalEquations_zero_iff (s h : ℝ) (c : Triple) (z : Plane)
    (mass : ∑ i, c i=0) (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0)
    (hr : ∀ i, radii s h z.1 z.2 i ≠ 0) :
    normalEquations s h c z = 0 ↔ ∀ w : Plane,
      c 1*(fderiv ℝ (chargeMap s h) z w).1+c 2*(fderiv ℝ (chargeMap s h) z w).2=0 := by
  have e (u v : ℝ) : c 1*(fderiv ℝ (chargeMap s h) z (u,v)).1+
      c 2*(fderiv ℝ (chargeMap s h) z (u,v)).2 =
        u*(normalEquations s h c z).1+v*(normalEquations s h c z).2 := by
    rw [chargeMap_fderiv s h z.1 z.2 u v hl hr,normalEquations_apply]
    simp only [Fin.sum_univ_three] at mass ⊢
    linear_combination -logVelocity s h z.1 z.2 u v 0*mass
  constructor
  · rintro hz ⟨u,v⟩
    simp [e,hz]
  · intro H
    apply Prod.ext
    · simpa only [e,one_mul,zero_mul,add_zero,Prod.fst_zero] using H (1,0)
    · simpa only [e,one_mul,zero_mul,zero_add,Prod.snd_zero] using H (0,1)

def dualVector (s h : ℝ) (c : Triple) (z : Plane) : Plane :=
  let l := coordinates s h z.1 z.2
  (∑ i, c i/l i*coordVelocity s h 1 0 i, ∑ i, c i/l i*coordVelocity s h 0 1 i)

private theorem bary_test (s h : ℝ) (z : Plane) (hh : h ≠ 0) (i j : Fin 3) :
    (-dx s z.1 j)*coordVelocity s h 1 0 i+(-dy h z.2 j)*coordVelocity s h 0 1 i =
      (if i=j then 1 else 0)-coordinates s h z.1 z.2 i := by
  fin_cases i <;> fin_cases j <;> norm_num [dx,dy,coordVelocity,coordinates] <;>
    field_simp [hh] <;> ring

theorem dual_pair (s h : ℝ) (c : Triple) (z : Plane) (hh : h ≠ 0)
    (mass : ∑ i, c i=0) (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (j : Fin 3) :
    c j = coordinates s h z.1 z.2 j*
      ((-dx s z.1 j)*(dualVector s h c z).1+(-dy h z.2 j)*(dualVector s h c z).2) := by
  let l := coordinates s h z.1 z.2
  have eq : (-dx s z.1 j)*(dualVector s h c z).1+(-dy h z.2 j)*(dualVector s h c z).2 =
      ∑ i, ((if i=j then c i/l i else 0)-c i) := by
    unfold dualVector
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (-dx s z.1 j)*(c i/l i*coordVelocity s h 1 0 i)+
        (-dy h z.2 j)*(c i/l i*coordVelocity s h 0 1 i) =
        c i/l i*((-dx s z.1 j)*coordVelocity s h 1 0 i+(-dy h z.2 j)*coordVelocity s h 0 1 i) by ring,
      bary_test s h z hh]
    by_cases he : i=j <;> simp [he,l,div_mul_cancel₀ _ (hl _)]
    field_simp [hl i,hl j]
  rw [eq,Finset.sum_sub_distrib,mass,sub_zero]
  simp [l]
  field_simp [hl j]

end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum.Chart

theorem bary_moments (s h : ℝ) (z : Plane) (hh : h ≠ 0) :
    let l := coordinates s h z.1 z.2
    let p := fun i => -dx s z.1 i
    let q := fun i => -dy h z.2 i
    (∑ i, l i=1) ∧ (∑ i, l i*p i=0) ∧ (∑ i, l i*q i=0) ∧
    ∀ U V : ℝ, let b := coordVelocity s h U V
      (∑ i, b i=0) ∧ (∑ i, b i*p i=U) ∧ (∑ i, b i*q i=V) := by
  dsimp only
  refine ⟨?_,?_,?_,fun U V => ⟨?_,?_,?_⟩⟩ <;>
    simp [Fin.sum_univ_three,dx,dy,coordVelocity,coordinates] <;> field_simp [hh] <;> ring

theorem displacement_separation (s h : ℝ) (z : Plane) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (i j : Fin 3) (ne : i ≠ j) :
    dx s z.1 i*dy h z.2 j-dy h z.2 i*dx s z.1 j ≠ 0 := by
  let m (i j : Fin 3) := dx s z.1 i*dy h z.2 j-dy h z.2 i*dx s z.1 j
  have cy (i : Fin 3) : m (i+1) (i+2)=h*coordinates s h z.1 z.2 i := by
    fin_cases i <;> dsimp [m,dx,dy,coordinates] <;> field_simp [hh] <;> ring
  have f (i : Fin 3) := (cy i).trans_ne (mul_ne_zero hh (hl i))
  have g (i : Fin 3) : m (i+2) (i+1) ≠ 0 := by
    have := f i
    dsimp [m] at *
    intro e; apply this; linarith
  change m i j ≠ 0
  fin_cases i <;> fin_cases j <;> first | contradiction | exact f 0 | exact f 1 | exact f 2 | exact g 0 | exact g 1 | exact g 2

theorem radii_pos_of_chamber (s h : ℝ) (z : Plane) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (i : Fin 3) : 0 < radii s h z.1 z.2 i := by
  rw [radii_eq]
  by_contra! hn
  have X : dx s z.1 i = 0 := by nlinarith [sq_nonneg (dy h z.2 i)]
  have Y : dy h z.2 i = 0 := by nlinarith [sq_nonneg (dx s z.1 i)]
  exact displacement_separation s h z hh hl i (i+1) (by fin_cases i <;> decide) (by simp [X,Y])

theorem normalEquations_smooth (s h : ℝ) (c : Triple) (z : Plane)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (hr : ∀ i, radii s h z.1 z.2 i ≠ 0) :
    ContDiffAt ℝ ⊤ (normalEquations s h c) z := by
  have dl (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : Plane => coordinates s h p.1 p.2 i) z := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop
  have dr (i : Fin 3) : ContDiffAt ℝ ⊤ (fun p : Plane => radii s h p.1 p.2 i) z := by
    fin_cases i <;> dsimp [radii] <;> fun_prop
  unfold normalEquations logVelocity dx dy
  fun_prop (disch := first | exact hl _ | exact hr _)

end MaxwellCausticExtremum.Chart

end
end

section

namespace MaxwellCusp

def coeff (x y z p q r : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (x*y*z, p*y*z+x*q*z+x*y*r, p*q*z+p*y*r+x*q*r, p*q*r)

private theorem sum_prod (i j k : ℝ) : 0 ≤ (i+j+k)^2 - 3*(i*j+i*k+j*k) := by
  nlinarith [sq_nonneg (i-j), sq_nonneg (i-k), sq_nonneg (j-k)]

theorem newton_bounds (x y z p q r : ℝ) :
    let (d,a,b,c) := coeff x y z p q r
    3*b*d ≤ a^2 ∧ 3*a*c ≤ b^2 := by
  dsimp [coeff]
  constructor
  · nlinarith only [sum_prod (p*y*z) (x*q*z) (x*y*r)]
  · nlinarith only [sum_prod (p*q*z) (p*y*r) (x*q*r)]

/-- A single vertical direction is allowed; pairwise distinct projective
directions ensure the leading two coefficients cannot vanish together. -/
theorem coeff_nonzero (x y z p q r : ℝ)
    (hxy : p*y-q*x ≠ 0) (hxz : p*z-r*x ≠ 0) (hyz : q*z-r*y ≠ 0) :
    let (d,a,_,_) := coeff x y z p q r
    d ≠ 0 ∨ a ≠ 0 := by
  dsimp [coeff]
  by_cases hx : x = 0
  · subst x
    simp_all
  by_cases hy : y = 0
  · subst y
    simp_all
  by_cases hz : z = 0
  · subst z
    simp_all
  exact Or.inl (mul_ne_zero (mul_ne_zero hx hy) hz)

end MaxwellCusp

namespace MaxwellCusp

/-- The two components of the spatial gradient of the normalized
determinant never vanish simultaneously on the critical locus. -/
theorem no_zero_gradient (x y z p q r : ℝ)
    (hxy : p*y-q*x ≠ 0) (hxz : p*z-r*x ≠ 0) (hyz : q*z-r*y ≠ 0) :
    let (d,a,b,c) := coeff x y z p q r
    b = 2*d → c ≠ 2*a := by
  have h := newton_bounds x y z p q r
  have hn := coeff_nonzero x y z p q r hxy hxz hyz
  generalize coeff x y z p q r = tuple at *
  obtain ⟨d,a,b,c⟩ := tuple
  dsimp at *
  obtain ⟨h₁,h₂⟩ := h
  rintro rfl rfl
  rcases hn with hd | ha
  · nlinarith [sq_pos_of_ne_zero hd]
  · nlinarith [sq_pos_of_ne_zero ha]

end MaxwellCusp

namespace MaxwellCusp

/-- Strict turning of the projective normal of the logarithmic caustic. -/
theorem turn_pos (x y z p q r : ℝ)
    (hxy : p*y-q*x ≠ 0) (hxz : p*z-r*x ≠ 0) (hyz : q*z-r*y ≠ 0) :
    let (d,a,b,c) := coeff x y z p q r
    0 < (c-2*a)^2+2*(b-2*d)*(b-3*d) := by
  have h := newton_bounds x y z p q r
  have hn := coeff_nonzero x y z p q r hxy hxz hyz
  have hgrad := no_zero_gradient x y z p q r hxy hxz hyz
  generalize coeff x y z p q r = tuple at *
  obtain ⟨d,a,b,c⟩ := tuple
  dsimp at *
  obtain ⟨h₁,h₂⟩ := h
  by_cases hpos : 0 < (b-2*d)*(b-3*d)
  · nlinarith [sq_nonneg (c-2*a)]
  have hp := le_of_not_gt hpos
  by_cases hd : d = 0
  · subst d
    have hb : b = 0 := by nlinarith [sq_nonneg b]
    subst b
    have hne := hgrad (by ring)
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hne)]
  have hb : 0 ≤ (b-2*d)*d := by
    nlinarith only [hp, sq_nonneg (b-2*d)]
  have hh : b^2 ≤ 9*d^2 := by
    nlinarith only [hp, sq_nonneg (b-3*d), sq_nonneg (b-2*d)]
  nlinarith only [h₁,h₂,hb,hh,sq_pos_of_ne_zero hd,sq_nonneg c,
    sq_nonneg (2*b-5*d)]

end MaxwellCusp

end

section

noncomputable section

namespace MaxwellCusp.Spatial.Normal

def offsetX (x y : Triple) := -(8*D x+B x y)
def offsetY (x y : Triple) := -(2*A x y+5/2*C y)

private def X (x y : Triple) (i : Fin 3) := 3*x i*K x y i + offsetX x y
private def Y (x y : Triple) (i : Fin 3) := 3/2*y i*K x y i + offsetY x y

private theorem opposite (x y : Triple) (unit : ∀ i, x i^2+y i^2=1) (i j : Fin 3)
    (ne : i ≠ j) : X x y i*x j+Y x y i*y j = -K x y j := by
  have h : X x y i*x j+Y x y i*y j = -K x y j*(x j^2+y j^2) := by
    fin_cases i <;> fin_cases j <;> first | exact (ne rfl).elim |
      dsimp [X,Y,K,offsetX,offsetY,A,B,C,D]; ring
  rw [h,unit,mul_one]

/-- Logarithmic barycentric velocity, including configurations with a vertical
site direction. The additive offsets are common to all three sites. -/
theorem bary_velocity (l r x y b : Triple) (κ u v : ℝ)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ)
    (mass : ∑ i, l i=1) (fx : ∑ i, l i*r i*x i=0) (fy : ∑ i, l i*r i*y i=0)
    (db : ∑ i, b i=0) (bx : ∑ i, b i*r i*x i=u) (by' : ∑ i, b i*r i*y i=v)
    (i : Fin 3) :
    κ*b i = l i*((3*x i*K x y i+offsetX x y)*u+(3/2*y i*K x y i+offsetY x y)*v) := by
  let z j := r j*(X x y i*x j+Y x y i*y j)+κ
  have vanish (j : Fin 3) (h : j ≠ i) : z j = 0 := by
    dsimp [z]
    rw [opposite x y unit i j h.symm,mul_neg,scale]; ring
  have one (f : Triple) : ∑ j, f j*z j=f i*z i :=
    Finset.sum_eq_single i (fun j _ hj => by rw [vanish j hj,mul_zero]) (by simp)
  have split (f : Triple) : ∑ j, f j*z j =
      X x y i*(∑ j, f j*r j*x j)+Y x y i*(∑ j, f j*r j*y j)+κ*∑ j, f j := by
    dsimp [z]; simp only [Fin.sum_univ_three]; ring
  have m := (one l).symm.trans (split l)
  have n := (one b).symm.trans (split b)
  rw [fx,fy,mass] at m
  rw [bx,by',db] at n
  change κ*b i=l i*(X x y i*u+Y x y i*v)
  linear_combination l i*n-b i*m

def moment (l x f : Triple) := ∑ i, l i*x i*f i

/-- The four finite sums needed in the second derivative of the charge map. -/
private theorem moments (l r x y bx : Triple) (κ : ℝ)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ)
    (mass : ∑ i, l i=1) (fx : ∑ i, l i*r i*x i=0) (fy : ∑ i, l i*r i*y i=0)
    (db : ∑ i, bx i=0) (bx₁ : ∑ i, bx i*r i*x i=1) (bx₂ : ∑ i, bx i*r i*y i=0)
    (xx : ∑ i, l i*x i^2=1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3) :
    let k := K x y
    moment l x k = (8*D x+B x y)/3 ∧
    moment l x (fun i => k i*x i^2) = (4*D x+B x y)/3 ∧
    moment l x (fun i => k i*x i*y i) = C y/3 ∧
    moment l x (fun i => k i*y i^2) = 4*D x/3 := by
  dsimp only
  have v := bary_velocity l r x y bx κ 1 0 unit scale mass fx fy db bx₁ bx₂
  have sm : moment l x (K x y) = (8*D x+B x y)/3 := by
    simp only [moment,Fin.sum_univ_three] at *
    simp only [offsetX] at v
    linear_combination -(v 0+v 1+v 2)/3+κ*db/3+(8*D x+B x y)*mass/3
  have p (i : Fin 3) : x i*K x y i*y i^2=2*D x*y i^2+C y*x i*y i := by
    fin_cases i <;> dsimp [D,C,K] <;> ring
  have q (i : Fin 3) : x i*K x y i*x i*y i=2*D x*x i*y i+C y*x i^2 := by
    fin_cases i <;> dsimp [D,C,K] <;> ring
  have sy : moment l x (fun i => K x y i*y i^2)=4*D x/3 := by
    simp only [moment,Fin.sum_univ_three] at *
    linear_combination l 0*p 0+l 1*p 1+l 2*p 2+2*D x*yy+C y*xy
  refine ⟨sm,?_,?_,sy⟩
  · simp only [moment,Fin.sum_univ_three] at *
    linear_combination sm-sy+l 0*x 0*K x y 0*unit 0+l 1*x 1*K x y 1*unit 1+
      l 2*x 2*K x y 2*unit 2
  · simp only [moment,Fin.sum_univ_three] at *
    linear_combination l 0*q 0+l 1*q 1+l 2*q 2+2*D x*xy+C y*xx

/-- Differential in direction w of the first derivative in direction z of
the fixed scalar projection whose three coefficients are λᵢ rᵢ xᵢ. -/
def second (l r x y b d : Triple) (u v a c : ℝ) :=
  ∑ i, l i*r i*x i*(-(b i/l i)*(d i/l i)+
    3*(u*a+v*c-2*(x i*u+y i*v)*(x i*a+y i*c))/r i^2)

theorem second_eq (l r x y : Triple) (b : ℝ → ℝ → Triple) (κ : ℝ)
    (nk : κ ≠ 0) (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (scale : ∀ i, r i*K x y i=κ)
    (mass : ∑ i, l i=1) (fx : ∑ i, l i*r i*x i=0) (fy : ∑ i, l i*r i*y i=0)
    (db : ∀ u v, ∑ i, b u v i=0) (bx : ∀ u v, ∑ i, b u v i*r i*x i=u)
    (by' : ∀ u v, ∑ i, b u v i*r i*y i=v)
    (xx : ∑ i, l i*x i^2=1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3)
    (u v a c : ℝ) :
    κ*second l r x y (b u v) (b a c) u v a c =
      -2*(B x y-2*D x)*u*a+(2*A x y-C y)*(u*c+v*a)+(B x y-3*D x)*v*c := by
  let t (u v : ℝ) (i : Fin 3) := 3*x i*u+3/2*y i*v
  let off (u v : ℝ) := offsetX x y*u+offsetY x y*v
  have vel (u v : ℝ) (i : Fin 3) : b u v i/l i=t u v i/r i+off u v/κ := by
    have h := bary_velocity l r x y (b u v) κ u v unit scale mass fx fy (db ..) (bx ..) (by' ..) i
    field_simp [hl i,hr i,nk]
    dsimp [t,off]
    linear_combination r i*h + l i*(3*x i*u+3/2*y i*v)*scale i
  let k := K x y
  let term (i : Fin 3) := l i*x i*k i*(3*(u*a+v*c-2*(x i*u+y i*v)*(x i*a+y i*c))-
    t u v i*t a c i)-off u v*l i*x i*t a c i-off a c*l i*x i*t u v i-
    off u v*off a c/κ*(l i*r i*x i)
  have one (i : Fin 3) : κ*(l i*r i*x i*(-(b u v i/l i)*(b a c i/l i)+
      3*(u*a+v*c-2*(x i*u+y i*v)*(x i*a+y i*c))/r i^2)) = term i := by
    rw [vel,vel]
    dsimp only [term,k]
    rw [show K x y i=κ/r i from (eq_div_iff (hr i)).mpr (by rw [mul_comm,scale])]
    field_simp [hr i,nk]
    ring
  rw [second,Finset.mul_sum,Finset.sum_congr rfl (fun i _ => one i)]
  obtain ⟨m0,mxx,mxy,myy⟩ := moments l r x y (b 1 0) κ unit scale mass fx fy (db ..)
    (bx ..) (by' ..) xx xy yy
  simp only [moment,Fin.sum_univ_three] at m0 mxx mxy myy xx xy fx ⊢
  dsimp only [term,k,t]
  linear_combination (norm := (dsimp [off,offsetX,offsetY]; ring)) 3*(u*a+v*c)*m0-15*u*a*mxx-(21/2)*(u*c+v*a)*mxy-
    (33/4)*v*c*myy-3*(off u v*a+off a c*u)*xx-
    (3/2)*(off u v*c+off a c*v)*xy-(off u v*off a c/κ)*fx

end MaxwellCusp.Spatial.Normal

namespace MaxwellCusp.Spatial.Normal

/-- A scalar projection of the log charges, differentiated in the fixed
direction (a,c), along the straight spatial path with velocity (u,v).
The projection coefficients are frozen at the base point. -/
def projectedSlope (l r x y b d : Triple) (u v a c t : ℝ) :=
  ∑ i, l i*r i*x i*(d i/(l i+t*b i) -
    3*((r i*x i-t*u)*a+(r i*y i-t*v)*c)/((r i*x i-t*u)^2+(r i*y i-t*v)^2))

theorem projectedSlope_deriv (l r x y b d : Triple) (u v a c : ℝ)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0) (unit : ∀ i, x i^2+y i^2=1) :
    HasDerivAt (projectedSlope l r x y b d u v a c) (second l r x y b d u v a c) 0 := by
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.const_mul
  have lin (z k : ℝ) : HasDerivAt (fun t : ℝ => z-t*k) (-k) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const k).const_sub z
  have dl : HasDerivAt (fun t : ℝ => l i+t*b i) (b i) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (b i)).const_add (l i)
  have p := lin (r i*x i) u
  have q := lin (r i*y i) v
  have sq : (r i*x i)^2+(r i*y i)^2=r i^2 := by linear_combination (r i)^2*unit i
  have z := (p.pow 2).add (q.pow 2)
  have m := (((p.mul_const a).add (q.mul_const c)).const_mul 3).div z
    (by simpa [sq] using pow_ne_zero 2 (hr i))
  have n := ((hasDerivAt_const (0:ℝ) (d i)).div dl (by simpa using hl i)).sub m
  convert! n using 1
  simp [Pi.pow_apply,Pi.add_apply,sq]
  field_simp [hl i,hr i]
  ring

/-- Each fixed normal projection has a nondegenerate saddle at the critical
point. This is the two by two Jacobian for the normal-direction equations
when written as the two components of the gradient of the projection. -/
theorem projectedSlope_det_neg (l r x y : Triple) (b : ℝ → ℝ → Triple)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ i, r i ≠ 0)
    (unit : ∀ i, x i^2+y i^2=1) (sep : ∀ i j, i ≠ j → minor x y i j ≠ 0)
    (mass : ∑ i, l i=1) (fx : ∑ i, l i*r i*x i=0) (fy : ∑ i, l i*r i*y i=0)
    (db : ∀ u v, ∑ i, b u v i=0) (bx : ∀ u v, ∑ i, b u v i*r i*x i=u)
    (by' : ∀ u v, ∑ i, b u v i*r i*y i=v)
    (xx : ∑ i, l i*x i^2=1/3) (xy : ∑ i, l i*x i*y i=0) (yy : ∑ i, l i*y i^2=2/3) :
    let M (u v a c : ℝ) := deriv (projectedSlope l r x y (b u v) (b a c) u v a c) 0
    M 1 0 1 0*M 0 1 0 1-M 1 0 0 1*M 0 1 1 0 < 0 := by
  obtain ⟨κ,nk,scale⟩ := common_scale l r x y hl hr sep xx xy yy fx fy
  let M (u v a c : ℝ) := deriv (projectedSlope l r x y (b u v) (b a c) u v a c) 0
  have e (u v a c : ℝ) := second_eq l r x y b κ nk hl hr unit scale mass fx fy db bx by' xx xy yy u v a c
  have ent (u v a c : ℝ) : κ*M u v a c =
      -2*(B x y-2*D x)*u*a+(2*A x y-C y)*(u*c+v*a)+(B x y-3*D x)*v*c := by
    dsimp [M]
    rw [(projectedSlope_deriv l r x y (b u v) (b a c) u v a c hl hr unit).deriv,e]
  have turn : 0 < (C y-2*A x y)^2+2*(B x y-2*D x)*(B x y-3*D x) := by
    apply MaxwellCusp.turn_pos (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)
    all_goals
      first | exact sub_ne_zero.mpr (fun h => (sep 1 0 (by decide)) (by dsimp [minor]; linarith))
            | exact sub_ne_zero.mpr (fun h => (sep 2 0 (by decide)) (by dsimp [minor]; linarith))
            | exact sub_ne_zero.mpr (fun h => (sep 2 1 (by decide)) (by dsimp [minor]; linarith))
  change M 1 0 1 0*M 0 1 0 1-M 1 0 0 1*M 0 1 1 0 < 0
  apply neg_of_mul_neg_right (a := κ^2) _ (sq_nonneg _)
  rw [show κ^2*(M 1 0 1 0*M 0 1 0 1-M 1 0 0 1*M 0 1 1 0) =
    (κ*M 1 0 1 0)*(κ*M 0 1 0 1)-(κ*M 1 0 0 1)*(κ*M 0 1 1 0) by ring]
  simp only [ent]
  linarith only [turn]

end MaxwellCusp.Spatial.Normal

end
end

section

noncomputable section
namespace MaxwellCusp.Spatial

/-- When the two null equations have zero derivative at a cusp, the spatial
velocity is parallel to the kernel and the derivative of the actual cubic is
the signed null speed times the strictly negative reduced quartic. -/
theorem cusp_tangent_derivative (l r x : ℝ → Triple) (y b : Triple) (t u v ω : ℝ)
    (hl : ∀ i, l t i ≠ 0) (hr : ∀ i, r t i ≠ 0)
    (unit : ∀ i, x t i^2+y i^2=1) (sep : ∀ i j, i ≠ j → minor (x t) y i j ≠ 0)
    (mass : ∑ i, l t i=1) (fx : ∑ i, l t i*r t i*x t i=0) (fy : ∑ i, l t i*r t i*y i=0)
    (bm : ∑ i, b i=0) (bx : ∑ i, b i*r t i*x t i=u) (by' : ∑ i, b i*r t i*y i=v)
    (xx : ∑ i, l t i*x t i^2=1/3) (xy : ∑ i, l t i*x t i*y i=0) (yy : ∑ i, l t i*y i^2=2/3)
    (cusp : cubicNull (l t) (r t) (x t)=0)
    (nullX : nullDerivative (l t) b (r t) (x t) y u v=0)
    (nullY : mixedEntryDerivative (l t) b (r t) (x t) y u v+ω=0)
    (dl : ∀ i, HasDerivAt (fun z => l z i) (b i) t)
    (dr : ∀ i, HasDerivAt (fun z => r z i) (-(x t i*u+y i*v)) t)
    (dx : ∀ i, HasDerivAt (fun z => x z i)
      ((x t i*(x t i*u+y i*v)-u)/r t i+ω*y i) t) :
    let Q := quarticNull (l t) (r t) (x t)-3*(cubicMixed (l t) (r t) (x t) y)^2
    v=0 ∧ ω= -u*cubicMixed (l t) (r t) (x t) y ∧ Q < 0 ∧
      HasDerivAt (fun z => cubicNull (l z) (r z) (x z)) (u*Q) t := by
  dsimp only
  obtain ⟨κ,nk,scale⟩ := common_scale (l t) (r t) (x t) y hl hr sep xx xy yy fx fy
  obtain ⟨j,m,_⟩ := homogeneous_jets (l t) (r t) (x t) y κ hr unit scale sep xx xy yy
  rw [cusp,mul_zero] at j
  have hB : B (x t) y=2*D (x t) := by linarith
  have grad := gradient_identity (l t) b (r t) (x t) y κ u v unit hr scale bm bx by' xx xy yy
  rw [nullX,hB] at grad
  have neg := cusp_quartic_negative (l t) (r t) (x t) y κ hr unit scale sep xx xy yy cusp
  have nonzero : C y-2*A (x t) y ≠ 0 := by
    have e := gradient_norm (x t) y
    rw [hB,sub_self] at e
    have p i : 0 < 2*x t i^2+y i^2 := by nlinarith only [unit i,sq_nonneg (x t i)]
    intro z
    rw [z] at e
    nlinarith only [e,mul_pos (mul_pos (p 0) (p 1)) (p 2)]
  have vz : v=0 := (mul_eq_zero.mp (show (C y-2*A (x t) y)*v=0 by linarith only [grad])).resolve_left nonzero
  rw [vz] at by' nullY dx dr ⊢
  have mixed := mixed_identity (l t) b (r t) (x t) y κ u 0 unit hr scale bx by' xx xy yy
  unfold mixedDerivative at mixed
  have rot : ω= -u*cubicMixed (l t) (r t) (x t) y := by
    apply mul_left_cancel₀ nk
    linear_combination κ*nullY-mixed+u*m
  refine ⟨rfl,rot,neg,?_⟩
  let c := Normal.offsetX (x t) y*u/κ
  have dl' (i : Fin 3) : b i=l t i*(c+3*u*x t i/r t i) := by
    have vel := Normal.bary_velocity (l t) (r t) (x t) y b κ u 0 unit scale mass fx fy bm bx by' i
    dsimp [c]
    field_simp [nk,hr i]
    linear_combination (r t i)*vel+3*u*l t i*x t i*scale i
  let M := cubicMixed (l t) (r t) (x t) y
  let third i := l t i*(15*(x t i)^3-9*x t i)/r t i
  let cross i := l t i*(15*(x t i)^2*y i-3*y i)/r t i
  let fourth i := l t i*(105*(x t i)^4-90*(x t i)^2+9)/(r t i)^2
  have term (i : Fin 3) : HasDerivAt (fun z => l z i*(15*(x z i)^3-9*x z i)/r z i)
      (u*fourth i+c*third i-3*u*M*cross i) t := by
    convert! ((dl i).mul ((((dx i).pow 3).const_mul 15).sub ((dx i).const_mul 9))).div (dr i) (hr i) using 1
    rw [dl',rot]
    dsimp [third,cross,fourth,M]
    field_simp [hr i]
    ring
  convert! HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => term i) using 1
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum]
  change _ = u*quarticNull (l t) (r t) (x t)+c*cubicNull (l t) (r t) (x t)-3*u*M*M
  rw [cusp]; dsimp [M]; ring

end MaxwellCusp.Spatial

namespace MaxwellCusp.Spatial

/-- A first-order deformation preserving the two kernel equations and the
cubic cusp equation has zero spatial and angular velocity at fixed shape. -/
theorem cusp_frame_rigid (l r x y : ℝ → Triple) (b : Triple) (t u v ω : ℝ)
    (hl : ∀ i, l t i ≠ 0) (hr : ∀ i, r t i ≠ 0)
    (unit : ∀ i, x t i^2+y t i^2=1) (sep : ∀ i j, i ≠ j → minor (x t) (y t) i j ≠ 0)
    (mass : ∑ i, l t i=1) (fx : ∑ i, l t i*r t i*x t i=0) (fy : ∑ i, l t i*r t i*y t i=0)
    (bm : ∑ i, b i=0) (bx : ∑ i, b i*r t i*x t i=u) (by' : ∑ i, b i*r t i*y t i=v)
    (xx : ∑ i, l t i*x t i^2=1/3) (xy : ∑ i, l t i*x t i*y t i=0) (yy : ∑ i, l t i*y t i^2=2/3)
    (cusp : cubicNull (l t) (r t) (x t)=0)
    (dl : ∀ i, HasDerivAt (fun z => l z i) (b i) t)
    (dr : ∀ i, HasDerivAt (fun z => r z i) (-(x t i*u+y t i*v)) t)
    (dx : ∀ i, HasDerivAt (fun z => x z i)
      ((x t i*(x t i*u+y t i*v)-u)/r t i+ω*y t i) t)
    (dy : ∀ i, HasDerivAt (fun z => y z i)
      ((y t i*(x t i*u+y t i*v)-v)/r t i-ω*x t i) t)
    (dxx : HasDerivAt (fun z => ∑ i, l z i*x z i^2) 0 t)
    (dxy : HasDerivAt (fun z => ∑ i, l z i*x z i*y z i) 0 t)
    (d3 : HasDerivAt (fun z => cubicNull (l z) (r z) (x z)) 0 t) :
    u=0 ∧ v=0 ∧ ω=0 := by
  have n := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (dl i).mul ((dx i).pow 2))).unique dxx
  have cross := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ((dl i).mul (dx i)).mul (dy i))).unique dxy
  have nullX : nullDerivative (l t) b (r t) (x t) (y t) u v=0 := by
    dsimp [nullDerivative]
    simp only [Fin.sum_univ_three] at n xy ⊢
    dsimp at n
    linear_combination 3*n-6*ω*xy
  have nullY : mixedEntryDerivative (l t) b (r t) (x t) (y t) u v+ω=0 := by
    dsimp [mixedEntryDerivative]
    simp only [Fin.sum_univ_three] at cross xx yy ⊢
    dsimp at cross
    linear_combination 3*cross+3*ω*xx-3*ω*yy
  obtain ⟨vz,rot,neg,d⟩ := cusp_tangent_derivative l r x (y t) b t u v ω hl hr unit sep mass fx fy
    bm bx by' xx xy yy cusp nullX nullY dl dr dx
  have uz := (mul_eq_zero.mp (d.unique d3)).resolve_right neg.ne
  exact ⟨uz,vz,by simp [rot,uz]⟩

end MaxwellCusp.Spatial

end
end

section

noncomputable section
namespace MaxwellCausticExtremum.Chart.Cusp
open MaxwellCusp.Spatial (cubicNull cusp_frame_rigid)

abbrev State := Plane × Plane

def radiusAt (s h : ℝ) (p : Plane) (i : Fin 3) := Real.sqrt (radii s h p.1 p.2 i)
def X (s h : ℝ) (w : State) (i : Fin 3) :=
  (-w.2.1*dx s w.1.1 i-w.2.2*dy h w.1.2 i)/radiusAt s h w.1 i
def Y (s h : ℝ) (w : State) (i : Fin 3) :=
  (w.2.2*dx s w.1.1 i-w.2.1*dy h w.1.2 i)/radiusAt s h w.1 i

def equations (s h : ℝ) (w : State) : State :=
  let l := coordinates s h w.1.1 w.1.2
  let x := X s h w
  let y := Y s h w
  ((w.2.1^2+w.2.2^2-1,(∑ i, l i*x i^2)-1/3),
   (∑ i, l i*x i*y i,cubicNull l (radiusAt s h w.1) x))

private theorem rxy (s h : ℝ) (p : State) (i : Fin 3) (hr : radiusAt s h p.1 i ≠ 0) :
    radiusAt s h p.1 i*X s h p i= -p.2.1*dx s p.1.1 i-p.2.2*dy h p.1.2 i ∧
    radiusAt s h p.1 i*Y s h p i= p.2.2*dx s p.1.1 i-p.2.1*dy h p.1.2 i := by
  constructor <;> dsimp [X,Y] <;> field_simp [hr]

private theorem linear (z k : ℝ) : HasDerivAt (fun t : ℝ => z+t*k) k 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const k).const_add z

private def line (p v : State) (t : ℝ) : State :=
  ((p.1.1+t*v.1.1,p.1.2+t*v.1.2),(p.2.1+t*v.2.1,p.2.2+t*v.2.2))

private theorem line_zero (p v : State) : line p v 0=p := by simp [line]

/-- All four oriented cusp constraints have independent spatial/frame
derivatives. In particular a cusp cannot split when the shape varies. -/
theorem equations_regular (s h : ℝ) (w : State) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h w.1.1 w.1.2 i ≠ 0) (zero : equations s h w=0) :
    Function.Injective (fderiv ℝ (equations s h) w) := by
  let a := w.2.1
  let k := w.2.2
  let x := X s h w
  let y := Y s h w
  let l := coordinates s h w.1.1 w.1.2
  let r := radiusAt s h w.1
  have unit : a^2+k^2=1 := sub_eq_zero.mp (congrArg (fun z : State => z.1.1) zero)
  have xx : ∑ i, l i*x i^2=1/3 := sub_eq_zero.mp (congrArg (fun z : State => z.1.2) zero)
  have xy : ∑ i, l i*x i*y i=0 := congrArg (fun z : State => z.2.1) zero
  have cusp : cubicNull l r x=0 := congrArg (fun z : State => z.2.2) zero
  have hr i := radii_pos_of_chamber s h w.1 hh hl i
  have nr i : r i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have rs i : r i^2=dx s w.1.1 i^2+dy h w.1.2 i^2 := (Real.sq_sqrt (hr i).le).trans (radii_eq ..)
  have rx i : r i*x i= -a*dx s w.1.1 i-k*dy h w.1.2 i := (rxy s h w i (nr i)).1
  have ry i : r i*y i=k*dx s w.1.1 i-a*dy h w.1.2 i := (rxy s h w i (nr i)).2
  have un i : x i^2+y i^2=1 := by
    dsimp only [x,y,X,Y]; change (_/r i)^2+(_/r i)^2=1
    field_simp [nr i]
    linear_combination (dx s w.1.1 i^2+dy h w.1.2 i^2)*unit-rs i
  have sep (i j : Fin 3) (ne : i ≠ j) : MaxwellCusp.Spatial.minor x y i j ≠ 0 := by
    intro e
    apply displacement_separation s h w.1 hh hl i j ne
    dsimp only [MaxwellCusp.Spatial.minor,x,y,X,Y] at e
    change (_/r i)*(_/r j)-(_/r i)*(_/r j)=0 at e
    field_simp [nr i,nr j] at e
    linear_combination e-(dx s w.1.1 i*dy h w.1.2 j-dy h w.1.2 i*dx s w.1.1 j)*unit
  obtain ⟨mass,fx,fy,db⟩ := bary_moments s h w.1 hh
  change ∑ i, l i=1 at mass
  have yy : ∑ i, l i*y i^2=2/3 := by
    simp only [Fin.sum_univ_three] at mass xx ⊢
    linear_combination l 0*un 0+l 1*un 1+l 2*un 2+mass-xx
  have rotate (b : Triple) (U V : ℝ) (P : ∑ i, b i*(-dx s w.1.1 i)=U)
      (Q : ∑ i, b i*(-dy h w.1.2 i)=V) :
      (∑ i, b i*r i*x i)=a*U+k*V ∧ (∑ i, b i*r i*y i)= -k*U+a*V := by
    simp only [Fin.sum_univ_three,mul_assoc,rx,ry] at P Q ⊢
    constructor
    · linear_combination a*P+k*Q
    · linear_combination -k*P+a*Q
  obtain ⟨fx',fy'⟩ := rotate l 0 0 fx fy
  simp only [mul_zero,add_zero] at fx' fy'
  have diff : DifferentiableAt ℝ (equations s h) w := by
    have dl (i : Fin 3) : DifferentiableAt ℝ (fun q : State => coordinates s h q.1.1 q.1.2 i) w := by
      fin_cases i <;> dsimp [coordinates] <;> fun_prop
    have R i : DifferentiableAt ℝ (fun q : State => radii s h q.1.1 q.1.2 i) w := by
      fin_cases i <;> dsimp [radii] <;> fun_prop
    have Dr i : DifferentiableAt ℝ (fun q : State => radiusAt s h q.1 i) w :=
      (R i).sqrt (hr i).ne'
    have Dx i : DifferentiableAt ℝ (fun q => X s h q i) w := by
      unfold X dx dy; fun_prop (disch := exact nr i)
    have Dy i : DifferentiableAt ℝ (fun q => Y s h q i) w := by
      unfold Y dx dy; fun_prop (disch := exact nr i)
    change DifferentiableAt ℝ (fun q : State =>
      ((q.2.1^2+q.2.2^2-1,(∑ i, coordinates s h q.1.1 q.1.2 i*(X s h q i)^2)-1/3),
       (∑ i, coordinates s h q.1.1 q.1.2 i*X s h q i*Y s h q i,
        ∑ i, coordinates s h q.1.1 q.1.2 i*(15*(X s h q i)^3-9*X s h q i)/radiusAt s h q.1 i))) w
    fun_prop (disch := exact nr _)
  apply (injective_iff_map_eq_zero _).mpr
  intro W ker
  let P := line w W
  let u := a*W.1.1+k*W.1.2
  let v := -k*W.1.1+a*W.1.2
  let ω := -k*W.2.1+a*W.2.2
  let L t := coordinates s h (P t).1.1 (P t).1.2
  let R t := radiusAt s h (P t).1
  let X' t := X s h (P t)
  let Y' t := Y s h (P t)
  let b := coordVelocity s h W.1.1 W.1.2
  obtain ⟨bm,bx,by'⟩ := db W.1.1 W.1.2
  obtain ⟨bx',by''⟩ := rotate b _ _ bx by'
  have lineD : HasDerivAt P W 0 := ((linear _ _).prodMk (linear _ _)).prodMk ((linear _ _).prodMk (linear _ _))
  have eqD := diff.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) lineD (line_zero w W).symm
  rw [ker] at eqD
  let fst := ContinuousLinearMap.fst ℝ ℝ ℝ
  let snd := ContinuousLinearMap.snd ℝ ℝ ℝ
  have p1 := (ContinuousLinearMap.fst ℝ Plane Plane).hasFDerivAt.comp_hasDerivAt 0 eqD
  have p2 := (ContinuousLinearMap.snd ℝ Plane Plane).hasFDerivAt.comp_hasDerivAt 0 eqD
  have din := fst.hasFDerivAt.comp_hasDerivAt 0 p1
  have dxx := snd.hasFDerivAt.comp_hasDerivAt 0 p1
  have dxy := fst.hasFDerivAt.comp_hasDerivAt 0 p2
  have dcu := snd.hasFDerivAt.comp_hasDerivAt 0 p2
  have nn := ((((linear a W.2.1).pow 2).add ((linear k W.2.2).pow 2)).sub_const 1).unique din
  simp [fst] at nn
  have ort : a*W.2.1+k*W.2.2=0 := by linarith only [nn]
  have oa : W.2.1= -ω*k := by dsimp [ω]; linear_combination a*ort-W.2.1*unit
  have ok : W.2.2=ω*a := by dsimp [ω]; linear_combination k*ort-W.2.2*unit
  have dl (i : Fin 3) : HasDerivAt (fun t => L t i) (b i) 0 := by
    convert! linear (l i) (b i) using 1
    funext t; exact coordinates_line .. 
  have dX (i : Fin 3) : HasDerivAt (fun t => dx s (P t).1.1 i) W.1.1 0 := by
    simpa [P,line,dx] using (linear w.1.1 W.1.1).sub_const ((![0,1,s] : Triple) i)
  have dY (i : Fin 3) : HasDerivAt (fun t => dy h (P t).1.2 i) W.1.2 0 := by
    simpa [P,line,dy] using (linear w.1.2 W.1.2).sub_const ((![0,0,h] : Triple) i)
  have at0 : P 0=w := line_zero w W
  have radial (i : Fin 3) : r i*(x i*u+y i*v)= -(dx s w.1.1 i*W.1.1+dy h w.1.2 i*W.1.2) := by
    dsimp only [u,v]
    linear_combination (a*W.1.1+k*W.1.2)*rx i+(-k*W.1.1+a*W.1.2)*ry i-
      (dx s w.1.1 i*W.1.1+dy h w.1.2 i*W.1.2)*unit
  have dr (i : Fin 3) : HasDerivAt (fun t => R t i) (-(x i*u+y i*v)) 0 := by
    have rr := ((dX i).pow 2).add ((dY i).pow 2)
    have e := rr.sqrt (by simpa [at0,← radii_eq] using (hr i).ne')
    convert! e using 1
    · funext t; simp [R,radiusAt,radii_eq]
    · simp [at0,← radii_eq]
      change _ = _/(2*r i)
      field_simp [nr i]
      linear_combination -radial i
  have derivX (i : Fin 3) : HasDerivAt (fun t => X' t i)
      ((x i*(x i*u+y i*v)-u)/r i+ω*y i) 0 := by
    have na : HasDerivAt (fun t => (P t).2.1) (-ω*k) 0 := oa ▸ linear a W.2.1
    have nk : HasDerivAt (fun t => (P t).2.2) (ω*a) 0 := ok ▸ linear k W.2.2
    have d := (((na.neg.mul (dX i)).sub (nk.mul (dY i))).div (dr i) (by simpa [R,at0] using nr i))
    convert! d using 1
    simp [R,at0]
    change _ = _/(r i)^2
    field_simp [nr i]
    dsimp [u,v,a,k] at *
    linear_combination (r i*ω)*ry i+(x i*u+y i*v)*rx i
  have derivY (i : Fin 3) : HasDerivAt (fun t => Y' t i)
      ((y i*(x i*u+y i*v)-v)/r i-ω*x i) 0 := by
    have na : HasDerivAt (fun t => (P t).2.1) (-ω*k) 0 := oa ▸ linear a W.2.1
    have nk : HasDerivAt (fun t => (P t).2.2) (ω*a) 0 := ok ▸ linear k W.2.2
    have d := (((nk.mul (dX i)).sub (na.mul (dY i))).div (dr i) (by simpa [R,at0] using nr i))
    convert! d using 1
    simp [R,at0]
    change _ = _/(r i)^2
    field_simp [nr i]
    linear_combination (norm := (dsimp [u,v,a,k]; ring)) -(r i*ω)*rx i+(x i*u+y i*v)*ry i
  have zxx : HasDerivAt (fun t => ∑ i, L t i*(X' t i)^2) 0 0 := by
    convert! dxx.add_const (1/3:ℝ) using 1
    funext t
    dsimp [L,X',snd,equations,Function.comp_def]
    ring
  have zxy : HasDerivAt (fun t => ∑ i, L t i*X' t i*Y' t i) 0 0 := dxy
  have zc : HasDerivAt (fun t => cubicNull (L t) (R t) (X' t)) 0 0 := dcu
  have atL : L 0=l := by dsimp [L]; rw [at0]
  have atR : R 0=r := by dsimp [R]; rw [at0]
  have atX : X' 0=x := by dsimp [X']; rw [at0]
  have atY : Y' 0=y := by dsimp [Y']; rw [at0]
  have rigid := cusp_frame_rigid L R X' Y' b 0 u v ω
  simp only [atL,atR,atX,atY] at rigid
  obtain ⟨uz,vz,oz⟩ := rigid hl nr un sep mass fx' fy' bm bx' by'' xx xy yy cusp dl dr derivX derivY zxx zxy zc
  apply Prod.ext
  · apply Prod.ext <;> dsimp [u,v] at uz vz
    · change W.1.1=0
      linear_combination a*uz-k*vz-W.1.1*unit
    · change W.1.2=0
      linear_combination k*uz+a*vz-W.1.2*unit
  · apply Prod.ext <;> simp [oa,ok,oz]

end MaxwellCausticExtremum.Chart.Cusp

end
end

section

noncomputable section
open MaxwellCusp.Spatial
namespace MaxwellCausticExtremum.Chart.Cusp

theorem kernel_iff (s h : ℝ) (z n : Plane) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (un : n.1^2+n.2^2=1) :
    fderiv ℝ (chargeMap s h) z n=0 ↔
      (∑ i, coordinates s h z.1 z.2 i*X s h (z,n) i^2)=1/3 ∧
      (∑ i, coordinates s h z.1 z.2 i*X s h (z,n) i*Y s h (z,n) i)=0 := by
  let l := coordinates s h z.1 z.2
  let r := radiusAt s h z
  let p := dx s z.1
  let q := dy h z.2
  let a := n.1
  let k := n.2
  let x := X s h (z,n)
  let y := Y s h (z,n)
  let R := radii s h z.1 z.2
  have hp i := radii_pos_of_chamber s h z hh hl i
  have nr i : r i ≠ 0 := (Real.sqrt_pos.mpr (hp i)).ne'
  have sq i : r i^2=R i := Real.sq_sqrt (hp i).le
  let L := fderiv ℝ (chargeMap s h) z n
  let P := l 1*p 1*L.1+l 2*p 2*L.2
  let Q := l 1*q 1*L.1+l 2*q 2*L.2
  have E := charge_differential s h z.1 z.2 a k hh hl
  have d : L = _ := chargeMap_fderiv s h z.1 z.2 a k hl (fun i => (hp i).ne')
  have P' : P=3*(∑ i, l i/R i*p i*(p i*a+q i*k))-a := by dsimp only [P]; rw [d]; exact E.1
  have Q' : Q=3*(∑ i, l i/R i*q i*(p i*a+q i*k))-k := by dsimp only [Q]; rw [d]; exact E.2
  have first (i : Fin 3) :
      l i*x i^2=a*(l i/R i*p i*(p i*a+q i*k))+k*(l i/R i*q i*(p i*a+q i*k)) := by
    change l i*((-a*p i-k*q i)/r i)^2=_
    rw [← sq]; field_simp [nr i]; ring
  have mixed (i : Fin 3) :
      l i*x i*y i= -k*(l i/R i*p i*(p i*a+q i*k))+a*(l i/R i*q i*(p i*a+q i*k)) := by
    change l i*((-a*p i-k*q i)/r i)*((k*p i-a*q i)/r i)=_
    rw [← sq]; field_simp [nr i]; ring
  have e1 : 3*(∑ i,l i*x i^2)-1=a*P+k*Q := by
    simp only [Fin.sum_univ_three] at P' Q' ⊢
    linear_combination 3*(first 0+first 1+first 2)-a*P'-k*Q'+un
  have e2 : 3*(∑ i,l i*x i*y i)= -k*P+a*Q := by
    simp only [Fin.sum_univ_three] at P' Q' ⊢
    linear_combination 3*(mixed 0+mixed 1+mixed 2)+k*P'-a*Q'
  change L=0 ↔ (∑ i,l i*x i^2)=1/3 ∧ (∑ i,l i*x i*y i)=0
  constructor
  · intro zero
    simp [P,Q,zero] at e1 e2
    exact ⟨by linarith only [e1],by linarith only [e2]⟩
  · rintro ⟨xx,xy⟩
    rw [xx] at e1; rw [xy] at e2
    have pz : P=0 := by linear_combination -a*e1+k*e2-P*un
    have qz : Q=0 := by linear_combination -k*e1-a*e2-Q*un
    have det : l 1*p 1*(l 2*q 2)-l 2*p 2*(l 1*q 1) ≠ 0 :=
      (charge_matrix_det s h z.1 z.2 hh).trans_ne (mul_ne_zero (mul_ne_zero (mul_ne_zero hh (hl 0)) (hl 1)) (hl 2))
    dsimp only [P] at pz; dsimp only [Q] at qz
    apply Prod.ext
    · change L.1=0
      apply (mul_eq_zero_iff_left det).mp
      linear_combination l 2*q 2*pz-l 2*p 2*qz
    · change L.2=0
      apply (mul_eq_zero_iff_left det).mp
      linear_combination l 1*p 1*qz-l 1*q 1*pz

/-- In a unit kernel direction the spatial derivative of the determinant is
the cubic null jet, with the barycentric charges prescribed at the base. -/
theorem det_line_deriv (s h : ℝ) (z n : Plane) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (un : n.1^2+n.2^2=1)
    (null : fderiv ℝ (chargeMap s h) z n=0) :
    HasDerivAt (fun t => detH s h (z.1+t*n.1) (z.2+t*n.2))
      (cubicNull (coordinates s h z.1 z.2) (radiusAt s h z) (X s h (z,n))) 0 := by
  let l := coordinates s h z.1 z.2
  let r := radiusAt s h z
  let x := X s h (z,n)
  let y := Y s h (z,n)
  let b := coordVelocity s h n.1 n.2
  let p := siteDx s z.1
  let q := siteDy h z.2
  have P (i : Fin 3) : p i= -dx s z.1 i := by fin_cases i <;> dsimp [p,dx,siteDx] <;> ring
  have Q (i : Fin 3) : q i= -dy h z.2 i := by fin_cases i <;> dsimp [q,dy,siteDy] <;> ring
  have hr i := radii_pos_of_chamber s h z hh hl i
  have nr i : r i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have rad i : r i^2=p i^2+q i^2 := (Real.sq_sqrt (hr i).le).trans (by rw [P,Q,radii_eq]; ring)
  have rx i : r i*x i=n.1*p i+n.2*q i := by
    change r i*((-n.1*dx s z.1 i-n.2*dy h z.2 i)/r i)=_
    rw [P,Q]; field_simp [nr i]; ring
  have ry i : r i*y i= -n.2*p i+n.1*q i := by
    change r i*((n.2*dx s z.1 i-n.1*dy h z.2 i)/r i)=_
    rw [P,Q]; field_simp [nr i]; ring
  have unit i : x i^2+y i^2=1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (nr i))
    linear_combination (norm := ring) (r i*x i+n.1*p i+n.2*q i)*rx i+
      (r i*y i-n.2*p i+n.1*q i)*ry i+(p i^2+q i^2)*un-rad i
  obtain ⟨xx,xy⟩ := (kernel_iff s h z n hh hl un).mp null
  change ∑ i,l i*x i^2=1/3 at xx
  change ∑ i,l i*x i*y i=0 at xy
  obtain ⟨mass,_,_,db⟩ := bary_moments s h z hh
  change ∑ i,l i=1 at mass
  have yy : ∑ i,l i*y i^2=2/3 := by
    simp only [Fin.sum_univ_three] at xx mass ⊢
    linear_combination l 0*unit 0+l 1*unit 1+l 2*unit 2+mass-xx
  have lc := lineDet_deriv l b r x y 1 0 nr unit xx xy yy
  have lv i : logVelocity s h z.1 z.2 n.1 n.2 i= b i/l i-3*x i/r i := by
    change b i/l i+3*(dx s z.1 i*n.1+dy h z.2 i*n.2)/radii s h z.1 z.2 i=_
    have sR : r i^2=radii s h z.1 z.2 i := Real.sq_sqrt (hr i).le
    rw [← sR]
    field_simp [nr i,show l i ≠ 0 from hl i]
    have eq := rx i
    rw [P,Q] at eq
    linear_combination 3*l i*eq
  let c := logVelocity s h z.1 z.2 n.1 n.2 0
  have same (i : Fin 3) : logVelocity s h z.1 z.2 n.1 n.2 i=c := by
    have e := (chargeMap_fderiv s h z.1 z.2 n.1 n.2 hl (fun i => (hr i).ne')).symm.trans null
    fin_cases i
    · rfl
    · exact sub_eq_zero.mp (congrArg Prod.fst e)
    · exact sub_eq_zero.mp (congrArg Prod.snd e)
  have vel i : b i=l i*(c+3*x i/r i) := by
    have e := (lv i).symm.trans (same i)
    field_simp [show l i ≠ 0 from hl i,nr i] at e ⊢
    linear_combination e
  have jet : nullDerivative l b r x y 1 0=cubicNull l r x := by
    have bm := (db n.1 n.2).1
    change ∑ i,b i=0 at bm
    simp only [nullDerivative,cubicNull,Fin.sum_univ_three] at xx mass bm ⊢
    simp only [vel] at bm ⊢
    linear_combination 3*c*xx-c*mass+bm
  rw [jet] at lc
  convert! lc using 1
  funext t
  change chartHessian s h (z.1+t*n.1) (z.2+t*n.2)=_
  rw [chartHessian_eq]
  let pt i := p i-t*n.1
  let qt i := q i-t*n.2
  have sp : siteDx s (z.1+t*n.1)=pt := by funext i; fin_cases i <;> dsimp [siteDx,pt,p] <;> ring
  have sq : siteDy h (z.2+t*n.2)=qt := by funext i; fin_cases i <;> dsimp [siteDy,qt,q] <;> ring
  have wt : MaxwellCusp.Spatial.bary s h (z.1+t*n.1) (z.2+t*n.2)=(fun i => l i+t*b i) :=
    funext (coordinates_line s h z.1 z.2 n.1 n.2 t)
  unfold normalizedDet
  rw [wt,sp,sq,← cartDet_rotation _ _ _ n.1 n.2 un]
  have r1 : rot pt qt n.1 n.2=(fun i => r i*x i-t*1) := by
    funext i; dsimp [rot,pt,qt]; rw [rx]; linear_combination -t*un
  have r2 : rot pt qt (-n.2) n.1=(fun i => r i*y i-t*0) := by
    funext i; dsimp [rot,pt,qt]; rw [ry]; ring
  rw [r1,r2]
  have xx' (w a b : ℝ) : w/(a^2+b^2)*a*a=w*a^2/(a^2+b^2) := by ring
  have yy' (w a b : ℝ) : w/(a^2+b^2)*b*b=w*b^2/(b^2+a^2) := by rw [add_comm (b^2)]; ring
  have xy' (w a b : ℝ) : w/(a^2+b^2)*a*b=w*a*b/(a^2+b^2) := by ring
  simp only [cartDet,gramDet,gram,lineDet,lineXX,lineXY,summand,xx',yy',xy']

end MaxwellCausticExtremum.Chart.Cusp

end
end

section

noncomputable section
open Set Filter Topology
namespace MaxwellCausticExtremum.Chart

private theorem unit_kernel (L : Plane →L[ℝ] Plane)
    (det : (L (1,0)).1*(L (0,1)).2-(L (0,1)).1*(L (1,0)).2=0) :
    ∃ n : Plane, n.1^2+n.2^2=1 ∧ L n=0 := by
  let u := L (1,0)
  let v := L (0,1)
  change u.1*v.2-v.1*u.2=0 at det
  by_cases z : u=0
  · exact ⟨(1,0),by norm_num,z⟩
  have make (a b : ℝ) (ne : a ≠ 0) (eq : L (b,-a)=0) : ∃ n : Plane, n.1^2+n.2^2=1 ∧ L n=0 := by
    let R := Real.sqrt (b^2+a^2)
    have pos : 0 < b^2+a^2 := by positivity
    have nz : R ≠ 0 := (Real.sqrt_pos.mpr pos).ne'
    refine ⟨R⁻¹ • (b,-a),?_,by rw [map_smul,eq,smul_zero]⟩
    dsimp; field_simp [nz]; linarith only [show R^2=b^2+a^2 from Real.sq_sqrt pos.le]
  have decomp (a b : ℝ) : L (b,-a)=b • u-a • v := by
    rw [← L.map_smul b (1,0),← L.map_smul a (0,1),← map_sub]; simp
  by_cases a : u.1=0
  · apply make u.2 v.2 (fun h => z (Prod.ext a h))
    rw [decomp]; apply Prod.ext <;> dsimp
    · linear_combination det
    · ring
  · apply make u.1 v.1 a
    rw [decomp]; apply Prod.ext <;> dsimp
    · ring
    · linear_combination -det

private def raw (s h : ℝ) (w : Plane) (i : Fin 3) :=
  coordinates s h w.1 w.2 i*Real.sqrt (radii s h w.1 w.2 i)^3

private theorem raw_cont (s h : ℝ) (i : Fin 3) : Continuous (fun w : Plane => raw s h w i) := by
  fin_cases i <;> dsimp [raw,coordinates,radii] <;> fun_prop

private theorem same_raw (s h : ℝ) (sign : Triple) (p q : Plane) (hh : h ≠ 0)
    (sp : ∀ i, 0<sign i*coordinates s h p.1 p.2 i) (sq : ∀ i, 0<sign i*coordinates s h q.1 q.2 i)
    (eq : chargeMap s h p=chargeMap s h q) :
    ∀ i, raw s h p i/raw s h p 0=raw s h q i/raw s h q 0 := by
  have good (z : Plane) (sz : ∀ i, 0<sign i*coordinates s h z.1 z.2 i) (i : Fin 3) :
      raw s h z i ≠ 0 ∧ 0<sign i*raw s h z i ∧ logCharge s h z.1 z.2 i=Real.log (raw s h z i) := by
    have hl j := right_ne_zero_of_mul (sz j).ne'
    have hr := radii_pos_of_chamber s h z hh hl i
    refine ⟨mul_ne_zero (hl i) (pow_ne_zero _ (Real.sqrt_pos.mpr hr).ne'),?_,?_⟩
    · unfold raw; rw [← mul_assoc]; exact mul_pos (sz i) (pow_pos (Real.sqrt_pos.mpr hr) _)
    · rw [logCharge_eq _ _ _ _ _ (hl i) hr,Real.log_abs]; rfl
  have logeq (i : Fin 3) : logCharge s h p.1 p.2 i-logCharge s h p.1 p.2 0=
      logCharge s h q.1 q.2 i-logCharge s h q.1 q.2 0 := by
    fin_cases i
    · simp
    · exact congrArg Prod.fst eq
    · exact congrArg Prod.snd eq
  have pos (i : Fin 3) : 0<raw s h p i*raw s h q i := by
    rcases mul_pos_iff.mp (good p sp i).2.1 with ⟨hs,hp⟩|⟨hs,hp⟩
    · exact mul_pos hp (pos_of_mul_pos_right (good q sq i).2.1 hs.le)
    · exact mul_pos_of_neg_of_neg hp (neg_of_mul_pos_right (good q sq i).2.1 hs.le)
  intro i
  have le := logeq i
  rw [(good p sp i).2.2,(good p sp 0).2.2,(good q sq i).2.2,(good q sq 0).2.2,
    ← Real.log_div (good p sp i).1 (good p sp 0).1,← Real.log_div (good q sq i).1 (good q sq 0).1] at le
  have ae := congrArg Real.exp le
  rw [Real.exp_log_eq_abs (div_ne_zero (good p sp i).1 (good p sp 0).1),
    Real.exp_log_eq_abs (div_ne_zero (good q sq i).1 (good q sq 0).1)] at ae
  rcases abs_eq_abs.mp ae with e|e
  · exact e
  · have nz := div_pos (pos i) (pos 0)
    rw [← div_mul_div_comm,e] at nz
    nlinarith only [nz,sq_nonneg (raw s h q i/raw s h q 0)]

namespace Local
open ForceSection
open MaxwellCusp.Spatial (rot gram gramDet cartDet chartHessian_eq normalizedDet)

def sites (s h : ℝ) (z n : Plane) : Sites where
  a i := -n.1*dx s z.1 i-n.2*dy h z.2 i
  b i := n.2*dx s z.1 i-n.1*dy h z.2 i

def state (s h : ℝ) (z n w : Plane) : P :=
  ((fun i => (raw s h z 0/raw s h w 0)*raw s h w i,n.1*(w.1-z.1)+n.2*(w.2-z.2)),
   -n.2*(w.1-z.1)+n.1*(w.2-z.2))

theorem state_cont (s h : ℝ) (z n : Plane) (nz : raw s h z 0 ≠ 0) :
    ContinuousAt (state s h z n) z := by
  unfold state
  have c i := (raw_cont s h i).continuousAt (x := z)
  fun_prop (disch := exact nz)

theorem state_charges (s h : ℝ) (z n p q : Plane) (hh : h ≠ 0) (sign : Triple)
    (sp : ∀ i, 0<sign i*coordinates s h p.1 p.2 i) (sq : ∀ i, 0<sign i*coordinates s h q.1 q.2 i)
    (eq : chargeMap s h p=chargeMap s h q) : (state s h z n p).1.1=(state s h z n q).1.1 := by
  funext i
  have e := same_raw s h sign p q hh sp sq eq i
  dsimp [state]
  linear_combination raw s h z 0*e

theorem state_inj (s h : ℝ) (z n : Plane) (un : n.1^2+n.2^2=1) : Function.Injective (state s h z n) := by
  intro p q eq
  have a := congrArg (fun v : P => v.1.2) eq
  have b := congrArg Prod.snd eq
  dsimp [state] at a b
  apply Prod.ext
  · linear_combination n.1*a-n.2*b-(p.1-q.1)*un
  · linear_combination n.2*a+n.1*b-(p.2-q.2)*un

private theorem displaced (s h : ℝ) (z n w : Plane) (i : Fin 3) :
    let S := sites s h z n
    let W := state s h z n w
    S.X W i= -n.1*dx s w.1 i-n.2*dy h w.2 i ∧ S.Y W i=n.2*dx s w.1 i-n.1*dy h w.2 i := by
  dsimp [Sites.X,Sites.Y,sites,state,dx,dy]; constructor <;> ring

theorem prescribed_force (s h : ℝ) (hh : h ≠ 0) (z n w : Plane) (un : n.1^2+n.2^2=1)
    (hl : ∀ i, coordinates s h w.1 w.2 i ≠ 0) :
    let S := sites s h z n
    let W := state s h z n w
    S.A W=0 ∧ S.B W=0 ∧
      S.Pxx W*S.N W-(S.M W)^2=(raw s h z 0/raw s h w 0)^2*detH s h w.1 w.2 := by
  let S := sites s h z n
  let W := state s h z n w
  let l := coordinates s h w.1 w.2
  let r i := Real.sqrt (radii s h w.1 w.2 i)
  let k := raw s h z 0/raw s h w 0
  let p := MaxwellCusp.Spatial.siteDx s w.1
  let q := MaxwellCusp.Spatial.siteDy h w.2
  have ep i : p i= -dx s w.1 i := by fin_cases i <;> dsimp [p,dx,MaxwellCusp.Spatial.siteDx] <;> ring
  have eq i : q i= -dy h w.2 i := by fin_cases i <;> dsimp [q,dy,MaxwellCusp.Spatial.siteDy] <;> ring
  have X i : S.X W i=rot p q n.1 n.2 i := by
    rw [(displaced s h z n w i).1]; dsimp [rot]; rw [ep,eq]; ring
  have Y i : S.Y W i=rot p q (-n.2) n.1 i := by
    rw [(displaced s h z n w i).2]; dsimp [rot]; rw [ep,eq]; ring
  have sq i : r i^2=p i^2+q i^2 := (Real.sq_sqrt (radii_pos_of_chamber _ _ w hh hl i).le).trans
    (by rw [ep,eq,radii_eq]; ring)
  have nr i : 0<r i := Real.sqrt_pos.mpr (radii_pos_of_chamber _ _ w hh hl i)
  have R i : S.R W i=r i := by
    unfold Sites.R; rw [X,Y]
    have e : (rot p q n.1 n.2 i)^2+(rot p q (-n.2) n.1 i)^2=(r i)^2 := by
      dsimp [rot]; linear_combination (p i^2+q i^2)*un-sq i
    rw [e,Real.sqrt_sq (nr i).le]
  have sum' (f g : Fin 3 → ℝ) (h : ∀ i, r i^3*f i=g i) :
      Sites.sum W f=k*∑ i,l i*g i := by
    unfold Sites.sum; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro i _
    change (k*(l i*r i^3))*f i=_
    linear_combination k*l i*h i
  obtain ⟨mass,bx,by',_⟩ := bary_moments s h w hh
  change ∑ i,l i=1 at mass
  have force (f : Fin 3 → ℝ) (U V : ℝ) (hf : ∀ i, f i=U*(-dx s w.1 i)+V*(-dy h w.2 i)) :
      Sites.sum W (fun i => fy (f i) (S.R W i))=0 := by
    rw [sum' _ f (by intro i; rw [R]; dsimp [fy]; field_simp [(nr i).ne'])]
    apply mul_eq_zero_of_right
    change ∑ i,l i*(-dx s w.1 i)=0 at bx
    change ∑ i,l i*(-dy h w.2 i)=0 at by'
    simp only [Fin.sum_univ_three,hf] at bx by' ⊢
    linear_combination U*bx+V*by'
  let wg i := l i/(p i^2+q i^2)
  have diag (f : Triple) :
      Sites.sum W (fun i => yy (f i) (S.R W i))=k*(3*gram wg f f-1) := by
    rw [sum' _ (fun i => 3*f i*f i/(r i)^2-1) (by intro i; rw [R]; dsimp [yy]; field_simp [(nr i).ne'])]
    congr 1
    dsimp [gram,wg]; simp only [Fin.sum_univ_three,← sq] at mass ⊢
    linear_combination -mass
  have cross : S.M W=k*(3*gram wg (S.X W) (S.Y W)) := by
    unfold Sites.M
    rw [sum' _ (fun i => 3*S.X W i*S.Y W i/(r i)^2) (by intro i; rw [R]; dsimp [hv]; field_simp [(nr i).ne']; ring)]
    dsimp [gram,wg]; simp only [Fin.sum_univ_three,← sq]; ring
  refine ⟨force _ n.1 n.2 (fun i => by rw [X]; dsimp [rot]; rw [ep,eq]),
    force _ (-n.2) n.1 (fun i => by rw [Y]; dsimp [rot]; rw [ep,eq]),?_⟩
  change S.Pxx W*S.N W-(S.M W)^2=k^2*detH s h w.1 w.2
  change _=k^2*MaxwellCusp.Spatial.chartHessian s h w.1 w.2
  rw [chartHessian_eq]
  change _=k^2*gramDet wg p q
  rw [← MaxwellCusp.Spatial.gramDet_rotation wg p q n.1 n.2 un,← funext X,← funext Y,
    Sites.Pxx,Sites.N,diag,diag,cross]
  dsimp [gramDet]; ring

end Local
end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum.Chart

/-- At every boundary point the charge map is one-to-one on a relative
neighborhood in the closed positive sheet. -/
theorem boundary_local (s h : ℝ) (hh : 0<h) (sign : Triple) (z : Plane)
    (hz : ∀ i, 0<sign i*coordinates s h z.1 z.2 i) (crit : detH s h z.1 z.2=0) :
    ∃ U ∈ 𝓝 z, InjOn (chargeMap s h) (U ∩ {p : Plane |
      (∀ i, 0<sign i*coordinates s h p.1 p.2 i) ∧ 0≤detH s h p.1 p.2}) := by
  let l := coordinates s h z.1 z.2
  let r i := Real.sqrt (radii s h z.1 z.2 i)
  have hl i : l i ≠ 0 := right_ne_zero_of_mul (hz i).ne'
  have hp i := radii_pos_of_chamber s h z hh.ne' hl i
  have hr i : 0<r i := Real.sqrt_pos.mpr (hp i)
  have j := (critical_iff s h z.1 z.2 hh.ne' hl (fun i => (hp i).ne')).mpr crit
  obtain ⟨n,un,kn⟩ := unit_kernel (fderiv ℝ (chargeMap s h) z) j
  let S := Local.sites s h z n
  let p := Local.state s h z n
  let x := Cusp.X s h (z,n)
  let y := Cusp.Y s h (z,n)
  let base : ForceSection.P := ((fun i => l i*r i^3,0),0)
  have nz0 : raw s h z 0 ≠ 0 := mul_ne_zero (hl 0) (pow_ne_zero _ (hr 0).ne')
  have p0 : p z=base := by simp [p,base,Local.state,nz0]; rfl
  have ax i : S.a i=r i*x i := by
    change _=r i*(S.a i/r i)
    field_simp [(hr i).ne']
  have ay i : S.b i=r i*y i := by
    change _=r i*(S.b i/r i)
    field_simp [(hr i).ne']
  have rad i : r i^2=dx s z.1 i^2+dy h z.2 i^2 := (Real.sq_sqrt (hp i).le).trans (radii_eq ..)
  have unit i : x i^2+y i^2=1 := by
    change ((S.a i)/r i)^2+((S.b i)/r i)^2=1
    field_simp [(hr i).ne']; dsimp [S,Local.sites]
    linear_combination (dx s z.1 i^2+dy h z.2 i^2)*un-rad i
  have sep (i j : Fin 3) (ne : i≠j) : MaxwellCusp.Spatial.minor x y i j ≠ 0 := by
    intro zero
    apply displacement_separation s h z hh.ne' hl i j ne
    change (S.a i/r i)*(S.b j/r j)-(S.b i/r i)*(S.a j/r j)=0 at zero
    field_simp [(hr i).ne',(hr j).ne'] at zero
    dsimp [S,Local.sites] at zero
    linear_combination zero-(dx s z.1 i*dy h z.2 j-dy h z.2 i*dx s z.1 j)*un
  obtain ⟨mass,mx,my,_⟩ := bary_moments s h z hh.ne'
  change ∑ i,l i=1 at mass
  obtain ⟨xx,xy⟩ := (Cusp.kernel_iff s h z n hh.ne' hl un).mp kn
  change ∑ i,l i*x i^2=1/3 at xx
  change ∑ i,l i*x i*y i=0 at xy
  have yy : ∑ i,l i*y i^2=2/3 := by
    simp only [Fin.sum_univ_three] at mass xx ⊢
    linear_combination l 0*unit 0+l 1*unit 1+l 2*unit 2+mass-xx
  have force : (∑ i,l i*r i*x i)=0 ∧ (∑ i,l i*r i*y i)=0 := by
    simp only [Fin.sum_univ_three,mul_assoc,← ax,← ay] at mx my ⊢
    dsimp only [S,Local.sites,l] at *
    exact ⟨by linear_combination n.1*mx+n.2*my,by linear_combination -n.2*mx+n.1*my⟩
  obtain ⟨κ,_,scale⟩ := MaxwellCusp.Spatial.common_scale l r x y hl (fun i => (hr i).ne') sep xx xy yy force.1 force.2
  obtain ⟨Rb,Nb,Eb,Jb⟩ := S.base_jets l r x y hr unit ax ay mass xx xy yy
  have bzero : S.B base=0 := p0 ▸ (Local.prescribed_force s h hh.ne' z n z un hl).2.1
  have turn : S.E base ≠ 0 ∨ S.J base < 0 := by
    by_cases fold : MaxwellCusp.Spatial.cubicNull l r x=0
    · right
      rw [show S.J base=_ from Jb]
      exact MaxwellCusp.Spatial.cusp_quartic_negative l r x y κ (fun i => (hr i).ne') unit scale sep xx xy yy fold
    · exact Or.inl (Eb.trans_ne fold)
  have hR (i : Fin 3) : 0<S.R base i := (Rb i).trans_gt (hr i)
  obtain ⟨U,hU,inj⟩ := S.unique_near base hR bzero Nb turn
  have cP : Tendsto p (𝓝 z) (𝓝 base) := p0 ▸ Local.state_cont s h z n nz0
  have np : 0<S.N base := Nb.trans_gt zero_lt_one
  have openN : ∀ᶠ w in 𝓝 base, 0<S.N w := continuousAt_const.eventually_lt (S.base_smooth base hR).2.2.2.continuousAt np
  have near : ∀ᶠ w in 𝓝 z, p w ∈ U ∧ 0<S.N (p w) := cP (inter_mem hU openN)
  refine ⟨_,near,?_⟩
  rintro v ⟨⟨vU,vN⟩,sv,vJ⟩ w ⟨⟨wU,wN⟩,sw,wJ⟩ eq
  have pr (u : Plane) (su : ∀ i, 0<sign i*coordinates s h u.1 u.2 i)
      (nU : 0<S.N (p u)) (ju : 0≤detH s h u.1 u.2) : S.A (p u)=0 ∧ S.B (p u)=0 ∧ 0≤S.D (p u) := by
    obtain ⟨za,zb,val⟩ := Local.prescribed_force s h hh.ne' z n u un (fun i => right_ne_zero_of_mul (su i).ne')
    have id := S.determinant (p u) nU.ne'
    refine ⟨za,zb,nonneg_of_mul_nonneg_left ?_ nU⟩
    rw [id,val]
    exact mul_nonneg (sq_nonneg _) ju
  obtain ⟨Av,Bv,Dv⟩ := pr v sv vN vJ
  obtain ⟨Aw,Bw,Dw⟩ := pr w sw wN wJ
  exact Local.state_inj s h z n un (inj _ vU _ wU
    (Local.state_charges s h z n v w hh.ne' sign sv sw eq) Bv Bw Dv Dw (Av.trans Aw.symm))

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Equilateral

def radius (x y : ℝ) := 3*x^2+y^2

def left (x y : ℝ) := radius (x-1) (y-1)

def right (x y : ℝ) := radius (x-1) (y+1)

/-- The radial-angular and angular-angular entries of the Hessian,
after clearing nonzero factors on the seven sign chambers. -/
def normal (x y : ℝ) : Prop :=
  (3*x+y-radius x y)*right x y = (3*x-y-radius x y)*left x y ∧
  9*((x+y)*(x-y)^2*right x y+(x-y)*(x+y)^2*left x y) =
    2*radius x y*left x y*right x y

theorem normal_iff (x y : ℝ) (hr : 0 < radius x y) (hl : 0 < left x y) (hv : 0 < right x y) :
    normal x y ↔ (y = 0 ∧ 3*x^2-9*x+4=0) ∨ (radius x y=4 ∧ 3*x+1=0) := by
  let t := 9*((x+y)*(x-y)^2*right x y+(x-y)*(x+y)^2*left x y) -
    2*radius x y*left x y*right x y
  have r : (3*x+y-radius x y)*right x y - (3*x-y-radius x y)*left x y =
      2*y*(4-radius x y) := by unfold left right radius; ring
  have off (h : radius x y=4) : t = 4*(3*x+1)*left x y*right x y := by
    dsimp [t,left,right,radius] at *
    linear_combination -2*(9*x^4-27*x^3+6*x^2*y^2+24*x^2+3*x*y^2+y^4-8*y^2-8)*h
  have axis (h : y=0) : t = -2*radius x y*left x y*(3*x^2-9*x+4) := by
    subst y
    dsimp [t,left,right,radius]
    ring
  unfold normal
  rw [← sub_eq_zero, r]
  constructor
  · rintro ⟨h₁,h₂⟩
    have ht : t=0 := sub_eq_zero.mpr h₂
    rcases mul_eq_zero.mp h₁ with h|h
    · have hy : y=0 := by linarith
      rw [axis hy] at ht
      exact Or.inl ⟨hy,(mul_eq_zero.mp ht).resolve_left (by positivity)⟩
    · have hh : radius x y=4 := by linarith
      rw [off hh] at ht
      have hh' := (mul_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hv.ne')).resolve_right hl.ne'
      exact Or.inr ⟨hh,by linarith⟩
  · rintro (⟨hy,h⟩|⟨hr',h⟩)
    · refine ⟨by rw [hy]; ring,sub_eq_zero.mp ?_⟩
      change t=0
      rw [axis hy,h,mul_zero]
    · refine ⟨by rw [hr']; ring,sub_eq_zero.mp ?_⟩
      change t=0
      rw [off hr',h]
      ring

theorem four_points (x y : ℝ) (hr : 0 < radius x y) (hl : 0 < left x y)
    (hv : 0 < right x y) :
    normal x y ↔
      (y=0 ∧ (x=(9-Real.sqrt 33)/6 ∨ x=(9+Real.sqrt 33)/6)) ∨
      (x= -(1/3 : ℝ) ∧ (y= -(Real.sqrt (11/3)) ∨ y=Real.sqrt (11/3))) := by
  rw [normal_iff x y hr hl hv]
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 11/3 by norm_num)
  have ax : 3*x^2-9*x+4=0 ↔ x=(9-Real.sqrt 33)/6 ∨ x=(9+Real.sqrt 33)/6 := by
    constructor
    · intro h
      have h' : (6*x-9+Real.sqrt 33)*(6*x-9-Real.sqrt 33)=0 := by nlinarith
      rcases mul_eq_zero.mp h' with ha|ha
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    · rintro (rfl|rfl) <;> nlinarith
  rw [ax]
  apply or_congr_right
  unfold radius
  constructor
  · rintro ⟨h,k⟩
    have hx : x= -(1/3 : ℝ) := by linarith
    subst x
    have hz : (y+Real.sqrt (11/3))*(y-Real.sqrt (11/3))=0 := by nlinarith
    rcases mul_eq_zero.mp hz with h|h
    · exact ⟨rfl,Or.inl (by linarith)⟩
    · exact ⟨rfl,Or.inr (by linarith)⟩
  · rintro ⟨rfl,h|h⟩ <;> subst y <;> constructor <;> nlinarith

/-- The three weights at (x,y), with the central site labeled zero. -/
def weights (x y : ℝ) : Fin 3 → ℝ := ![1-x,(x+y)/2,(x-y)/2]

/-- Bilinear Hessian in the chart with metric diag(3,1). -/
def H (x y : ℝ) (u v : ℝ × ℝ) : ℝ :=
  let d : Fin 3 → ℝ × ℝ := ![(x,y),(x-1,y-1),(x-1,y+1)]
  let dot (b c : ℝ × ℝ) := 3*b.1*c.1+b.2*c.2
  3*(∑ i, weights x y i*(dot (d i) u)*(dot (d i) v)/(dot (d i) (d i))) - dot u v

def angularKernel (x y : ℝ) : Prop :=
  H x y (x,y) (-y,3*x) = 0 ∧ H x y (-y,3*x) (-y,3*x) = 0

theorem angularKernel_iff_normal {x y : ℝ} (hr : radius x y ≠ 0) (hl : left x y ≠ 0)
    (hw : right x y ≠ 0) (hp : x+y ≠ 0) (hm : x-y ≠ 0) :
    angularKernel x y ↔ normal x y := by
  let R := radius x y
  let U := left x y
  let W := right x y
  have nR : R ≠ 0 := hr
  have nU : U ≠ 0 := hl
  have nW : W ≠ 0 := hw
  have calcH (u v : ℝ × ℝ) : H x y u v =
      3*((1-x)*(3*x*u.1+y*u.2)*(3*x*v.1+y*v.2)/R +
        ((x+y)/2)*(3*(x-1)*u.1+(y-1)*u.2)*(3*(x-1)*v.1+(y-1)*v.2)/U +
        ((x-y)/2)*(3*(x-1)*u.1+(y+1)*u.2)*(3*(x-1)*v.1+(y+1)*v.2)/W) -
        (3*u.1*v.1+u.2*v.2) := by
    simp [H,weights,R,U,W,radius,left,right,Fin.sum_univ_three,pow_two,mul_assoc]
  have e1 : H x y (x,y) (-y,3*x) * (2*U*W) =
      9*(x+y)*(x-y)*((3*x+y-R)*W-(3*x-y-R)*U) := by
    rw [calcH]
    dsimp only [Prod.fst,Prod.snd]
    field_simp [nR,nU,nW]
    dsimp [R,radius]
    ring
  have e2 : H x y (-y,3*x) (-y,3*x) * (2*U*W) =
      3*(9*((x+y)*(x-y)^2*W+(x-y)*(x+y)^2*U)-2*R*U*W) := by
    rw [calcH]
    dsimp only [Prod.fst,Prod.snd]
    field_simp [nR,nU,nW]
    dsimp [R,radius]
    ring
  unfold angularKernel normal
  change (_ ∧ _) ↔ ((3*x+y-R)*W=(3*x-y-R)*U ∧ _=2*R*U*W)
  have hn : 2*U*W ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) nU) nW
  have hc : 9*(x+y)*(x-y) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp) hm
  apply and_congr
  · calc
      _ ↔ H x y (x,y) (-y,3*x)*(2*U*W) = 0 := (mul_eq_zero_iff_right hn).symm
      _ ↔ _ := by rw [e1,mul_eq_zero_iff_left hc,sub_eq_zero]
  · calc
      _ ↔ H x y (-y,3*x) (-y,3*x)*(2*U*W) = 0 := (mul_eq_zero_iff_right hn).symm
      _ ↔ _ := by rw [e2,mul_eq_zero_iff_left (by norm_num : (3:ℝ) ≠ 0),sub_eq_zero]

/-- Positivity masks of the interior and the three edge chambers. -/
def chamber (c : Fin 4) (x y : ℝ) : Prop :=
  match c with
  | 0 => 0 < 1-x ∧ 0 < x+y ∧ 0 < x-y
  | 1 => 1-x < 0 ∧ 0 < x+y ∧ 0 < x-y
  | 2 => 0 < 1-x ∧ x+y < 0 ∧ 0 < x-y
  | 3 => 0 < 1-x ∧ 0 < x+y ∧ x-y < 0

def basePoint : Fin 4 → ℝ × ℝ :=
  ![((9-Real.sqrt 33)/6,0),((9+Real.sqrt 33)/6,0),
    (-(1/3),-Real.sqrt (11/3)),(-(1/3),Real.sqrt (11/3))]

theorem angular_fiber (c : Fin 4) (x y : ℝ) :
    chamber c x y ∧ angularKernel x y ↔ (x,y) = basePoint c := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have ht := Real.sq_sqrt (show (0:ℝ) ≤ 11/3 by norm_num)
  have bs := Real.sqrt_nonneg 33
  have bt := Real.sqrt_nonneg (11/3)
  have b1 : 3 < Real.sqrt 33 := by nlinarith
  have b2 : Real.sqrt 33 < 9 := by nlinarith
  have b3 : 1/3 < Real.sqrt (11/3) := by nlinarith
  have classify (hc : chamber c x y) : angularKernel x y ↔
      (y=0 ∧ (x=(9-Real.sqrt 33)/6 ∨ x=(9+Real.sqrt 33)/6)) ∨
      (x= -(1/3 : ℝ) ∧ (y= -(Real.sqrt (11/3)) ∨ y=Real.sqrt (11/3))) := by
    have nz : 1-x ≠ 0 ∧ x+y ≠ 0 ∧ x-y ≠ 0 := by
      fin_cases c <;> simp [chamber] at hc <;> grind
    have hr : 0 < radius x y := by
      unfold radius
      by_contra! h
      have : x = 0 := by nlinarith [sq_nonneg y]
      have : y = 0 := by nlinarith [sq_nonneg x]
      grind
    have xx : x-1 ≠ 0 := by grind
    have lu : 0 < left x y := by dsimp [left,radius]; positivity
    have rv : 0 < right x y := by dsimp [right,radius]; positivity
    rw [angularKernel_iff_normal hr.ne' lu.ne' rv.ne' nz.2.1 nz.2.2,four_points x y hr lu rv]
  constructor
  · rintro ⟨hc,hk⟩
    rcases (classify hc).mp hk with ⟨rfl,rfl|rfl⟩|⟨rfl,rfl|rfl⟩ <;>
      fin_cases c <;> norm_num [chamber,basePoint] at * <;> linarith
  · intro he
    have ex : x = (basePoint c).1 := congrArg Prod.fst he
    have ey : y = (basePoint c).2 := congrArg Prod.snd he
    subst x
    subst y
    have hc : chamber c (basePoint c).1 (basePoint c).2 := by
      fin_cases c <;> refine ⟨?_,?_,?_⟩ <;> dsimp [basePoint] <;> linarith
    refine ⟨hc,(classify hc).mpr ?_⟩
    fin_cases c <;> first
      | exact Or.inl ⟨rfl,Or.inl rfl⟩
      | exact Or.inl ⟨rfl,Or.inr rfl⟩
      | exact Or.inr ⟨rfl,Or.inl rfl⟩
      | exact Or.inr ⟨rfl,Or.inr rfl⟩

end MaxwellCausticExtremum.Equilateral

namespace MaxwellCausticExtremum.Equilateral

/-- The logarithm of the outer-site charge ratio, written as a sum of logarithms
on a sign chamber. Common metric-scale and barycentric factors cancel. -/
def outerLog (p : ℝ × ℝ) : ℝ :=
  Real.log (p.1-p.2) - Real.log (p.1+p.2) +
    (3/2)*(Real.log (right p.1 p.2)-Real.log (left p.1 p.2))

theorem outerLog_fderiv (x y : ℝ) (u : ℝ × ℝ) (hp : x+y ≠ 0) (hm : x-y ≠ 0)
    (hU : left x y ≠ 0) (hW : right x y ≠ 0) :
    fderiv ℝ outerLog (x,y) u =
      (u.1-u.2)/(x-y) - (u.1+u.2)/(x+y) +
       3*((3*(x-1)*u.1+(y+1)*u.2)/right x y-(3*(x-1)*u.1+(y-1)*u.2)/left x y) := by
  have dx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (x,y))
  have dy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (x,y))
  have dX := (((dx.sub_const 1).pow 2).const_mul 3)
  have dU := dX.add ((dy.sub_const 1).pow 2)
  have dW := dX.add ((dy.add_const 1).pow 2)
  have df := (((dx.sub dy).log hm).sub ((dx.add dy).log hp)).add
    (((dW.log hW).sub (dU.log hU)).const_mul (3/2:ℝ))
  have eq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L u) df.fderiv
  change fderiv ℝ outerLog (x,y) u = _ at eq
  rw [eq]
  simp [right,left,radius,div_eq_mul_inv]
  ring

theorem angular_derivative (x y : ℝ) (u : ℝ × ℝ) (hp : x+y ≠ 0) (hm : x-y ≠ 0)
    (hU : left x y ≠ 0) (hW : right x y ≠ 0) :
    H x y (-y,3*x) u = ((3:ℝ)/2)*(x+y)*(x-y)*fderiv ℝ outerLog (x,y) u := by
  rw [outerLog_fderiv x y u hp hm hU hW]
  simp only [H,weights,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  change 3*((1-x)*(3*x*(-y)+y*(3*x))*(3*x*u.1+y*u.2)/(3*x*x+y*y) +
    ((x+y)/2)*(3*(x-1)*(-y)+(y-1)*(3*x))*(3*(x-1)*u.1+(y-1)*u.2)/
      (3*(x-1)*(x-1)+(y-1)*(y-1)) +
    ((x-y)/2)*(3*(x-1)*(-y)+(y+1)*(3*x))*(3*(x-1)*u.1+(y+1)*u.2)/
      (3*(x-1)*(x-1)+(y+1)*(y+1))) - (3*(-y)*u.1+(3*x)*u.2) = _
  simp only [radius,left,right,pow_two,mul_assoc] at *
  field_simp [hU,hW,hp,hm]
  ring

theorem outerLog_critical_iff (x y : ℝ) (hp : x+y ≠ 0) (hm : x-y ≠ 0)
    (hR : radius x y ≠ 0) (hU : left x y ≠ 0) (hW : right x y ≠ 0) :
    fderiv ℝ outerLog (x,y) = 0 ↔ angularKernel x y := by
  let D := fderiv ℝ outerLog (x,y)
  have q := angular_derivative x y
  have hs (a b : ℝ × ℝ) : H x y a b = H x y b a := by
    dsimp [H]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    · ring
  have k : (3/2:ℝ)*(x+y)*(x-y) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hp) hm
  unfold angularKernel
  rw [hs (x,y) (-y,3*x),q (x,y) hp hm hU hW,q (-y,3*x) hp hm hU hW,
    mul_eq_zero_iff_left k,mul_eq_zero_iff_left k]
  constructor
  · rintro he
    simp [he]
  · rintro ⟨da,db⟩
    change D = 0
    apply ContinuousLinearMap.ext
    intro u
    have de : u = ((3*x*u.1+y*u.2)/radius x y) • (x,y) +
        ((x*u.2-y*u.1)/radius x y) • (-y,3*x) := by
      apply Prod.ext <;> simp [radius] at hR ⊢ <;> field_simp [hR] <;> ring
    change D u = 0
    rw [de,map_add,map_smul,map_smul,(show D (x,y) = 0 from da),(show D (-y,3*x) = 0 from db)]
    simp

end MaxwellCausticExtremum.Equilateral

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Chart

open Equilateral

private def baseHeight := Real.sqrt 3/2
private def embed (p : Plane) : Plane := ((3*p.1+p.2)/4,Real.sqrt 3*(p.1-p.2)/4)

private theorem hsqrt : Real.sqrt 3^2=3 := Real.sq_sqrt (by norm_num)
private theorem height_ne : baseHeight ≠ 0 := by unfold baseHeight; positivity

private theorem onWeights (p : Plane) :
    coordinates (1/2) baseHeight (embed p).1 (embed p).2 = weights p.1 p.2 := by
  funext i
  fin_cases i <;> dsimp [coordinates,weights,embed,baseHeight] <;>
    field_simp [show Real.sqrt 3 ≠ 0 by positivity] <;> ring

private theorem onRadii (p : Plane) :
    radii (1/2) baseHeight (embed p).1 (embed p).2 =
      ![radius p.1 p.2/4,left p.1 p.2/4,right p.1 p.2/4] := by
  funext i
  fin_cases i <;> dsimp [radii,radius,left,right,embed,baseHeight] <;>
    ring_nf <;> rw [hsqrt] <;> ring

def baseCovector : Triple := ![0,-1,1]

def chamberSigns (c : Fin 4) : Triple := ![![1,1,1],![-1,1,1],![1,-1,1],![1,1,-1]] c

private theorem signed_chamber (c : Fin 4) (p : Plane) :
    (∀ i, 0 < chamberSigns c i*coordinates (1/2) baseHeight (embed p).1 (embed p).2 i) ↔
      chamber c p.1 p.2 := by
  rw [onWeights]
  fin_cases c <;> simp [chamberSigns,weights,chamber,Fin.forall_fin_succ] <;> grind

private theorem embed_surj : Function.Surjective embed := by
  rintro ⟨x,y⟩
  refine ⟨(x+y/Real.sqrt 3,x-3*y/Real.sqrt 3),?_⟩
  apply Prod.ext <;> dsimp [embed] <;> field_simp [show Real.sqrt 3 ≠ 0 by positivity] <;> ring

private theorem slope_base (p w : Plane)
    (hp : p.1+p.2 ≠ 0) (hm : p.1-p.2 ≠ 0)
    (hU : left p.1 p.2 ≠ 0) (hW : right p.1 p.2 ≠ 0) :
    let n := normalEquations (1/2) baseHeight baseCovector (embed p)
    (embed w).1*n.1+(embed w).2*n.2=fderiv ℝ outerLog p w := by
  dsimp only
  rw [normalEquations_apply,outerLog_fderiv p.1 p.2 w hp hm hU hW]
  simp only [Fin.sum_univ_three,logVelocity,onWeights,onRadii]
  dsimp [baseCovector,weights,coordVelocity,dx,dy,embed,baseHeight]
  have hroot : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [hp,hm,hU,hW,hroot]
  ring_nf
  simp only [hsqrt]
  ring

/-- In each nonvertex chamber the normal equations have exactly one solution
for the reference triangle and the reference covector. -/
theorem base_normal_fiber (c : Fin 4) :
    {z : Plane | (∀ i, 0 < chamberSigns c i*coordinates (1/2) baseHeight z.1 z.2 i) ∧
        normalEquations (1/2) baseHeight baseCovector z=0} = {embed (basePoint c)} := by
  ext z
  obtain ⟨p,rfl⟩ := embed_surj z
  change (_ ∧ _) ↔ embed p=embed (basePoint c)
  rw [signed_chamber]
  have inv : Function.Injective embed := by
    intro p q eq
    have X := congrArg Prod.fst eq
    have Y := congrArg Prod.snd eq
    dsimp [embed] at X Y
    have eq' : p.1-p.2=q.1-q.2 := by
      apply mul_left_cancel₀ (show Real.sqrt 3 ≠ 0 by positivity)
      linarith
    apply Prod.ext <;> linarith
  rw [inv.eq_iff,← angular_fiber c p.1 p.2]
  apply and_congr_right
  intro hc
  have nz : 1-p.1 ≠ 0 ∧ p.1+p.2 ≠ 0 ∧ p.1-p.2 ≠ 0 := by
    fin_cases c <;> simp [chamber] at hc <;> grind
  have hl i := right_ne_zero_of_mul (((signed_chamber _ _).mpr hc) i).ne'
  have pos i := radii_pos_of_chamber (1/2) baseHeight (embed p) height_ne hl i
  simp only [onRadii] at pos
  have hr : radius p.1 p.2 ≠ 0 := by have := pos 0; dsimp at this; linarith
  have hU : left p.1 p.2 ≠ 0 := by have := pos 1; dsimp at this; linarith
  have hW : right p.1 p.2 ≠ 0 := by have := pos 2; dsimp at this; linarith
  rw [← outerLog_critical_iff p.1 p.2 nz.2.1 nz.2.2 hr hU hW]
  let n := normalEquations (1/2) baseHeight baseCovector (embed p)
  have e := fun w => slope_base p w nz.2.1 nz.2.2 hU hW
  constructor
  · intro hn
    apply ContinuousLinearMap.ext
    intro w
    have ew := (e w).symm
    rw [hn] at ew
    simpa using ew
  · intro D
    obtain ⟨u,hu⟩ := embed_surj (1,0)
    obtain ⟨v,hv⟩ := embed_surj (0,1)
    apply Prod.ext
    · simpa [D,hu] using e u
    · simpa [D,hv] using e v

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Chart

open MaxwellCusp.Spatial.Normal

private def push (a k u v : ℝ) : Plane := (a*u-k*v,k*u+a*v)

private theorem push_dot (a k u v U V : ℝ) (unit : a^2+k^2=1) :
    (push a k u v).1*(push a k U V).1+(push a k u v).2*(push a k U V).2=u*U+v*V := by
  dsimp [push]; linear_combination (u*U+v*V)*unit

/-- On a spatial line, the normalized projection in a rotated frame agrees
with the constant-normal chart equations, including their common scale. -/
private theorem slope_on_line (s h : ℝ) (z : Plane) (c r x y : Triple) (a k m : ℝ)
    (unit : a^2+k^2=1)
    (px : ∀ i, -dx s z.1 i=(push a k (r i*x i) (r i*y i)).1)
    (py : ∀ i, -dy h z.2 i=(push a k (r i*x i) (r i*y i)).2)
    (weights : ∀ i, c i=m*(coordinates s h z.1 z.2 i*r i*x i))
    (u v U V t : ℝ) :
    let w := push a k u v
    let e := push a k U V
    let b := fun u v => coordVelocity s h (push a k u v).1 (push a k u v).2
    let p := (z.1+t*w.1,z.2+t*w.2)
    e.1*(normalEquations s h c p).1+e.2*(normalEquations s h c p).2 =
      m*projectedSlope (coordinates s h z.1 z.2) r x y (b u v) (b U V) u v U V t := by
  dsimp only
  rw [normalEquations_apply,projectedSlope,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let X := r i*x i-t*u
  let Y := r i*y i-t*v
  have Xeq : dx s (z.1+t*(push a k u v).1) i = -(push a k X Y).1 := by
    have e := px i
    dsimp [dx,push,X,Y] at e ⊢
    linarith only [e]
  have Yeq : dy h (z.2+t*(push a k u v).2) i = -(push a k X Y).2 := by
    have e := py i
    dsimp [dy,push,X,Y] at e ⊢
    linarith only [e]
  rw [logVelocity,coordinates_line,radii_eq,Xeq,Yeq,weights]
  have sq : (-(push a k X Y).1)^2+(-(push a k X Y).2)^2=X^2+Y^2 := by
    linear_combination push_dot a k X Y X Y unit
  have dot : -(push a k X Y).1*(push a k U V).1 + -(push a k X Y).2*(push a k U V).2 =
      -(X*U+Y*V) := by linarith only [push_dot a k X Y U V unit]
  rw [sq,dot]
  dsimp [X,Y]
  ring

/-- Annihilating the charge differential picks a nonzero dual vector and
hence an orthonormal null frame. In this frame the two spatial derivatives
of the incidence equations have negative determinant. -/
theorem normalEquations_regular (s h : ℝ) (z : Plane) (c : Triple)
    (hh : h ≠ 0) (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (nc : c ≠ 0)
    (massC : ∑ i, c i=0) (critical : normalEquations s h c z=0) :
    Function.Injective (fderiv ℝ (normalEquations s h c) z) := by
  let l := coordinates s h z.1 z.2
  let p i := -dx s z.1 i
  let q i := -dy h z.2 i
  let n := dualVector s h c z
  have pair (i : Fin 3) : c i=l i*(p i*n.1+q i*n.2) := dual_pair s h c z hh massC hl i
  have len : 0 < n.1^2+n.2^2 := by
    by_contra! e
    have e1 : n.1=0 := by nlinarith [sq_nonneg n.2]
    have e2 : n.2=0 := by nlinarith [sq_nonneg n.1]
    exact nc (by ext i; simp [pair i,e1,e2])
  let m := Real.sqrt (n.1^2+n.2^2)
  have nm : m ≠ 0 := (Real.sqrt_pos.mpr len).ne'
  let a := n.1/m
  let k := n.2/m
  have unit : a^2+k^2=1 := by
    have sq : m^2=n.1^2+n.2^2 := Real.sq_sqrt len.le
    dsimp only [a,k]; field_simp [nm]; linarith only [sq]
  let r i := Real.sqrt (radii s h z.1 z.2 i)
  have hr i := radii_pos_of_chamber s h z hh hl i
  have nr i : r i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have rad i : r i^2=p i^2+q i^2 := (Real.sq_sqrt (hr i).le).trans (by simp [p,q,radii_eq])
  let x i := (a*p i+k*q i)/r i
  let y i := (-k*p i+a*q i)/r i
  have rx i : r i*x i=a*p i+k*q i := by dsimp [x]; field_simp [nr i]
  have ry i : r i*y i= -k*p i+a*q i := by dsimp [y]; field_simp [nr i]
  have ux i : x i^2+y i^2=1 := by
    dsimp [x,y]; field_simp [nr i]
    linear_combination (p i^2+q i^2)*unit-rad i
  have px i : p i=(push a k (r i*x i) (r i*y i)).1 := by
    rw [rx,ry]; dsimp [push]; linear_combination -p i*unit
  have py i : q i=(push a k (r i*x i) (r i*y i)).2 := by
    rw [rx,ry]; dsimp [push]; linear_combination -q i*unit
  have wt i : c i=m*(l i*r i*x i) := by
    rw [pair,mul_assoc (l i),rx]
    dsimp only [a,k]; field_simp [nm]
  have sep (i j : Fin 3) (ne : i ≠ j) : MaxwellCusp.Spatial.minor x y i j ≠ 0 := by
    intro eq
    have nz := displacement_separation s h z hh hl i j ne
    have bad : p i*q j-q i*p j=0 := by
      dsimp [MaxwellCusp.Spatial.minor,x,y] at eq
      field_simp [nr i,nr j] at eq
      linear_combination eq-(p i*q j-q i*p j)*unit
    exact nz (by simpa [p,q] using bad)
  let b (u v : ℝ) := coordVelocity s h (push a k u v).1 (push a k u v).2
  obtain ⟨mass,fx,fy,db⟩ := bary_moments s h z hh
  have sumrot (f : Triple) (U V : ℝ) (hx : ∑ i, f i*p i=U) (hy : ∑ i, f i*q i=V) :
      (∑ i, f i*r i*x i)=a*U+k*V ∧ (∑ i, f i*r i*y i)= -k*U+a*V := by
    simp only [Fin.sum_univ_three,mul_assoc,rx,ry] at hx hy ⊢
    constructor
    · linear_combination a*hx+k*hy
    · linear_combination -k*hx+a*hy
  obtain ⟨fx',fy'⟩ := sumrot l 0 0 fx fy
  simp only [mul_zero,add_zero] at fx' fy'
  have bv (u v : ℝ) : (∑ i, b u v i=0) ∧
      (∑ i, b u v i*r i*x i=u) ∧ (∑ i, b u v i*r i*y i=v) := by
    obtain ⟨M,P,Q⟩ := db (push a k u v).1 (push a k u v).2
    obtain ⟨e,f⟩ := sumrot (b u v) _ _ P Q
    dsimp only [push] at e f
    exact ⟨M,by linear_combination e+u*unit,by linear_combination f+v*unit⟩
  have sl := slope_on_line s h z c r x y a k m unit px py wt
  have moment0 (U V : ℝ) : 3*(∑ i, l i*x i*(x i*U+y i*V))=U := by
    have e := sl 0 0 U V 0
    dsimp only at e
    simp only [zero_mul,add_zero,critical,Prod.fst_zero,Prod.snd_zero,mul_zero] at e
    have zero := (mul_eq_zero.mp e.symm).resolve_left nm
    have term (i : Fin 3) : l i*r i*x i*(b U V i/l i -
        3*((r i*x i)*U+(r i*y i)*V)/((r i*x i)^2+(r i*y i)^2)) =
        b U V i*r i*x i-3*l i*x i*(x i*U+y i*V) := by
      have sq : (r i*x i)^2+(r i*y i)^2=r i^2 := by linear_combination (r i)^2*ux i
      rw [sq]; field_simp [show l i ≠ 0 from hl i,nr i]
    change projectedSlope l r x y (b 0 0) (b U V) 0 0 U V 0=0 at zero
    simp only [projectedSlope,zero_mul,mul_zero,sub_zero,add_zero,term,Fin.sum_univ_three] at zero
    have e' := (bv U V).2.1
    simp only [Fin.sum_univ_three] at e' ⊢
    linear_combination e'-zero
  have xx : ∑ i, l i*x i^2=1/3 := by
    have := moment0 1 0
    simp only [Fin.sum_univ_three] at this ⊢
    linear_combination this/3
  have xy : ∑ i, l i*x i*y i=0 := by
    have := moment0 0 1
    simp only [Fin.sum_univ_three] at this ⊢
    linear_combination this/3
  have yy : ∑ i, l i*y i^2=2/3 := by
    change ∑ i, l i=1 at mass
    simp only [Fin.sum_univ_three] at xx mass ⊢
    linear_combination l 0*ux 0+l 1*ux 1+l 2*ux 2+mass-xx
  let M (u v U V : ℝ) := deriv (projectedSlope l r x y (b u v) (b U V) u v U V) 0
  have det : M 1 0 1 0*M 0 1 0 1-M 1 0 0 1*M 0 1 1 0 < 0 :=
    projectedSlope_det_neg l r x y b hl nr ux sep mass fx' fy' (fun u v => (bv u v).1)
      (fun u v => (bv u v).2.1) (fun u v => (bv u v).2.2) xx xy yy
  let F := normalEquations s h c
  let L := fderiv ℝ F z
  have df : HasFDerivAt F L z :=
    ((normalEquations_smooth s h c z hl (fun i => (hr i).ne')).differentiableAt (by simp)).hasFDerivAt
  have entry (u v U V : ℝ) : (push a k U V).1*(L (push a k u v)).1+
      (push a k U V).2*(L (push a k u v)).2=m*M u v U V := by
    have ln (z w : ℝ) : HasDerivAt (fun t : ℝ => z+t*w) w 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const w).const_add z
    let w := push a k u v
    let e := push a k U V
    have d := df.comp_hasDerivAt_of_eq (0:ℝ) ((ln z.1 w.1).prodMk (ln z.2 w.2)) (by simp)
    have d₁ := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 d
    have d₂ := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0 d
    have test := (d₁.const_mul e.1).add (d₂.const_mul e.2)
    have rhs := (projectedSlope_deriv l r x y (b u v) (b U V) u v U V hl nr ux)
    rw [show M u v U V=_ from rhs.deriv]
    apply test.unique
    convert! rhs.const_mul m using 1
    funext t
    exact sl u v U V t
  apply (injective_iff_map_eq_zero L).mpr
  rintro ⟨U,V⟩ eq
  let u := a*U+k*V
  let v := -k*U+a*V
  have decomp : (U,V) = u • push a k 1 0+v • push a k 0 1 := by
    apply Prod.ext <;> dsimp [push,u,v]
    · linear_combination -U*unit
    · linear_combination -V*unit
  rw [decomp,map_add,map_smul,map_smul] at eq
  have E := congrArg Prod.fst eq
  have G := congrArg Prod.snd eq
  change u*(L (push a k 1 0)).1+v*(L (push a k 0 1)).1=0 at E
  change u*(L (push a k 1 0)).2+v*(L (push a k 0 1)).2=0 at G
  have row (i j : ℝ) : u*M 1 0 i j+v*M 0 1 i j=0 := by
    apply (mul_eq_zero_iff_left nm).mp
    linear_combination (push a k i j).1*E+(push a k i j).2*G-u*entry 1 0 i j-v*entry 0 1 i j
  have e1 := row 1 0
  have e2 := row 0 1
  have gu : u=0 := by
    apply (mul_eq_zero_iff_left det.ne).mp
    linear_combination M 0 1 0 1*e1-M 0 1 1 0*e2
  have gv : v=0 := by
    apply (mul_eq_zero_iff_left det.ne).mp
    linear_combination M 1 0 1 0*e2-M 1 0 0 1*e1
  simpa [gu,gv] using decomp

end MaxwellCausticExtremum.Chart

end
end

section

open Set Filter Topology

namespace MaxwellCausticExtremum.Transport

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Local inverse charts restrict to an arbitrary target subset, including
a closed path times a single level of a system of equations. -/
theorem restrict_local {F : E → X} {S : Set X} (h : IsLocalHomeomorphOn F (F ⁻¹' S)) :
    IsLocalHomeomorph (S.restrictPreimage F) := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro x
  obtain ⟨U,hU,emb⟩ := (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mp h x.1 x.2
  let V : Set (F ⁻¹' S) := Subtype.val ⁻¹' U
  refine ⟨V,continuous_subtype_val.continuousAt.preimage_mem_nhds hU,?_⟩
  let swap : V ≃ₜ ((U.domRestrict F) ⁻¹' S) :=
    { toFun := fun z => ⟨⟨z.1.1,z.2⟩,z.1.2⟩
      invFun := fun z => ⟨⟨z.1.1,z.2⟩,z.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (emb.restrictPreimage S).comp swap.isOpenEmbedding

private def fullFiber (F : E → X) (S : Set X) (x : S) :
    (F ⁻¹' {x.val}) ≃ ((S.restrictPreimage F) ⁻¹' {x}) where
  toFun z := ⟨⟨z.1,show F z.1 ∈ S by rw [show F z.1=x.val from z.2]; exact x.2⟩,Subtype.ext z.2⟩
  invFun z := ⟨z.1.1,congrArg Subtype.val (show S.restrictPreimage F z.1=x from z.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem fiber_count [T2Space E] [T2Space X] {F : E → X} {S : Set X}
    (compact : IsCompact (F ⁻¹' S)) (localInv : IsLocalHomeomorphOn F (F ⁻¹' S))
    {x y : S} (path : Path x y) :
    (F ⁻¹' {x.val}).encard = (F ⁻¹' {y.val}).encard := by
  let := isCompact_iff_compactSpace.mp compact
  have cover := isLocalHomeomorph_iff_isCoveringMap.mp (restrict_local localInv)
  exact encard_congr <| (fullFiber F S x).trans <|
    (Equiv.ofBijective _ (cover.monodromy_bijective (.mk path))).trans (fullFiber F S y).symm

/-- The ambient inverse-chart hypothesis is supplied directly by a strict
derivative that is a linear equivalence at each point of the selected level. -/
theorem regular_level_count {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [CompleteSpace A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {F : A → B} {S : Set B} (compact : IsCompact (F ⁻¹' S))
    (regular : ∀ p, F p ∈ S → ∃ L : A ≃L[ℝ] B, HasStrictFDerivAt F (L : A →L[ℝ] B) p)
    {x y : S} (path : Path x y) : (F ⁻¹' {x.val}).encard = (F ⁻¹' {y.val}).encard := by
  apply fiber_count compact _ path
  intro p hp
  obtain ⟨L,d⟩ := regular p hp
  exact ⟨d.toOpenPartialHomeomorph F,d.mem_toOpenPartialHomeomorph_source,rfl⟩

end MaxwellCausticExtremum.Transport

end

section

noncomputable section
open Set Filter Topology

namespace MaxwellCausticExtremum.Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem open_path_count [Nontrivial E] (U : Set (ℝ × E)) (hU : IsOpen U)
    (G : ℝ × E → E)
    (compact : IsCompact {p : ℝ × E | p.1 ∈ Icc 0 1 ∧ p ∈ U ∧ G p=0})
    (smooth : ∀ p ∈ U, ContDiffAt ℝ 1 G p)
    (regular : ∀ p ∈ U, p.1 ∈ Icc 0 1 → G p=0 →
      Function.Injective (fderiv ℝ (fun x => G (p.1,x)) p.2)) :
    {x : E | (0,x) ∈ U ∧ G (0,x)=0}.encard = {x : E | (1,x) ∈ U ∧ G (1,x)=0}.encard := by
  classical
  obtain ⟨c,nc⟩ := exists_ne (0:E)
  let F (p : ℝ × E) := if p ∈ U then (p.1,G p) else (p.1,c)
  let S : Set (ℝ × E) := Icc 0 1 ×ˢ {0}
  have pre (p : ℝ × E) : F p ∈ S ↔ p.1 ∈ Icc 0 1 ∧ p ∈ U ∧ G p=0 := by
    by_cases h : p ∈ U <;> simp [F,S,h,nc]
  have hc : IsCompact (F ⁻¹' S) := by
    convert compact using 1
    exact Set.ext pre
  have inv (p : ℝ × E) (hp : F p ∈ S) :
      ∃ L : (ℝ × E) ≃L[ℝ] (ℝ × E), HasStrictFDerivAt F (L : (ℝ × E) →L[ℝ] (ℝ × E)) p := by
    obtain ⟨ht,hu,hg⟩ := (pre p).mp hp
    let D := fderiv ℝ G p
    let L := (ContinuousLinearMap.fst ℝ ℝ E).prod D
    have d := (smooth p hu).hasStrictFDerivAt (by simp)
    have dp : HasStrictFDerivAt (fun q : ℝ × E => (q.1,G q)) L p :=
      (ContinuousLinearMap.fst ℝ ℝ E).hasStrictFDerivAt.prodMk d
    have slice : HasFDerivAt (fun x => G (p.1,x))
        (D.comp (ContinuousLinearMap.inr ℝ ℝ E)) p.2 :=
      d.hasFDerivAt.comp p.2 ((hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2))
    have inj := regular p hu ht hg
    rw [slice.fderiv] at inj
    have li : Function.Injective L := by
      apply (injective_iff_map_eq_zero L).mpr
      rintro ⟨t,x⟩ h
      obtain rfl : t=0 := congrArg Prod.fst h
      have hx : x=0 := (injective_iff_map_eq_zero _).mp inj x (congrArg Prod.snd h)
      simp [hx]
    let e := (LinearEquiv.ofBijective L.toLinearMap
      ⟨li,LinearMap.injective_iff_surjective.mp li⟩).toContinuousLinearEquiv
    refine ⟨e,dp.congr_of_eventuallyEq ?_⟩
    filter_upwards [hU.mem_nhds hu] with q hq
    simp only [F,if_pos hq]
  let lift (t : Set.Icc (0:ℝ) 1) : S := ⟨(t.1,0),t.2,rfl⟩
  let start := lift ⟨0,by simp⟩
  let stop := lift ⟨1,by simp⟩
  let path : Path start stop := ⟨⟨lift,by dsimp [lift]; fun_prop⟩,rfl,rfl⟩
  have tr := regular_level_count hc inv path
  have fiber (t : ℝ) : (F ⁻¹' {(t,(0:E))}).encard = {x : E | (t,x) ∈ U ∧ G (t,x)=0}.encard := by
    let B : Set E := {x | (t,x) ∈ U ∧ G (t,x)=0}
    have eq : F ⁻¹' {(t,(0:E))} = (fun x => (t,x)) '' B := by
      ext ⟨a,x⟩
      by_cases h : (a,x) ∈ U
      · simp [F,h,B,Set.mem_image,Prod.ext_iff]
        grind
      · simp [F,h,B,nc,Set.mem_image,Prod.ext_iff]
        grind
    rw [eq]
    exact (show Function.Injective (fun x : E => (t,x)) from fun _ _ e => congrArg Prod.snd e).encard_image B
  exact (fiber 0).symm.trans (tr.trans (fiber 1))

end MaxwellCausticExtremum.Transport

end
end

section

noncomputable section

open Set
open scoped NNReal ENNReal

namespace MaxwellCausticExtremum.Compact

abbrev Weights := Fin 3 → ℝ

def mass (p : Weights) := p 0 + p 1 + p 2

def X (s : ℝ) (p : Weights) := p 1 + s*p 2

def Y (h : ℝ) (p : Weights) := h*p 2

def U (s : ℝ) (p : Weights) (i : Fin 3) :=
  X s p - mass p * (![0,1,s] : Weights) i

def V (h : ℝ) (p : Weights) (i : Fin 3) :=
  Y h p - mass p * (![0,0,h] : Weights) i

def R (s h : ℝ) (p : Weights) (i : Fin 3) := U s p i ^ 2 + V h p i ^ 2

def W (s h : ℝ) (p : Weights) :=
  p 0*p 1 + p 0*p 2*(s^2+h^2) + p 1*p 2*((s-1)^2+h^2)

def major (s h : ℝ) := 1 + h^2 + s^2 + (s-1)^2

private theorem linear_sq (a b x y : ℝ) :
    (a*x+b*y)^2 ≤ (a^2+b^2)*(x^2+y^2) := by
  nlinarith only [sq_nonneg (a*y-b*x)]

private theorem weight_bound (s h : ℝ) (p : Weights) (i j : Fin 3) (hne : i ≠ j) :
    (h*p j)^2 ≤ major s h * R s h p i := by
  let a : Weights := ![-h,h,0]
  let b : Weights := ![s-1,-s,1]
  have eq : h*p j = a j*U s p i + b j*V h p i := by
    fin_cases i <;> fin_cases j <;> first | contradiction |
      simp [a,b,U,V,X,Y,mass] <;> ring
  have hM : a j^2+b j^2 ≤ major s h := by
    fin_cases j <;> simp [a,b,major] <;> nlinarith [sq_nonneg h,sq_nonneg s,sq_nonneg (s-1)]
  rw [eq]
  exact (linear_sq ..).trans (mul_le_mul_of_nonneg_right hM (by positivity))

private theorem product_bound (s h : ℝ) (p : Weights) (i : Fin 3) :
    |h^2*p (i+1)*p (i+2)| ≤ major s h * R s h p i := by
  have a := weight_bound s h p i (i+1) (by fin_cases i <;> decide)
  have b := weight_bound s h p i (i+2) (by fin_cases i <;> decide)
  apply abs_le.mpr
  constructor <;> nlinarith only [a,b,sq_nonneg (h*p (i+1)+h*p (i+2)),
    sq_nonneg (h*p (i+1)-h*p (i+2))]

def raw (s h : ℝ) (p : Weights) : Prop :=
  2*R s h p 0*R s h p 1*R s h p 2 ≤ 9*h^2*p 0*p 1*p 2*mass p*W s h p

def safe (s h : ℝ) (p : Weights) : Prop :=
  ∀ i : Fin 3, 2*R s h p (i+1)*R s h p (i+2) ≤
    9*|p i*mass p*W s h p| * major s h

theorem safe_of_raw {s h : ℝ} {p : Weights} (hr : ∀ i, 0 < R s h p i)
    (he : raw s h p) : safe s h p := by
  intro i
  apply le_of_mul_le_mul_right _ (hr i)
  calc
    _ = 2*R s h p 0*R s h p 1*R s h p 2 := by fin_cases i <;> dsimp <;> ring
    _ ≤ _ := he
    _ = 9*(p i*mass p*W s h p)*(h^2*p (i+1)*p (i+2)) := by fin_cases i <;> dsimp <;> ring
    _ ≤ |9*(p i*mass p*W s h p)*(h^2*p (i+1)*p (i+2))| := le_abs_self _
    _ = 9*|p i*mass p*W s h p| * |h^2*p (i+1)*p (i+2)| := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 9)]
    _ ≤ 9*|p i*mass p*W s h p| * (major s h*R s h p i) :=
      mul_le_mul_of_nonneg_left (product_bound s h p i) (by positivity)
    _ = _ := by ring

private theorem at_infinity {s h : ℝ} {p : Weights} (hh : h ≠ 0) (hp : mass p = 0)
    (he : raw s h p) : ∀ i, p i = 0 := by
  simp [raw,R,U,V,hp] at he
  have hz : X s p ^ 2 + Y h p ^ 2 = 0 := by
    by_contra ne
    have pos : 0 < X s p ^ 2 + Y h p ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm ne)
    exact (not_lt_of_ge he) (by positivity)
  have hy : Y h p = 0 := by nlinarith [sq_nonneg (X s p),sq_nonneg (Y h p)]
  have hx : X s p = 0 := by nlinarith [sq_nonneg (X s p),sq_nonneg (Y h p)]
  have hc : p 2 = 0 := (mul_eq_zero.mp hy).resolve_left hh
  simp [X,hc] at hx
  simp [mass,hx,hc] at hp
  intro i
  fin_cases i <;> assumption

private theorem at_site {s h : ℝ} {p : Weights} {i : Fin 3} (hh : h ≠ 0)
    (ht : 0 < mass p) (he : safe s h p) : 0 < R s h p i := by
  by_contra! hn
  have hu : U s p i = 0 := by dsimp [R] at hn; nlinarith [sq_nonneg (V h p i)]
  have hv : V h p i = 0 := by dsimp [R] at hn; nlinarith [sq_nonneg (U s p i)]
  have others (j : Fin 3) (hnj : i ≠ j) : p j = 0 := by
    have hb := weight_bound s h p i j hnj
    simp [R,hu,hv] at hb
    exact hb.resolve_left hh
  have hW : W s h p = 0 := by
    fin_cases i
    · simp [W,others 1 (by decide),others 2 (by decide)]
    · simp [W,others 0 (by decide),others 2 (by decide)]
    · simp [W,others 0 (by decide),others 1 (by decide)]
  have ne (j : Fin 3) (hnj : i ≠ j) : 0 < R s h p j := by
    have hu' := sub_eq_zero.mp hu
    have hv' := sub_eq_zero.mp hv
    dsimp only [R,U,V]
    rw [hu',hv']
    fin_cases i <;> fin_cases j <;> first | contradiction |
      (simp; positivity)
  have hn' := he i
  rw [hW] at hn'
  simp at hn'
  exact (not_lt_of_ge hn') (by have := ne (i+1) (by fin_cases i <;> decide)
                               have := ne (i+2) (by fin_cases i <;> decide)
                               positivity)

end MaxwellCausticExtremum.Compact

namespace MaxwellCausticExtremum.Compact

abbrev Shape := ℝ × ℝ
abbrev State := Shape × Weights

def size (p : Weights) := |p 0| + |p 1| + |p 2|

private theorem size_scale (k : ℝ) (p : Weights) : size (k • p) = |k| * size p := by
  simp [size,abs_mul,mul_add]

private theorem size_bound (p : Weights) (i : Fin 3) : |p i| ≤ size p := by
  fin_cases i <;> dsimp [size] <;> linarith [abs_nonneg (p 0),abs_nonneg (p 1),abs_nonneg (p 2)]

private theorem mass_scale (k : ℝ) (p : Weights) : mass (k • p) = k*mass p := by
  simp [mass,mul_add]

private theorem R_scale (s h k : ℝ) (p : Weights) (i : Fin 3) :
    R s h (k • p) i = k^2*R s h p i := by
  simp [R,U,V,X,Y,mass_scale]
  ring

private theorem W_scale (s h k : ℝ) (p : Weights) : W s h (k • p) = k^2*W s h p := by
  simp [W]
  ring

private theorem raw_scale {s h : ℝ} {p : Weights} (k : ℝ) (hr : raw s h p) :
    raw s h (k • p) := by
  unfold raw at *
  simp only [R_scale,W_scale,mass_scale,Pi.smul_apply,smul_eq_mul]
  linear_combination (norm := ring_nf) k^6 * hr
  exact le_rfl

def model (K : Set Shape) (sign : Weights) : Set State :=
  {z | z.1 ∈ K ∧ size z.2 = 1 ∧ 0 ≤ mass z.2 ∧
    (∀ i, 0 ≤ sign i*z.2 i) ∧ raw z.1.1 z.1.2 z.2 ∧ safe z.1.1 z.1.2 z.2}

private theorem model_compact {K : Set Shape} (hc : IsCompact K) (sign : Weights) :
    IsCompact (model K sign) := by
  have closed : IsClosed (model K sign) := by
    simp only [model,raw,safe,ofPred_and,ofPred_forall]
    refine (hc.isClosed.preimage continuous_fst).inter ?_
    refine (isClosed_eq (by unfold size; fun_prop) continuous_const).inter ?_
    refine (isClosed_le continuous_const (by unfold mass; fun_prop)).inter ?_
    refine (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter ?_
    refine (isClosed_le ?_ ?_).inter ?_
    · dsimp [R,U,V,X,Y,mass]
      fun_prop
    · dsimp [W,mass]
      fun_prop
    · apply isClosed_iInter
      intro i
      apply isClosed_le
      · fin_cases i <;> dsimp [R,U,V,X,Y,mass] <;> fun_prop
      · dsimp [W,mass,major]
        fun_prop
  apply (hc.prod (isCompact_Icc (a := fun _ : Fin 3 => (-1 : ℝ)) (b := fun _ => (1:ℝ)))).of_isClosed_subset closed
  intro z hz
  refine ⟨hz.1, (fun i => ?_), (fun i => ?_)⟩
  all_goals have hb := size_bound z.2 i
            rw [hz.2.1] at hb
  · exact (abs_le.mp hb).1
  · exact (abs_le.mp hb).2

private theorem model_regular {K : Set Shape} {sign : Weights} {z : State}
    (hn : ∀ a ∈ K, a.2 ≠ 0) (hsgn : ∀ i, sign i ≠ 0) (hz : z ∈ model K sign) :
    0 < mass z.2 ∧ (∀ i, 0 < R z.1.1 z.1.2 z.2 i) ∧ ∀ i, 0 < sign i*z.2 i := by
  obtain ⟨hk,hs,ht,hsg,hr,he⟩ := hz
  have hm : 0 < mass z.2 := by
    apply lt_of_le_of_ne ht
    intro h
    have e := at_infinity (hn _ hk) h.symm hr
    simp [size,e] at hs
  have rad (i : Fin 3) := at_site (i := i) (hn _ hk) hm he
  refine ⟨hm,rad,fun i => lt_of_le_of_ne (hsg i) ?_⟩
  intro h
  have rhs : z.2 i ≠ 0 := by
    intro e
    have lt : 0 < 2*R z.1.1 z.1.2 z.2 0*R z.1.1 z.1.2 z.2 1*R z.1.1 z.1.2 z.2 2 := mul_pos (mul_pos (mul_pos (by norm_num) (rad 0)) (rad 1)) (rad 2)
    unfold raw at hr
    fin_cases i <;> dsimp at e <;> rw [e] at hr <;> simp at hr <;> linarith
  exact mul_ne_zero (hsgn i) rhs h.symm

end MaxwellCausticExtremum.Compact

namespace MaxwellCausticExtremum.Compact

def sheet (K : Set Shape) (sign : Weights) : Set State :=
  {z | z.1 ∈ K ∧ mass z.2 = 1 ∧ (∀ i, 0 < sign i*z.2 i) ∧ raw z.1.1 z.1.2 z.2}

private theorem positive_radii {s h : ℝ} {p : Weights} (hh : h ≠ 0)
    (nz : ∀ i, p i ≠ 0) (i : Fin 3) : 0 < R s h p i := by
  have b := weight_bound s h p i (i+1) (by fin_cases i <;> decide)
  have u := sq_pos_of_ne_zero (mul_ne_zero hh (nz (i+1)))
  exact pos_of_mul_pos_right (u.trans_le b) (by unfold major; positivity)

theorem sheet_compact {K : Set Shape} (hc : IsCompact K) (hn : ∀ a ∈ K, a.2 ≠ 0)
    (sign : Weights) (hsgn : ∀ i, sign i ≠ 0) : IsCompact (sheet K sign) := by
  let f (z : State) : State := (z.1,(mass z.2)⁻¹ • z.2)
  have hf : ContinuousOn f (model K sign) := by
    intro z hz
    have hm := (model_regular hn hsgn hz).1.ne'
    exact continuousWithinAt_fst.prodMk
      (((show Continuous (fun w : State => mass w.2) by unfold mass; fun_prop).continuousWithinAt.inv₀ hm).smul
      continuousWithinAt_snd)
  have eq : f '' model K sign = sheet K sign := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      obtain ⟨hm,_,hs⟩ := model_regular hn hsgn hw
      obtain ⟨hk,_,_,_,hr,_⟩ := hw
      refine ⟨hk,?_,?_,raw_scale _ hr⟩
      · simp [f,mass_scale,hm.ne']
      · intro i
        change 0 < sign i*((mass w.2)⁻¹*w.2 i)
        rw [mul_left_comm]
        exact mul_pos (inv_pos.mpr hm) (hs i)
    · rintro ⟨hk,hm,hsi,hr⟩
      have nz (i : Fin 3) : z.2 i ≠ 0 := right_ne_zero_of_mul (hsi i).ne'
      have hsz : 0 < size z.2 := (abs_pos.mpr (nz 0)).trans_le (size_bound _ _)
      let k := (size z.2)⁻¹
      have hp : 0 < k := inv_pos.mpr hsz
      let w : State := (z.1,k • z.2)
      have mw : mass w.2 = k := by simp [w,mass_scale,hm]
      have wr : raw w.1.1 w.1.2 w.2 := raw_scale k hr
      refine ⟨w,⟨hk,?_,mw.symm ▸ hp.le,?_,wr,safe_of_raw ?_ wr⟩,?_⟩
      · simp [w,size_scale,abs_of_pos hp,k,hsz.ne']
      · intro i
        change 0 ≤ sign i*(k*z.2 i)
        rw [mul_left_comm]
        exact (mul_pos hp (hsi i)).le
      · intro i
        exact positive_radii (hn _ hk) (fun j => mul_ne_zero hp.ne' (nz j)) i
      · refine Prod.ext ?_ ?_
        · rfl
        · change (mass w.2)⁻¹ • (k • z.2) = _
          rw [mw,smul_smul,inv_mul_cancel₀ hp.ne',one_smul]
  exact eq ▸ (model_compact hc sign).image_of_continuousOn hf

/-- Convert the compact sheet to the physical plane. -/
def physical (z : State) : Shape × (ℝ × ℝ) := (z.1,X z.1.1 z.2,Y z.1.2 z.2)

theorem physical_sheet_compact {K : Set Shape} (hc : IsCompact K)
    (hn : ∀ a ∈ K, a.2 ≠ 0) (sign : Weights) (hsgn : ∀ i, sign i ≠ 0) :
    IsCompact (physical '' sheet K sign) :=
  (sheet_compact hc hn sign hsgn).image (by unfold physical X Y; fun_prop)

end MaxwellCausticExtremum.Compact

namespace MaxwellCausticExtremum.Compact

/-- Chart barycentrics and squared distances in the format of the determinant formula. -/
def bary (s h x y : ℝ) : Weights := ![1-x+(s-1)*y/h,x-s*y/h,y/h]

def distSq (s h x y : ℝ) : Weights := ![x^2+y^2,(x-1)^2+y^2,(x-s)^2+(y-h)^2]

private theorem mass_bary (s h x y : ℝ) (hh : h ≠ 0) : mass (bary s h x y) = 1 := by
  simp [mass,bary]
  field_simp
  ring

private theorem physical_bary (s h x y : ℝ) (hh : h ≠ 0) :
    X s (bary s h x y) = x ∧ Y h (bary s h x y) = y := by
  constructor <;> simp [X,Y,bary]
  field_simp
  ring
  field_simp

private theorem bary_physical (s h : ℝ) (p : Weights) (ht : mass p = 1) (hh : h ≠ 0) :
    bary s h (X s p) (Y h p) = p := by
  funext i
  dsimp [mass] at ht
  fin_cases i <;> simp [bary,X,Y] <;> field_simp <;> nlinarith only [ht,congrArg (fun t : ℝ => h*t) ht]

private theorem radii_physical (s h : ℝ) (p : Weights) (ht : mass p = 1) (i : Fin 3) :
    R s h p i = distSq s h (X s p) (Y h p) i := by
  fin_cases i <;> simp [R,U,V,distSq,ht]

private theorem moment (s h : ℝ) (p : Weights) :
    (∑ i, p i*R s h p i) = mass p*W s h p := by
  simp [Fin.sum_univ_three,R,U,V,mass,W,X,Y]
  ring

/-- Compactness for any determinant presented by the chart's Cauchy–Binet
formula, in particular for the normalized Coulomb Hessian determinant. -/
theorem compact_of_det_formula (J : ℝ → ℝ → ℝ → ℝ → ℝ)
    (formula : ∀ s h x y, h ≠ 0 → (∀ i, distSq s h x y i ≠ 0) →
      let l := bary s h x y
      let r := distSq s h x y
      J s h x y = 9*h^2*l 0*l 1*l 2*(∑ i, l i*r i)/(r 0*r 1*r 2)-2)
    {K : Set Shape} (hc : IsCompact K) (hn : ∀ a ∈ K, a.2 ≠ 0)
    (sign : Weights) (hsign : ∀ i, sign i ≠ 0) :
    IsCompact {z : Shape × (ℝ × ℝ) | z.1 ∈ K ∧
      (∀ i, 0 < sign i*bary z.1.1 z.1.2 z.2.1 z.2.2 i) ∧
      0 ≤ J z.1.1 z.1.2 z.2.1 z.2.2} := by
  have crit (s h : ℝ) (p : Weights) (hh : h ≠ 0) (hm : mass p = 1)
      (hz : ∀ i, 0 < sign i*p i) :
      0 ≤ J s h (X s p) (Y h p) ↔ raw s h p := by
    have hr := positive_radii (s := s) hh (fun i => right_ne_zero_of_mul (hz i).ne')
    have e := formula s h (X s p) (Y h p) hh (fun i => (radii_physical s h p hm i) ▸ (hr i).ne')
    dsimp only at e
    simp only [bary_physical s h p hm hh,← radii_physical s h p hm,moment] at e
    rw [e,sub_nonneg,le_div_iff₀ (mul_pos (mul_pos (hr 0) (hr 1)) (hr 2))]
    unfold raw
    ring_nf
  have eq : physical '' sheet K sign = {z : Shape × (ℝ × ℝ) | z.1 ∈ K ∧
      (∀ i, 0 < sign i*bary z.1.1 z.1.2 z.2.1 z.2.2 i) ∧
      0 ≤ J z.1.1 z.1.2 z.2.1 z.2.2} := by
    ext z
    constructor
    · rintro ⟨w,⟨hk,hm,hz,hr⟩,rfl⟩
      change w.1 ∈ K ∧ (∀ i, 0 < sign i*bary w.1.1 w.1.2 (X w.1.1 w.2) (Y w.1.2 w.2) i) ∧ _
      rw [bary_physical _ _ _ hm (hn _ hk)]
      exact ⟨hk,hz,(crit _ _ _ (hn _ hk) hm hz).mpr hr⟩
    · rintro ⟨hk,hz,hr⟩
      let p := bary z.1.1 z.1.2 z.2.1 z.2.2
      have hh := hn _ hk
      have hm := mass_bary z.1.1 _ z.2.1 z.2.2 hh
      obtain ⟨hx,hy⟩ := physical_bary z.1.1 _ z.2.1 z.2.2 hh
      refine ⟨(z.1,p),⟨hk,hm,hz,(crit _ _ p hh hm hz).mp ?_⟩,?_⟩
      · simpa only [p,hx,hy] using hr
      · exact Prod.ext rfl (Prod.ext hx hy)
  exact eq ▸ physical_sheet_compact hc hn sign hsign

end MaxwellCausticExtremum.Compact

end
end

section

noncomputable section
open Set Filter Topology

namespace MaxwellCausticExtremum.Chart

theorem normalEquations_det_zero (s h : ℝ) (z : Plane) (c : Triple)
    (hh : h ≠ 0) (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) (nc : c ≠ 0)
    (mass : ∑ i, c i=0) (critical : normalEquations s h c z=0) : detH s h z.1 z.2=0 := by
  have hr i := (radii_pos_of_chamber s h z hh hl i).ne'
  have ann := (normalEquations_zero_iff s h c z mass hl hr).mp critical
  apply (critical_iff s h z.1 z.2 hh hl hr).mp
  let L := fderiv ℝ (chargeMap s h) z
  let d := jacobian s h z.1 z.2
  change d=0
  by_contra hn
  have e1 := ann (1,0)
  have e2 := ann (0,1)
  have k1 : c 1*d=0 := by
    dsimp only [d,jacobian]
    linear_combination (L (0,1)).2*e1-(L (1,0)).2*e2
  have k2 : c 2*d=0 := by
    dsimp only [d,jacobian]
    linear_combination (L (1,0)).1*e2-(L (0,1)).1*e1
  have a := (mul_eq_zero.mp k1).resolve_right hn
  have b := (mul_eq_zero.mp k2).resolve_right hn
  simp only [Fin.sum_univ_three,a,b,add_zero] at mass
  exact nc (by funext i; fin_cases i <;> assumption)

theorem family_smooth (s h : ℝ → ℝ) (c : ℝ → Triple) (p : ℝ × Plane)
    (hs : ContDiffAt ℝ 1 s p.1) (ht : ContDiffAt ℝ 1 h p.1)
    (hc : ∀ i, ContDiffAt ℝ 1 (fun t => c t i) p.1)
    (hh : h p.1 ≠ 0) (hl : ∀ i, coordinates (s p.1) (h p.1) p.2.1 p.2.2 i ≠ 0) :
    ContDiffAt ℝ 1 (fun w : ℝ × Plane => normalEquations (s w.1) (h w.1) (c w.1) w.2) p := by
  have dr i := (radii_pos_of_chamber (s p.1) (h p.1) p.2 hh hl i).ne'
  have S : ContDiffAt ℝ 1 (fun w : ℝ × Plane => s w.1) p := hs.comp p contDiffAt_fst
  have H : ContDiffAt ℝ 1 (fun w : ℝ × Plane => h w.1) p := ht.comp p contDiffAt_fst
  have C i : ContDiffAt ℝ 1 (fun w : ℝ × Plane => c w.1 i) p := (hc i).comp p contDiffAt_fst
  have dL i : ContDiffAt ℝ 1 (fun w : ℝ × Plane => coordinates (s w.1) (h w.1) w.2.1 w.2.2 i) p := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop (disch := exact hh)
  have dR i : ContDiffAt ℝ 1 (fun w : ℝ × Plane => radii (s w.1) (h w.1) w.2.1 w.2.2 i) p := by
    fin_cases i <;> dsimp [radii] <;> fun_prop
  have vel (u v : ℝ) (i : Fin 3) :
      ContDiffAt ℝ 1 (fun w : ℝ × Plane => logVelocity (s w.1) (h w.1) w.2.1 w.2.2 u v i) p := by
    have B : ContDiffAt ℝ 1 (fun w : ℝ × Plane => coordVelocity (s w.1) (h w.1) u v i) p := by
      fin_cases i <;> dsimp [coordVelocity] <;> fun_prop (disch := exact hh)
    have X : ContDiffAt ℝ 1 (fun w : ℝ × Plane => dx (s w.1) w.2.1 i) p := by
      fin_cases i <;> dsimp [dx] <;> fun_prop
    have Y : ContDiffAt ℝ 1 (fun w : ℝ × Plane => dy (h w.1) w.2.2 i) p := by
      fin_cases i <;> dsimp [dy] <;> fun_prop
    unfold logVelocity
    fun_prop (disch := first | exact hl _ | exact dr _)
  unfold normalEquations
  fun_prop

theorem path_sheet_compact (s h : ℝ → ℝ) (sign : Triple) (hs : Continuous s) (ht : Continuous h)
    (height : ∀ t ∈ Icc (0:ℝ) 1, h t ≠ 0) (signs : ∀ i, sign i ≠ 0) :
    IsCompact {p : ℝ × Plane | p.1 ∈ Icc (0:ℝ) 1 ∧
      (∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i) ∧
      0 ≤ detH (s p.1) (h p.1) p.2.1 p.2.2} := by
  let I := Icc (0:ℝ) 1
  let shape (t : ℝ) : Plane := (s t,h t)
  let K := shape '' I
  have cs : Continuous shape := hs.prodMk ht
  have cK : IsCompact K := isCompact_Icc.image cs
  have nh : ∀ p ∈ K, p.2 ≠ 0 := by rintro _ ⟨t,ht,rfl⟩; exact height t ht
  let sheet := {w : Plane × Plane | w.1 ∈ K ∧
    (∀ i, 0 < sign i*coordinates w.1.1 w.1.2 w.2.1 w.2.2 i) ∧ 0 ≤ detH w.1.1 w.1.2 w.2.1 w.2.2}
  have comp : IsCompact sheet := Compact.compact_of_det_formula detH detH_eq cK nh sign signs
  let T := {p : ℝ × Plane | p.1 ∈ I ∧ (shape p.1,p.2) ∈ sheet}
  have cp : IsCompact T := by
    let D := (I ×ˢ sheet) ∩ {w : ℝ × (Plane × Plane) | shape w.1=w.2.1}
    have cd : IsCompact D := (isCompact_Icc.prod comp).inter_right
      (isClosed_eq (cs.comp continuous_fst) (continuous_fst.comp continuous_snd))
    have eq : (fun w : ℝ × (Plane × Plane) => (w.1,w.2.2)) '' D=T := by
      ext p
      constructor
      · rintro ⟨⟨t,a,z⟩,⟨⟨hi,hk⟩,he⟩,rfl⟩
        exact ⟨hi,he.symm ▸ hk⟩
      · intro hp
        exact ⟨(p.1,shape p.1,p.2),⟨⟨hp.1,hp.2⟩,rfl⟩,rfl⟩
    rw [← eq]
    exact cd.image (by fun_prop)

  have eq : T={p : ℝ × Plane | p.1 ∈ I ∧
      (∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i) ∧
      0 ≤ detH (s p.1) (h p.1) p.2.1 p.2.2} := by
    ext p
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,⟨p.1,h.1,rfl⟩,h.2⟩⟩
  exact eq ▸ cp

theorem path_chamber_open (s h : ℝ → ℝ) (sign : Triple) (hs : Continuous s) (ht : Continuous h) :
    IsOpen {p : ℝ × Plane | h p.1 ≠ 0 ∧
      ∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i} := by
  let U := {p : ℝ × Plane | h p.1 ≠ 0 ∧
    ∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i}
  have op : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    obtain ⟨hh,hp⟩ := hp
    have sh : ContinuousAt (fun w : ℝ × Plane => s w.1) p := (hs.comp continuous_fst).continuousAt
    have ht' : ContinuousAt (fun w : ℝ × Plane => h w.1) p := (ht.comp continuous_fst).continuousAt
    have ev (i : Fin 3) : ∀ᶠ w : ℝ × Plane in 𝓝 p,
        0 < sign i*coordinates (s w.1) (h w.1) w.2.1 w.2.2 i := by
      have H : ContinuousAt (fun w : ℝ × Plane => sign i*coordinates (s w.1) (h w.1) w.2.1 w.2.2 i) p := by
        apply continuousAt_const.mul
        have X : ContinuousAt (fun w : ℝ × Plane => w.2.1) p := (continuous_fst.comp continuous_snd).continuousAt
        have Y : ContinuousAt (fun w : ℝ × Plane => w.2.2) p := (continuous_snd.comp continuous_snd).continuousAt
        fin_cases i
        · exact (continuousAt_const.sub X).add (((sh.sub continuousAt_const).mul Y).div ht' hh)
        · exact X.sub ((sh.mul Y).div ht' hh)
        · exact Y.div ht' hh
      exact continuousAt_const.eventually_lt H (hp i)
    exact (ht'.eventually_ne hh).and (Filter.eventually_all.mpr ev)
  exact op

theorem normal_path_count (s h : ℝ → ℝ) (c : ℝ → Triple) (sign : Triple)
    (hs : ContDiff ℝ 1 s) (ht : ContDiff ℝ 1 h) (hc : ∀ i, ContDiff ℝ 1 (fun t => c t i))
    (height : ∀ t ∈ Icc (0:ℝ) 1, h t ≠ 0) (signs : ∀ i, sign i ≠ 0)
    (nc : ∀ t ∈ Icc (0:ℝ) 1, c t ≠ 0) (mass : ∀ t, ∑ i, c t i=0) :
    let fiber (t : ℝ) := {z : Plane | (∀ i, 0 < sign i*coordinates (s t) (h t) z.1 z.2 i) ∧
      normalEquations (s t) (h t) (c t) z=0}
    (fiber 0).encard = (fiber 1).encard := by
  let I := Icc (0:ℝ) 1
  let U := {p : ℝ × Plane | h p.1 ≠ 0 ∧
    ∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i}
  have op : IsOpen U := path_chamber_open s h sign hs.continuous ht.continuous
  let G (p : ℝ × Plane) := normalEquations (s p.1) (h p.1) (c p.1) p.2
  have sm (p : ℝ × Plane) (hp : p ∈ U) : ContDiffAt ℝ 1 G p :=
    family_smooth s h c p hs.contDiffAt ht.contDiffAt (fun i => (hc i).contDiffAt) hp.1
      (fun i => right_ne_zero_of_mul (hp.2 i).ne')
  let T := {p : ℝ × Plane | p.1 ∈ I ∧
    (∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i) ∧
    0 ≤ detH (s p.1) (h p.1) p.2.1 p.2.2}
  have cp : IsCompact T := path_sheet_compact s h sign hs.continuous ht.continuous height signs
  have sub {p : ℝ × Plane} (hp : p ∈ T) : p ∈ U := ⟨height p.1 hp.1,hp.2.1⟩
  have compact : IsCompact {p : ℝ × Plane | p.1 ∈ I ∧ p ∈ U ∧ G p=0} := by
    let := isCompact_iff_compactSpace.mp cp
    have cont : Continuous (fun p : T => G p.1) := continuous_iff_continuousAt.mpr
      (fun p => (sm p.1 (sub p.2)).continuousAt.comp continuous_subtype_val.continuousAt)
    have closed := isClosed_eq cont (g := fun _ => (0:Plane)) continuous_const
    have eq : Subtype.val '' {p : T | G p.1=0} = {p : ℝ × Plane | p.1 ∈ I ∧ p ∈ U ∧ G p=0} := by
      ext p
      constructor
      · rintro ⟨⟨q,hq⟩,hz,rfl⟩; exact ⟨hq.1,sub hq,hz⟩
      · rintro ⟨hi,hu,hg⟩
        have hz := normalEquations_det_zero (s p.1) (h p.1) p.2 (c p.1) hu.1
          (fun i => right_ne_zero_of_mul (hu.2 i).ne') (nc _ hi) (mass _) hg
        exact ⟨⟨p,hi,hu.2,hz.ge⟩,hg,rfl⟩
    rw [← eq]; exact closed.isCompact.image continuous_subtype_val
  have count := Transport.open_path_count U op G compact sm (by
    intro p hu hi hg
    exact normalEquations_regular _ _ _ _ hu.1 (fun i => right_ne_zero_of_mul (hu.2 i).ne')
      (nc _ hi) (mass _) hg)
  simpa [U,G,height 0 (by simp),height 1 (by simp)] using count

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section
open Set Filter Topology Real

namespace MaxwellCausticExtremum.Chart

def angleCovector (t : ℝ) : Triple := ![sin t-cos t,-sin t,cos t]

def normalFiber (s h : ℝ) (c : Fin 4) (t : ℝ) : Set Plane :=
  {z | (∀ i, 0 < chamberSigns c i*coordinates s h z.1 z.2 i) ∧
    normalEquations s h (angleCovector t) z=0}

private theorem covector_ne (t : ℝ) : angleCovector t ≠ 0 := by
  intro h
  have X := congrFun h 1
  have Y := congrFun h 2
  change -sin t=0 at X
  change cos t=0 at Y
  nlinarith only [sin_sq_add_cos_sq t,X,Y]

private theorem covector_mass (t : ℝ) : ∑ i, angleCovector t i=0 := by
  simp [angleCovector,Fin.sum_univ_three]; ring

private theorem equations_scale (s h : ℝ) (p : Plane) (c : Triple) (k : ℝ) :
    normalEquations s h (k • c) p=k • normalEquations s h c p := by
  apply Prod.ext <;> dsimp [normalEquations] <;> simp [Fin.sum_univ_three] <;> ring

theorem normalFiber_one (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    (normalFiber s h c t).encard=1 := by
  let S (a : ℝ) := (1-a)/2+a*s
  let H (a : ℝ) := (1-a)*(sqrt 3/2)+a*h
  let T (a : ℝ) := (1-a)*(π/4)+a*t
  have ph (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : H a ≠ 0 := by
    dsimp [H]
    by_cases e : a=0
    · subst a; norm_num
    · have := mul_pos (lt_of_le_of_ne ha.1 (Ne.symm e)) hh
      linarith only [this,mul_nonneg (sub_nonneg.mpr ha.2) (show 0 ≤ sqrt 3/2 by positivity)]
  have sign (i : Fin 3) : chamberSigns c i ≠ 0 := by
    fin_cases c <;> fin_cases i <;> norm_num [chamberSigns]
  have path := normal_path_count S H (fun a => angleCovector (T a)) (chamberSigns c)
    (by dsimp [S]; fun_prop) (by dsimp [H]; fun_prop) (by intro i; fin_cases i <;> dsimp [angleCovector,T] <;> fun_prop)
    ph sign (fun a _ => covector_ne _) (fun _ => covector_mass _)
  have k : angleCovector (π/4) = (sqrt 2/2) • baseCovector := by
    ext i
    fin_cases i <;> simp [angleCovector,baseCovector,sin_pi_div_four,cos_pi_div_four]
  dsimp only at path
  simp only [S,H,T,sub_zero,sub_self,zero_mul,one_mul,zero_div,zero_add,add_zero] at path
  unfold normalFiber
  rw [← path]
  simp only [k,equations_scale,smul_eq_zero,
    show sqrt 2/2 ≠ 0 by positivity,false_or]
  exact (congrArg Set.encard (base_normal_fiber c)).trans (encard_singleton _)

private theorem uniqueNormal (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    ∃ p, normalFiber s h c t={p} := Set.encard_eq_one.mp (normalFiber_one s h hh c t)

def oval (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) : Plane :=
  (uniqueNormal s h hh c t).choose

theorem normalFiber_eq (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    normalFiber s h c t={oval s h hh c t} := (uniqueNormal s h hh c t).choose_spec

theorem oval_periodic (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    Function.Periodic (oval s h hh c) π := by
  intro t
  have k : angleCovector (t+π)=(-1:ℝ) • angleCovector t := by
    ext i; fin_cases i <;> simp [angleCovector]
    ring
  have eq : normalFiber s h c (t+π)=normalFiber s h c t := by
    ext p
    simp only [normalFiber,mem_ofPred_eq,k,equations_scale]
    simp
  simpa only [normalFiber_eq s h hh c,singleton_eq_singleton_iff] using eq

end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum.Chart

/-- The uniquely selected root is smooth in the angle. Neighborhoods from
the implicit function theorem agree with the selection by fiber uniqueness. -/
theorem oval_C1 (s h : ℝ) (hh : 0<h) (c : Fin 4) : ContDiff ℝ 1 (oval s h hh c) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  let γ := oval s h hh c
  let G (p : ℝ × Plane) := normalEquations s h (angleCovector p.1) p.2
  let p := (t,γ t)
  have root (u : ℝ) : γ u ∈ normalFiber s h c u := by rw [normalFiber_eq s h hh c]; rfl
  have side := (root t).1
  have zero : G p=0 := (root t).2
  have hl i := right_ne_zero_of_mul (side i).ne'
  have sm : ContDiffAt ℝ 1 G p :=
    family_smooth (fun _ => s) (fun _ => h) angleCovector p contDiffAt_const contDiffAt_const
      (by intro i; fin_cases i <;> dsimp [angleCovector] <;> fun_prop) hh.ne' hl
  let B := (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ Plane)
  have slice : HasFDerivAt (fun x => G (t,x)) B (γ t) :=
    (sm.differentiableAt (by simp)).hasFDerivAt.comp (γ t)
      ((hasFDerivAt_const t (γ t)).prodMk (hasFDerivAt_id (γ t)))
  have inj : Function.Injective B := slice.fderiv ▸
    normalEquations_regular s h (γ t) (angleCovector t) hh.ne' hl (covector_ne _) (covector_mass _) zero
  let e := (LinearEquiv.ofBijective B.toLinearMap
    ⟨inj,LinearMap.injective_iff_surjective.mp inj⟩).toContinuousLinearEquiv
  have inv : B.IsInvertible := ⟨e,rfl⟩
  let f := sm.implicitFunction (by simp) inv
  have cf : ContDiffAt ℝ 1 f t := sm.contDiffAt_implicitFunction (by simp) inv
  have atp : f t=γ t := sm.implicitFunction_apply_self (by simp) inv
  have near (i : Fin 3) : ∀ᶠ u in 𝓝 t, 0 < chamberSigns c i*coordinates s h (f u).1 (f u).2 i := by
    have pos := side i
    rw [← atp] at pos
    have H : ContinuousAt (fun u => chamberSigns c i*coordinates s h (f u).1 (f u).2 i) t := by
      have := cf.continuousAt
      fin_cases i <;> dsimp [coordinates] <;> fun_prop
    exact continuousAt_const.eventually_lt H pos
  apply cf.congr_of_eventuallyEq
  filter_upwards [Filter.eventually_all.mpr near,sm.eventually_apply_implicitFunction (by simp) inv] with u hu hG
  have inc : f u ∈ normalFiber s h c u := ⟨hu,hG.trans zero⟩
  rw [normalFiber_eq s h hh c] at inc
  exact Eq.symm inc

private theorem has_annihilator (L : Plane →L[ℝ] Plane)
    (d : (L (1,0)).1*(L (0,1)).2-(L (0,1)).1*(L (1,0)).2=0) :
    ∃ t, ∀ w, -sin t*(L w).1+cos t*(L w).2=0 := by
  let u := L (1,0)
  let v := L (0,1)
  have extend (t : ℝ) (e : -sin t*u.1+cos t*u.2=0) (f : -sin t*v.1+cos t*v.2=0) :
      ∀ w, -sin t*(L w).1+cos t*(L w).2=0 := by
    rintro ⟨a,b⟩
    have h : L (a,b)=a • u+b • v := by
      rw [← L.map_smul a (1,0),← L.map_smul b (0,1),← map_add]
      simp
    rw [h]
    change -sin t*(a*u.1+b*v.1)+cos t*(a*u.2+b*v.2)=0
    linear_combination a*e+b*f
  have angle (u : Plane) (nz : u ≠ 0) :
      ∃ t k, k ≠ 0 ∧ k*cos t=u.1 ∧ k*sin t=u.2 := by
    let z : ℂ := ⟨u.1,u.2⟩
    have ne : z ≠ 0 := fun h => nz (Prod.ext (congrArg Complex.re h) (congrArg Complex.im h))
    exact ⟨z.arg,‖z‖,norm_ne_zero_iff.mpr ne,Complex.norm_mul_cos_arg z,Complex.norm_mul_sin_arg z⟩
  change u.1*v.2-v.1*u.2=0 at d
  by_cases hu : u=0
  · by_cases hv : v=0
    · exact ⟨0,extend _ (by simp [hu]) (by simp [hv])⟩
    obtain ⟨t,k,nk,e,f⟩ := angle v hv
    exact ⟨t,extend t (by simp [hu]) (by rw [← e,← f]; ring)⟩
  obtain ⟨t,k,nk,e,f⟩ := angle u hu
  refine ⟨t,extend t (by rw [← e,← f]; ring) ?_⟩
  apply (mul_eq_zero_iff_left nk).mp
  linear_combination d+v.2*e-v.1*f

theorem oval_range (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    range (oval s h hh c) =
      {z | (∀ i, 0 < chamberSigns c i*coordinates s h z.1 z.2 i) ∧ detH s h z.1 z.2=0} := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    have mem : oval s h hh c t ∈ normalFiber s h c t := by rw [normalFiber_eq s h hh c]; rfl
    exact ⟨mem.1,normalEquations_det_zero _ _ _ _ hh.ne' (fun i => right_ne_zero_of_mul (mem.1 i).ne')
      (covector_ne t) (covector_mass t) mem.2⟩
  · rintro ⟨side,crit⟩
    have hl i := right_ne_zero_of_mul (side i).ne'
    have hr i := (radii_pos_of_chamber s h z hh.ne' hl i).ne'
    have d := (critical_iff s h z.1 z.2 hh.ne' hl hr).mpr crit
    obtain ⟨t,ann⟩ := has_annihilator _ d
    have mem : z ∈ normalFiber s h c t := ⟨side,
      (normalEquations_zero_iff s h (angleCovector t) z (covector_mass t) hl hr).mpr ann⟩
    rw [normalFiber_eq s h hh c] at mem
    exact ⟨t,Eq.symm mem⟩

theorem boundary_preconnected (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    IsPreconnected {z : Plane | (∀ i, 0 < chamberSigns c i*coordinates s h z.1 z.2 i) ∧
      detH s h z.1 z.2=0} := by
  rw [← oval_range s h hh c]
  exact isPreconnected_range (oval_C1 s h hh c).continuous

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section

namespace MaxwellCausticExtremum.Chart

theorem chargeMap_fderiv_ne (s h : ℝ) (z : Plane) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h z.1 z.2 i ≠ 0) : fderiv ℝ (chargeMap s h) z ≠ 0 := by
  let l := coordinates s h z.1 z.2
  let r := radii s h z.1 z.2
  let X := dx s z.1
  let Y := dy h z.2
  have hr i : r i ≠ 0 := (radii_pos_of_chamber s h z hh hl i).ne'
  intro e
  have H (u v : ℝ) := charge_differential s h z.1 z.2 u v hh hl
  have zv (u v : ℝ) := chargeMap_fderiv s h z.1 z.2 u v hl hr
  simp only [e,zero_apply] at zv
  have f (u v : ℝ) := congrArg Prod.fst (zv u v)
  have g (u v : ℝ) := congrArg Prod.snd (zv u v)
  dsimp only [Prod.fst_zero,Prod.snd_zero] at f g
  have a := (H 1 0).1
  have b := (H 0 1).2
  simp only [← f,← g,mul_zero,mul_one,add_zero,zero_add] at a b
  have trace (i : Fin 3) : l i/r i*X i*X i+l i/r i*Y i*Y i=l i := by
    have id : r i=X i^2+Y i^2 := radii_eq .. 
    field_simp [hr i]; linear_combination -l i*id
  have m := (bary_moments s h z hh).1
  change ∑ i, l i=1 at m
  change 0=3*(∑ i, l i/r i*X i*X i)-1 at a
  change 0=3*(∑ i, l i/r i*Y i*Y i)-1 at b
  simp only [Fin.sum_univ_three] at a b m
  linarith only [a,b,m,trace 0,trace 1,trace 2]

end MaxwellCausticExtremum.Chart

end
end

section

open Set

namespace MaxwellCausticExtremum.Arc

private theorem two_stationary {a b : ℝ} (hab : a < b) (f g speed slope : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc a b))
    (df : ∀ t ∈ Ioo a b, HasDerivAt f (speed t) t)
    (dg : ∀ t ∈ Ioo a b, HasDerivAt g (slope t * speed t) t)
    (hs : InjOn slope (Ioo a b)) (ef : f a = f b) (eg : g a = g b) :
    ∃ t ∈ Ioo a b, ∃ u ∈ Ioo a b, t ≠ u ∧ speed t = 0 ∧ speed u = 0 := by
  obtain ⟨m,hm,em⟩ := exists_hasDerivAt_eq_zero hab hf ef df
  have left : Ioo a m ⊆ Ioo a b := fun _ ht => ⟨ht.1,ht.2.trans hm.2⟩
  have right : Ioo m b ⊆ Ioo a b := fun _ ht => ⟨hm.1.trans ht.1,ht.2⟩
  have lc : Icc a m ⊆ Icc a b := fun _ ht => ⟨ht.1,ht.2.trans hm.2.le⟩
  have rc : Icc m b ⊆ Icc a b := fun _ ht => ⟨hm.1.le.trans ht.1,ht.2⟩
  by_cases he : f a = f m
  · obtain ⟨t,ht,e⟩ := exists_hasDerivAt_eq_zero hm.1 (hf.mono lc) he
      (fun t ht => df t (left ht))
    exact ⟨t,left ht,m,hm,ht.2.ne,e,em⟩
  obtain ⟨t,ht,et⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f speed hm.1 (hf.mono lc)
    (fun t ht => df t (left ht)) g (fun t => slope t*speed t) (hg.mono lc)
    (fun t ht => dg t (left ht))
  obtain ⟨u,hu,eu⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f speed hm.2 (hf.mono rc)
    (fun t ht => df t (right ht)) g (fun t => slope t*speed t) (hg.mono rc)
    (fun t ht => dg t (right ht))
  by_cases hst : speed t = 0
  · exact ⟨t,left ht,m,hm,ht.2.ne,hst,em⟩
  by_cases hsu : speed u = 0
  · exact ⟨m,hm,u,right hu,hu.1.ne,em,hsu⟩
  rw [← ef, ← eg] at eu
  rw [← mul_assoc] at et eu
  have et' := mul_right_cancel₀ hst et
  have eu' := mul_right_cancel₀ hsu eu
  have same : (f m-f a)*slope t = (f m-f a)*slope u := by linarith
  exact (ht.2.trans hu.1).ne.elim
    (hs (left ht) (right hu) (mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm he)) same))

/-- A periodic curve with at most three stationary parameters per period is
simple if the tangent slopes are injective in a suitable frame on each proper
arc. The frame may depend on both endpoints. -/
theorem injective_of_three_stationary
    (F V : ℝ → ℝ × ℝ) (p : ℝ) (period : Function.Periodic F p)
    (diff : ∀ t, HasDerivAt F (V t) t)
    (count : ∀ a, {t ∈ Ioo a (a+p) | V t = 0}.encard ≤ 3)
    (charts : ∀ a b : ℝ, a < b → b < a+p →
      ∃ (L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)) (s m : ℝ → ℝ), InjOn m (Ioo a b) ∧
        ∀ t ∈ Ioo a b, L (V t) = (s t,m t*s t)) :
    ∀ a, InjOn F (Ico a (a+p)) := by
  have arc {a b : ℝ} (hab : a < b) (hbp : b < a+p) (he : F a = F b) :
      ∃ t ∈ Ioo a b, ∃ u ∈ Ioo a b, t ≠ u ∧ V t = 0 ∧ V u = 0 := by
    obtain ⟨L,s,m,hm,hL⟩ := charts a b hab hbp
    let f (t : ℝ) := (L (F t)).1
    let g (t : ℝ) := (L (F t)).2
    have d (t : ℝ) := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (diff t)
    have df (t : ℝ) : HasDerivAt f (L (V t)).1 t :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (d t)
    have dg (t : ℝ) : HasDerivAt g (L (V t)).2 t :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (d t)
    obtain ⟨t,ht,u,hu,hne,zt,zu⟩ := two_stationary hab f g s m
      (fun t _ => (df t).continuousAt.continuousWithinAt)
      (fun t _ => (dg t).continuousAt.continuousWithinAt)
      (fun t ht => by simpa only [hL t ht] using df t)
      (fun t ht => by simpa only [hL t ht] using dg t)
      hm (congrArg (fun z => (L z).1) he) (congrArg (fun z => (L z).2) he)
    have zero (t : ℝ) (ht : t ∈ Ioo a b) (hz : s t = 0) : V t = 0 := by
      apply L.injective
      rw [hL t ht,hz,mul_zero,map_zero]
      rfl
    exact ⟨t,ht,u,hu,hne,zero t ht zt,zero u hu zu⟩
  have noReturn (a b : ℝ) (hab : a < b) (hbp : b < a+p) (he : F a = F b) : False := by
    obtain ⟨t,ht,u,hu,htu,zt,zu⟩ := arc hab hbp he
    obtain ⟨v,hv,w,hw,hvw,zv,zw⟩ := arc hbp (by linarith) (he.symm.trans (period a).symm)
    let S : Set ℝ := {t,u,v,w}
    have four : S.encard = 4 := Set.encard_eq_four.mpr
      ⟨t,u,v,w,htu,(ht.2.trans hv.1).ne,(ht.2.trans hw.1).ne,
        (hu.2.trans hv.1).ne,(hu.2.trans hw.1).ne,hvw,rfl⟩
    have sub : S ⊆ {z ∈ Ioo a (a+p) | V z = 0} := by
      rintro z (rfl|rfl|rfl|rfl)
      · exact ⟨⟨ht.1,ht.2.trans hbp⟩,zt⟩
      · exact ⟨⟨hu.1,hu.2.trans hbp⟩,zu⟩
      · exact ⟨⟨hab.trans hv.1,hv.2⟩,zv⟩
      · exact ⟨⟨hab.trans hw.1,hw.2⟩,zw⟩
    have bound := (Set.encard_le_encard sub).trans (count a)
    rw [four] at bound
    norm_num at bound
  intro a x hx y hy he
  rcases lt_trichotomy x y with h|h|h
  · exact (noReturn x y h (by linarith [hx.1,hy.2]) he).elim
  · exact h
  · exact (noReturn y x h (by linarith [hy.1,hx.2]) he.symm).elim

end MaxwellCausticExtremum.Arc

namespace MaxwellCausticExtremum.Arc

open Real

private noncomputable def turnFrame (c : ℝ) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
  { toFun := fun p => (cos c*p.1+sin c*p.2,cos c*p.2-sin c*p.1)
    invFun := fun p => (cos c*p.1-sin c*p.2,cos c*p.2+sin c*p.1)
    left_inv := by
      rintro ⟨x,y⟩
      apply Prod.ext <;> dsimp
      · linear_combination x * sin_sq_add_cos_sq c
      · linear_combination y * sin_sq_add_cos_sq c
    right_inv := by
      rintro ⟨x,y⟩
      apply Prod.ext <;> dsimp
      · linear_combination x * sin_sq_add_cos_sq c
      · linear_combination y * sin_sq_add_cos_sq c
    map_add' := by intro x y; apply Prod.ext <;> dsimp <;> ring
    map_smul' := by intro a x; apply Prod.ext <;> dsimp <;> ring }

/-- With the tangent line itself as angular parameter, the slope charts are
automatic even at a cusp, where the velocity vanishes. -/
theorem injective_in_angle_parameter (F V : ℝ → ℝ × ℝ) (period : Function.Periodic F π)
    (diff : ∀ t, HasDerivAt F (V t) t)
    (count : ∀ a, {t ∈ Ioo a (a+π) | V t = 0}.encard ≤ 3)
    (direction : ∀ t, ∃ k : ℝ, V t = (k*cos t,k*sin t)) :
    ∀ a, InjOn F (Ico a (a+π)) := by
  apply injective_of_three_stationary F V π period diff count
  intro a b _ hb
  let c := (a+b)/2
  have arc {t : ℝ} (ht : t ∈ Ioo a b) : t-c ∈ Ioo (-(π/2)) (π/2) := by
    dsimp [c]
    constructor <;> linarith [ht.1,ht.2]
  refine ⟨turnFrame c,fun t => (turnFrame c (V t)).1,fun t => tan (t-c),?_,?_⟩
  · intro x hx y hy he
    linarith only [strictMonoOn_tan.injOn (arc hx) (arc hy) he]
  · intro t ht
    obtain ⟨k,hk⟩ := direction t
    dsimp only
    rw [hk]
    apply Prod.ext
    · rfl
    · change cos c*(k*sin t)-sin c*(k*cos t) =
        tan (t-c)*(cos c*(k*cos t)+sin c*(k*sin t))
      have hc := (cos_pos_of_mem_Ioo (arc ht)).ne'
      rw [show cos c*(k*cos t)+sin c*(k*sin t) = k*cos (t-c) by
        rw [cos_sub]; ring,tan_eq_sin_div_cos]
      field_simp [hc]
      rw [sin_sub]
      ring

end MaxwellCausticExtremum.Arc

end

section

noncomputable section
open Set Real

namespace MaxwellCausticExtremum.Chart

private theorem annihilates (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    let z := oval s h hh c t
    ∀ w : Plane, -sin t*(fderiv ℝ (chargeMap s h) z w).1+cos t*(fderiv ℝ (chargeMap s h) z w).2=0 := by
  have hmem : oval s h hh c t ∈ normalFiber s h c t := by rw [normalFiber_eq s h hh c]; rfl
  have hl i := right_ne_zero_of_mul (hmem.1 i).ne'
  have mass : ∑ i, angleCovector t i=0 := by simp [angleCovector,Fin.sum_univ_three]; ring
  exact (normalEquations_zero_iff s h (angleCovector t) _ mass hl
    (fun i => (radii_pos_of_chamber s h _ hh.ne' hl i).ne')).mp hmem.2

theorem oval_injective_period (s h : ℝ) (hh : 0<h) (c : Fin 4) (q : ℝ) :
    InjOn (oval s h hh c) (Ico q (q+π)) := by
  let γ := oval s h hh c
  have apart (a b : ℝ) (hab : a<b) (bound : b<a+π) (eq : γ a=γ b) : False := by
    let L := fderiv ℝ (chargeMap s h) (γ b)
    have A := annihilates s h hh c a
    change ∀ w, -sin a*(fderiv ℝ (chargeMap s h) (γ a) w).1+cos a*(fderiv ℝ (chargeMap s h) (γ a) w).2=0 at A
    rw [eq] at A
    have B := annihilates s h hh c b
    have nz : sin b*cos a-cos b*sin a ≠ 0 := by
      rw [← sin_sub]
      exact (sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)).ne'
    have side : γ b ∈ normalFiber s h c b := by rw [normalFiber_eq s h hh c]; rfl
    apply chargeMap_fderiv_ne s h (γ b) hh.ne' (fun i => right_ne_zero_of_mul (side.1 i).ne')
    apply ContinuousLinearMap.ext
    intro w
    apply Prod.ext
    · change (L w).1=0
      apply (mul_eq_zero_iff_left nz).mp
      linear_combination cos b*A w-cos a*B w
    · change (L w).2=0
      apply (mul_eq_zero_iff_left nz).mp
      linear_combination sin b*A w-sin a*B w
  intro a ha b hb eq
  rcases lt_trichotomy a b with e|e|e
  · exact (apart a b e (by linarith [hb.2,ha.1]) eq).elim
  · exact e
  · exact (apart b a e (by linarith [ha.2,hb.1]) eq.symm).elim

theorem oval_velocity_ne (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    deriv (oval s h hh c) t ≠ 0 := by
  let γ := oval s h hh c
  let F := chargeMap s h
  let D := fderiv ℝ F (γ t)
  have root : γ t ∈ normalFiber s h c t := by rw [normalFiber_eq s h hh c]; rfl
  have hl i := right_ne_zero_of_mul (root.1 i).ne'
  have hr i := (radii_pos_of_chamber s h _ hh.ne' hl i).ne'
  have sm := chargeMap_smooth s h (γ t) hl hr
  intro zero
  have dg : HasDerivAt γ 0 t := zero ▸ ((oval_C1 s h hh c).differentiable (by simp) t).hasDerivAt
  apply chargeMap_fderiv_ne s h (γ t) hh.ne' hl
  apply ContinuousLinearMap.ext
  intro w
  let K (u : ℝ) := fderiv ℝ F (γ u) w
  have derivativeMap : DifferentiableAt ℝ (fun z => fderiv ℝ F z w) (γ t) := by
    have a : ContDiffAt ℝ 1 (fderiv ℝ F) (γ t) := sm.fderiv_right (by simp)
    exact (a.clm_apply contDiffAt_const).differentiableAt (by simp)
  have dk : HasDerivAt K 0 t := by
    exact (derivativeMap.hasFDerivAt.comp_hasDerivAt t dg).congr_deriv (map_zero _)
  have dk1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dk
  have dk2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dk
  have ann (u : ℝ) : -sin u*(K u).1+cos u*(K u).2=0 := annihilates s h hh c u w
  have rv := (((hasDerivAt_sin t).neg.mul dk1).add ((hasDerivAt_cos t).mul dk2)).unique
    (show HasDerivAt (fun u => -sin u*(K u).1+cos u*(K u).2) 0 t by simp_rw [ann]; exact hasDerivAt_const _ _)
  simp only [map_zero,mul_zero,add_zero] at rv
  change -cos t*(K t).1+(-sin t)*(K t).2=0 at rv
  have e : -cos t*(K t).1-sin t*(K t).2=0 := by linarith only [rv]
  apply Prod.ext
  · change (K t).1=0
    linear_combination -sin t*ann t-cos t*e-(K t).1*sin_sq_add_cos_sq t
  · change (K t).2=0
    linear_combination cos t*ann t-sin t*e-(K t).2*sin_sq_add_cos_sq t

end MaxwellCausticExtremum.Chart

end
end

section

noncomputable section
open Set Filter Topology
namespace MaxwellCausticExtremum.Chart.Cusp

theorem det_zero (s h : ℝ) (w : State) (hh : h ≠ 0)
    (hl : ∀ i, coordinates s h w.1.1 w.1.2 i ≠ 0) (eq : equations s h w=0) :
    detH s h w.1.1 w.1.2=0 := by
  let l := coordinates s h w.1.1 w.1.2
  let p := MaxwellCusp.Spatial.siteDx s w.1.1
  let q := MaxwellCusp.Spatial.siteDy h w.1.2
  let r := radiusAt s h w.1
  let x := X s h w
  let y := Y s h w
  let a := w.2.1
  let k := w.2.2
  have norm : a^2+k^2=1 := sub_eq_zero.mp (congrArg (fun z : State => z.1.1) eq)
  have xx : ∑ i, l i*x i^2=1/3 := sub_eq_zero.mp (congrArg (fun z : State => z.1.2) eq)
  have xy : ∑ i, l i*x i*y i=0 := congrArg (fun z : State => z.2.1) eq
  have P i : p i= -dx s w.1.1 i := by fin_cases i <;> dsimp [dx,p,MaxwellCusp.Spatial.siteDx] <;> ring
  have Q i : q i= -dy h w.1.2 i := by fin_cases i <;> dsimp [dy,q,MaxwellCusp.Spatial.siteDy] <;> ring
  have hr i := radii_pos_of_chamber s h w.1 hh hl i
  have nr i : r i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have rad i : r i^2=p i^2+q i^2 := (Real.sq_sqrt (hr i).le).trans (by rw [P,Q,radii_eq]; ring)
  have rx i : MaxwellCusp.Spatial.rot p q a k i=r i*x i := by
    dsimp [MaxwellCusp.Spatial.rot,x,X]; rw [P,Q]; change _=r i*(_/r i); field_simp [nr i]; ring
  have ry i : MaxwellCusp.Spatial.rot p q (-k) a i=r i*y i := by
    dsimp [MaxwellCusp.Spatial.rot,y,Y]; rw [P,Q]; change _=r i*(_/r i); field_simp [nr i]; ring
  change MaxwellCusp.Spatial.chartHessian s h w.1.1 w.1.2=0
  rw [MaxwellCusp.Spatial.chartHessian_eq]
  change MaxwellCusp.Spatial.gramDet (fun i => l i/(p i^2+q i^2)) p q=0
  rw [← MaxwellCusp.Spatial.gramDet_rotation _ _ _ a k norm]
  have form (f g : Triple) : MaxwellCusp.Spatial.gram (fun i => l i/(p i^2+q i^2))
      (fun i => r i*f i) (fun i => r i*g i) = ∑ i, l i*f i*g i := by
    apply Finset.sum_congr rfl; intro i _
    dsimp only; rw [← rad]; field_simp [nr i]
  unfold MaxwellCusp.Spatial.gramDet
  rw [funext rx,funext ry,form,form,form,xy,show (∑ i, l i*x i*x i)=1/3 by simpa only [pow_two,mul_assoc] using xx]
  ring

theorem equations_smooth (s h : ℝ → ℝ) (p : ℝ × State)
    (hs : ContDiffAt ℝ 1 s p.1) (ht : ContDiffAt ℝ 1 h p.1) (hh : h p.1 ≠ 0)
    (hl : ∀ i, coordinates (s p.1) (h p.1) p.2.1.1 p.2.1.2 i ≠ 0) :
    ContDiffAt ℝ 1 (fun w : ℝ × State => equations (s w.1) (h w.1) w.2) p := by
  have S : ContDiffAt ℝ 1 (fun w : ℝ × State => s w.1) p := hs.comp p contDiffAt_fst
  have H : ContDiffAt ℝ 1 (fun w : ℝ × State => h w.1) p := ht.comp p contDiffAt_fst
  have L i : ContDiffAt ℝ 1 (fun w : ℝ × State => coordinates (s w.1) (h w.1) w.2.1.1 w.2.1.2 i) p := by
    fin_cases i <;> dsimp [coordinates] <;> fun_prop (disch := exact hh)
  have hr i := radii_pos_of_chamber _ _ p.2.1 hh hl i
  have R i : ContDiffAt ℝ 1 (fun w : ℝ × State => radiusAt (s w.1) (h w.1) w.2.1 i) p := by
    have d : ContDiffAt ℝ 1 (fun w : ℝ × State => radii (s w.1) (h w.1) w.2.1.1 w.2.1.2 i) p := by
      fin_cases i <;> dsimp [radii] <;> fun_prop
    exact d.sqrt (hr i).ne'
  have nr i : radiusAt (s p.1) (h p.1) p.2.1 i ≠ 0 := (Real.sqrt_pos.mpr (hr i)).ne'
  have dx' i : ContDiffAt ℝ 1 (fun w : ℝ × State => dx (s w.1) w.2.1.1 i) p := by
    fin_cases i <;> dsimp [dx] <;> fun_prop
  have dy' i : ContDiffAt ℝ 1 (fun w : ℝ × State => dy (h w.1) w.2.1.2 i) p := by
    fin_cases i <;> dsimp [dy] <;> fun_prop
  have x i : ContDiffAt ℝ 1 (fun w : ℝ × State => X (s w.1) (h w.1) w.2 i) p := by
    unfold X; fun_prop (disch := exact nr i)
  have y i : ContDiffAt ℝ 1 (fun w : ℝ × State => Y (s w.1) (h w.1) w.2 i) p := by
    unfold Y; fun_prop (disch := exact nr i)
  unfold equations MaxwellCusp.Spatial.cubicNull
  dsimp only
  fun_prop (disch := exact nr _)

def fiber (s h : ℝ) (sign : Triple) := {w : State |
  (∀ i, 0 < sign i*coordinates s h w.1.1 w.1.2 i) ∧ equations s h w=0}

set_option maxHeartbeats 1000000 in
theorem cusp_path_count (s h : ℝ → ℝ) (sign : Triple) (hs : ContDiff ℝ 1 s) (ht : ContDiff ℝ 1 h)
    (height : ∀ t ∈ Icc (0:ℝ) 1, h t ≠ 0) (signs : ∀ i, sign i ≠ 0) :
    (fiber (s 0) (h 0) sign).encard=(fiber (s 1) (h 1) sign).encard := by
  let base (p : ℝ × State) : ℝ × Plane := (p.1,p.2.1)
  let U := {p : ℝ × State | h p.1 ≠ 0 ∧
    ∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1.1 p.2.1.2 i}
  have op : IsOpen U := (path_chamber_open s h sign hs.continuous ht.continuous).preimage
    (show Continuous base by dsimp [base]; fun_prop)
  let G (p : ℝ × State) := equations (s p.1) (h p.1) p.2
  have sm (p : ℝ × State) (hp : p ∈ U) : ContDiffAt ℝ 1 G p := equations_smooth s h p
    hs.contDiffAt ht.contDiffAt hp.1 (fun i => right_ne_zero_of_mul (hp.2 i).ne')
  let T := {p : ℝ × Plane | p.1 ∈ Icc (0:ℝ) 1 ∧
    (∀ i, 0 < sign i*coordinates (s p.1) (h p.1) p.2.1 p.2.2 i) ∧
    0 ≤ detH (s p.1) (h p.1) p.2.1 p.2.2}
  let box : Set Plane := Icc (-1:ℝ) 1 ×ˢ Icc (-1:ℝ) 1
  let D := T ×ˢ box
  have cp : IsCompact D := (path_sheet_compact s h sign hs.continuous ht.continuous height signs).prod
    (isCompact_Icc.prod isCompact_Icc)
  let := isCompact_iff_compactSpace.mp cp
  let map (v : D) : ℝ × State := (v.val.1.1,v.val.1.2,v.val.2)
  have cm : Continuous map := by dsimp [map]; fun_prop
  have hu (v : D) : map v ∈ U := ⟨height _ v.2.1.1,v.2.1.2.1⟩
  have cG : Continuous (G ∘ map) := continuous_iff_continuousAt.mpr
    (fun v => (sm _ (hu v)).continuousAt.comp cm.continuousAt)
  have compact : IsCompact {p : ℝ × State | p.1 ∈ Icc 0 1 ∧ p ∈ U ∧ G p=0} := by
    have cs := (isClosed_eq cG (g := fun _ => (0:State)) continuous_const).isCompact.image cm
    refine (show map '' {q : D | G (map q)=0} = {p : ℝ × State | p.1 ∈ Icc 0 1 ∧ p ∈ U ∧ G p=0} from ?_) ▸ cs
    ext p
    symm
    constructor
    · rintro ⟨hi,hin,hg⟩
      have eq := det_zero (s p.1) (h p.1) p.2 hin.1 (fun i => right_ne_zero_of_mul (hin.2 i).ne') hg
      have unit : p.2.2.1^2+p.2.2.2^2=1 := sub_eq_zero.mp (congrArg (fun z : State => z.1.1) hg)
      have ht' : (p.1,p.2.1) ∈ T := ⟨hi,hin.2,eq.ge⟩
      have hb : p.2.2 ∈ box := by
        refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩ <;> nlinarith only [unit,sq_nonneg p.2.2.1,sq_nonneg p.2.2.2]
      exact ⟨⟨((p.1,p.2.1),p.2.2),ht',hb⟩,hg,rfl⟩
    · rintro ⟨v,hv,rfl⟩; exact ⟨v.2.1.1,hu v,hv⟩
  have reg (p : ℝ × State) (hp : p ∈ U) (_ : p.1 ∈ Icc (0:ℝ) 1) (eq : G p=0) :
      Function.Injective (fderiv ℝ (fun x => G (p.1,x)) p.2) := by
    exact equations_regular (s p.1) (h p.1) p.2 hp.1 (fun i => right_ne_zero_of_mul (hp.2 i).ne') eq
  have count := Transport.open_path_count (E := State) U op G compact sm reg
  simpa [U,G,fiber,height 0 (by simp),height 1 (by simp)] using count

end MaxwellCausticExtremum.Chart.Cusp

end
end

section

noncomputable section
open Set
namespace MaxwellCausticExtremum.Chart.Cusp

def source (s h : ℝ) (sign : Triple) := Prod.fst '' fiber s h sign

theorem opposite_iff (s h : ℝ) (p n : Plane) :
    equations s h (p,-n)=0 ↔ equations s h (p,n)=0 := by
  have x (i : Fin 3) : X s h (p,-n) i= -X s h (p,n) i := by dsimp [X]; ring
  have y (i : Fin 3) : Y s h (p,-n) i= -Y s h (p,n) i := by dsimp [Y]; ring
  have cub : MaxwellCusp.Spatial.cubicNull (coordinates s h p.1 p.2) (radiusAt s h p) (X s h (p,-n)) =
      -MaxwellCusp.Spatial.cubicNull (coordinates s h p.1 p.2) (radiusAt s h p) (X s h (p,n)) := by
    simp [MaxwellCusp.Spatial.cubicNull,Fin.sum_univ_three,x]; ring
  simp only [equations,Prod.fst_neg,Prod.snd_neg,neg_sq,x,y,mul_neg,neg_mul,neg_neg,Prod.ext_iff,
    Prod.fst_zero,Prod.snd_zero,cub,neg_eq_zero]

private theorem two_axes (L : Plane →L[ℝ] Plane) (nz : L ≠ 0) (n m : Plane)
    (kn : L n=0) (km : L m=0) (un : n.1^2+n.2^2=1) (um : m.1^2+m.2^2=1) :
    m=n ∨ m= -n := by
  let d := n.1*m.2-n.2*m.1
  have par : d=0 := by
    by_contra hd
    apply nz; apply ContinuousLinearMap.ext; intro w
    let a := (m.2*w.1-m.1*w.2)/d
    let b := (-n.2*w.1+n.1*w.2)/d
    have e : w=a • n+b • m := by
      apply Prod.ext <;> dsimp [a,b] <;> field_simp [hd] <;> dsimp [d] <;> ring
    simp [e,kn,km]
  let k := m.1*n.1+m.2*n.2
  have e : m=k • n := by
    apply Prod.ext <;> dsimp [k,d] at *
    · linear_combination -m.1*un-n.2*par
    · linear_combination -m.2*un+n.1*par
  have sq : k^2=1 := by
    rw [e] at um; dsimp at um
    linear_combination um-k^2*un
  rcases mul_eq_zero.mp (show (k-1)*(k+1)=0 by linarith only [sq]) with a|a
  · left; simpa [show k=1 by linarith] using e
  · right; simpa [show k= -1 by linarith] using e

theorem fiber_pair_count (s h : ℝ) (hh : h ≠ 0) (sign : Triple) :
    (fiber s h sign).encard = (source s h sign).encard*2 := by
  classical
  let S := source s h sign
  have ex (p : S) : ∃ n : Plane, (p.val,n) ∈ fiber s h sign := by
    obtain ⟨w,hw,he⟩ := p.property
    exact ⟨w.2,he ▸ hw⟩
  let a (p : S) := (ex p).choose
  have root (p : S) := (ex p).choose_spec
  let f (p : S × Bool) : State := (p.1.1,if p.2 then -a p.1 else a p.1)
  have fmem (p : S × Bool) : f p ∈ fiber s h sign := by
    rcases p with ⟨p,_|_⟩
    · exact root p
    · exact ⟨(root p).1,(opposite_iff ..).mpr (root p).2⟩
  have ne (p : S) : a p ≠ -a p := by
    have unit : (a p).1^2+(a p).2^2=1 := sub_eq_zero.mp (congrArg (fun z : State => z.1.1) (root p).2)
    intro e
    have e1 := congrArg Prod.fst e
    have e2 := congrArg Prod.snd e
    change (a p).1= -(a p).1 at e1
    change (a p).2= -(a p).2 at e2
    rw [show (a p).1=0 by linarith,show (a p).2=0 by linarith] at unit; norm_num at unit
  have inj : Function.Injective f := by
    rintro ⟨p,i⟩ ⟨q,j⟩ eq
    have same : p=q := Subtype.ext (congrArg Prod.fst eq)
    subst q
    cases i <;> cases j <;> first | rfl | exact (ne p (congrArg Prod.snd eq)).elim | exact (ne p (congrArg Prod.snd eq).symm).elim
  have sur : Set.range f=fiber s h sign := by
    apply Set.Subset.antisymm
    · rintro _ ⟨p,rfl⟩; exact fmem p
    · intro w hw
      let p : S := ⟨w.1,⟨w,hw,rfl⟩⟩
      have null (n : Plane) (hn : (w.1,n) ∈ fiber s h sign) :
          fderiv ℝ (chargeMap s h) w.1 n=0 ∧ n.1^2+n.2^2=1 := by
        have un : n.1^2+n.2^2=1 := sub_eq_zero.mp (congrArg (fun z : State => z.1.1) hn.2)
        have hl i := right_ne_zero_of_mul (hn.1 i).ne'
        exact ⟨(kernel_iff _ _ _ _ hh hl un).mpr
          ⟨sub_eq_zero.mp (congrArg (fun z : State => z.1.2) hn.2),congrArg (fun z : State => z.2.1) hn.2⟩,un⟩
      have A := null (a p) (root p)
      have B := null w.2 hw
      rcases two_axes _ (chargeMap_fderiv_ne _ _ _ hh (fun i => right_ne_zero_of_mul (hw.1 i).ne'))
          _ _ A.1 B.1 A.2 B.2 with pos|neg
      · exact ⟨(p,false),Prod.ext rfl pos.symm⟩
      · exact ⟨(p,true),Prod.ext rfl neg.symm⟩
  rw [← sur,← Set.image_univ,inj.encard_image,Set.encard_univ]
  simp [ENat.card_prod,S,ENat.card_eq_coe_fintype_card]
end MaxwellCausticExtremum.Chart.Cusp

end
end

section

noncomputable section
open Set Real
namespace MaxwellCausticExtremum.Chart

def imageVelocity (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) : Plane :=
  fderiv ℝ (chargeMap s h) (oval s h hh c t) (deriv (oval s h hh c) t)

theorem image_deriv (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    HasDerivAt (chargeMap s h ∘ oval s h hh c) (imageVelocity s h hh c t) t := by
  have root : oval s h hh c t ∈ normalFiber s h c t := by rw [normalFiber_eq s h hh c]; rfl
  have hl i := right_ne_zero_of_mul (root.1 i).ne'
  have sm := chargeMap_smooth s h (oval s h hh c t) hl (fun i => (radii_pos_of_chamber _ _ _ hh.ne' hl i).ne')
  exact (sm.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((oval_C1 s h hh c).differentiable (by simp) t).hasDerivAt

private theorem collinear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] (L : Plane →L[ℝ] Y)
    (ne : L ≠ 0) (n v : Plane) (unit : n.1^2+n.2^2=1) (kn : L n=0) (kv : L v=0) :
    ∃ a : ℝ, v=a • n := by
  let d := n.1*v.2-n.2*v.1
  have eq : d=0 := by
    by_contra nz; apply ne; apply ContinuousLinearMap.ext; intro w
    let a := (v.2*w.1-v.1*w.2)/d
    let b := (-n.2*w.1+n.1*w.2)/d
    have e : w=a • n+b • v := by
      apply Prod.ext <;> dsimp [a,b] <;> field_simp [nz] <;> dsimp [d] <;> ring
    rw [e,map_add,map_smul,map_smul,kn,kv]; simp
  refine ⟨v.1*n.1+v.2*n.2,?_⟩
  apply Prod.ext <;> dsimp [d] at *
  · linear_combination -v.1*unit-n.2*eq
  · linear_combination -v.2*unit+n.1*eq

theorem velocity_zero_iff (s h : ℝ) (hh : 0<h) (c : Fin 4) (t : ℝ) :
    imageVelocity s h hh c t=0 ↔ oval s h hh c t ∈ Cusp.source s h (chamberSigns c) := by
  let γ := oval s h hh c
  let z := γ t
  let v := deriv γ t
  let F := fderiv ℝ (chargeMap s h) z
  let J (z : Plane) := detH s h z.1 z.2
  let L := fderiv ℝ J z
  have root (u : ℝ) : γ u ∈ normalFiber s h c u := by rw [normalFiber_eq s h hh c]; rfl
  have data (u : ℝ) : (∀ i, 0 < chamberSigns c i*coordinates s h (γ u).1 (γ u).2 i) ∧ J (γ u)=0 :=
    (Set.ext_iff.mp (oval_range s h hh c) (γ u)).mp ⟨u,rfl⟩
  have hl i := right_ne_zero_of_mul ((root t).1 i).ne'
  have ne : L ≠ 0 := MaxwellCusp.Spatial.chart_gradient s h z.1 z.2 hh.ne' hl (data t).2
  have dif : DifferentiableAt ℝ J z := by
    by_contra nd; exact ne (fderiv_zero_of_not_differentiableAt nd)
  have vel : HasDerivAt γ v t := ((oval_C1 s h hh c).differentiable (by simp) t).hasDerivAt
  have kv : L v=0 := (dif.hasFDerivAt.comp_hasDerivAt t vel).unique
    (show HasDerivAt (J ∘ γ) 0 t by simpa only [Function.comp_def,(data _).2] using hasDerivAt_const t (0:ℝ))
  have jet (n : Plane) (unit : n.1^2+n.2^2=1) (kn : F n=0) :
      L n=MaxwellCusp.Spatial.cubicNull (coordinates s h z.1 z.2) (Cusp.radiusAt s h z) (Cusp.X s h (z,n)) := by
    have lin (x k : ℝ) : HasDerivAt (fun u : ℝ => x+u*k) k 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).mul_const k).const_add x
    have d := dif.hasFDerivAt.comp_hasDerivAt_of_eq 0 ((lin z.1 n.1).prodMk (lin z.2 n.2)) (by simp)
    exact d.unique (Cusp.det_line_deriv s h z n hh.ne' hl unit kn)
  constructor
  · intro zero
    have nv : v ≠ 0 := oval_velocity_ne s h hh c t
    let R := sqrt (v.1^2+v.2^2)
    have hp : 0 < v.1^2+v.2^2 := by
      by_contra! e
      exact nv (Prod.ext (by change v.1=0; nlinarith [sq_nonneg v.2]) (by change v.2=0; nlinarith [sq_nonneg v.1]))
    have nr : R ≠ 0 := (sqrt_pos.mpr hp).ne'
    let n := R⁻¹ • v
    have un : n.1^2+n.2^2=1 := by
      dsimp [n]; field_simp [nr]; linarith only [show R^2=_ from sq_sqrt hp.le]
    change F v=0 at zero
    have kn : F n=0 := by simp [n,zero]
    obtain ⟨xx,xy⟩ := (Cusp.kernel_iff s h z n hh.ne' hl un).mp kn
    have cb := (jet n un kn).symm
    have kz : L n=0 := by simp [n,kv]
    rw [kz] at cb
    exact ⟨(z,n),⟨(data t).1,by
      change ((n.1^2+n.2^2-1,(_)-1/3),(_,_))=(0:Cusp.State)
      rw [un,xx,xy,cb]; simp⟩,rfl⟩
  · rintro ⟨⟨p,n⟩,hp,e⟩
    change p=z at e; subst p
    have un : n.1^2+n.2^2=1 := sub_eq_zero.mp (congrArg (fun z : Cusp.State => z.1.1) hp.2)
    have kn : F n=0 := (Cusp.kernel_iff s h z n hh.ne' hl un).mpr
      ⟨sub_eq_zero.mp (congrArg (fun z : Cusp.State => z.1.2) hp.2),congrArg (fun z : Cusp.State => z.2.1) hp.2⟩
    have Jn := (jet n un kn).trans (congrArg (fun z : Cusp.State => z.2.2) hp.2)
    obtain ⟨a,ha⟩ := collinear L ne n v un Jn kv
    change F v=0; simp [ha,kn]

end MaxwellCausticExtremum.Chart

end
end

section

namespace MaxwellCausticExtremum.Cusps

abbrev Triple := Fin 3 → ℝ

def pairSum (l : Triple) := l 0*l 1 + l 0*l 2 + l 1*l 2

def prod (l : Triple) := l 0*l 1*l 2

def pairRate (l d : Triple) :=
  d 0*(l 1+l 2)+d 1*(l 0+l 2)+d 2*(l 0+l 1)

def prodRate (l d : Triple) := d 0*l 1*l 2+l 0*d 1*l 2+l 0*l 1*d 2

def fold (a b : ℝ) := 8*a^2*(a-1)+(27*a+8)*b

/-- A nonzero tangent to the determinant locus with zero log-ratio
velocity. k is twice the common logarithmic charge velocity. -/
def cuspJet (l d : Triple) (k : ℝ) : Prop :=
  let a := pairSum l
  let b := prod l
  let u := pairRate l d
  let v := prodRate l d
  l 0+l 1+l 2=1 ∧ d 0+d 1+d 2=0 ∧ (∃ i, d i ≠ 0) ∧ (∀ i, l i ≠ 0) ∧
    fold a b=0 ∧ (24*a^2-16*a+27*b)*u+(27*a+8)*v=0 ∧
    ∀ i, (2*(1-a)-5*l i)*d i-3*l i*u = k*l i*(1-a-l i)

theorem determinant_numerator (l : Triple) (mass : l 0+l 1+l 2=1) :
    let a := pairSum l
    let r (i : Fin 3) := 1-a-l i
    27*prod l*(∑ i, l i*r i)-8*r 0*r 1*r 2 = fold a (prod l) := by
  simp only [prod,pairSum,fold,Fin.sum_univ_three]
  rw [show l 0 = 1-l 1-l 2 by linarith]
  ring

private theorem quadratic_zero (x y z A B C : ℝ) (nxy : x ≠ y) (nxz : x ≠ z) (nyz : y ≠ z)
    (a : A*x^2+B*x+C=0) (b : A*y^2+B*y+C=0) (c : A*z^2+B*z+C=0) :
    A=0 ∧ B=0 := by
  have h : (x-y)*(A*(x+y)+B)=0 := by linear_combination a-b
  have g : (x-z)*(A*(x+z)+B)=0 := by linear_combination a-c
  have d := (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr nxy)
  have e := (mul_eq_zero.mp g).resolve_left (sub_ne_zero.mpr nxz)
  have f : A*(y-z)=0 := by linear_combination d-e
  have ha := (mul_eq_zero.mp f).resolve_right (sub_ne_zero.mpr nyz)
  exact ⟨ha,by simpa [ha] using d⟩

/-- All cusps with three distinct weights have the same unordered triple.
The cubic has exactly one negative root. -/
theorem distinct_cusp (l d : Triple) (k : ℝ) (hj : cuspJet l d k)
    (distinct : Function.Injective l) :
    pairSum l = -(2/3) ∧ prod l = -(16/27) ∧
    ∀ i, (3*l i-2)*(9*l i^2-3*l i-8)=0 := by
  obtain ⟨mass,dm,dne,nz,hF,dF,hk⟩ := hj
  let a := pairSum l
  let b := prod l
  let u := pairRate l d
  let v := prodRate l d
  change 8*a^2*(a-1)+(27*a+8)*b=0 at hF
  change (24*a^2-16*a+27*b)*u+(27*a+8)*v=0 at dF
  have root (i : Fin 3) : l i^3-l i^2+a*l i-b=0 := by
    fin_cases i <;> dsimp [a,b,pairSum,prod] <;> rw [show l 0 = 1-l 1-l 2 by linarith] <;> ring
  have dr (i : Fin 3) : (3*l i^2-2*l i+a)*d i = v-l i*u := by
    have e : l 0 = 1-l 1-l 2 := by linarith
    have e' : d 0 = -d 1-d 2 := by linarith
    fin_cases i <;> dsimp [a,u,v,pairSum,pairRate,prodRate] <;> rw [e,e'] <;> ring
  have nr (i : Fin 3) : 3*l i^2-2*l i+a ≠ 0 := by
    have e : 3*l i^2-2*l i+a = (l i-l (i+1))*(l i-l (i+2)) := by
      fin_cases i <;> dsimp [a,pairSum] <;> rw [show l 0 = 1-l 1-l 2 by linarith] <;> ring
    rw [e]
    exact mul_ne_zero (sub_ne_zero.mpr (distinct.ne (by fin_cases i <;> decide)))
      (sub_ne_zero.mpr (distinct.ne (by fin_cases i <;> decide)))
  have nb : b ≠ 0 := mul_ne_zero (mul_ne_zero (nz 0) (nz 1)) (nz 2)
  have na : a ≠ 0 := by intro e; rw [e] at hF; exact nb (by linarith)
  have nden : 27*a+8 ≠ 0 := by
    intro e
    rw [e] at hF
    have ea : a= -(8/27) := by linarith
    rw [ea] at hF
    norm_num at hF
  have nu : u ≠ 0 := by
    intro e
    have ev : v=0 := by simpa [e,nden] using dF
    obtain ⟨i,hi⟩ := dne
    have := dr i
    simp [e,ev,nr i,hi] at this
  let A := 2*u-a*k
  let B := (-2*a^2+a+3*b)*k+(8*a-2)*u-5*v
  let C := (3*a-2)*b*k-9*b*u+(2-2*a)*v
  have q (i : Fin 3) : A*l i^2+B*l i+C=0 := by
    have he : (2*(1-a)-5*l i)*d i-3*l i*u=k*l i*(1-a-l i) := hk i
    dsimp [A,B,C]
    linear_combination (3*l i^2-2*l i+a)*he -
      (2*(1-a)-5*l i)*dr i - (3*l i*k+3*a*k-2*k-9*u)*root i
  obtain ⟨hA,hB⟩ := quadratic_zero _ _ _ _ _ _ (distinct.ne (by decide : (0:Fin 3) ≠ 1))
    (distinct.ne (by decide : (0:Fin 3) ≠ 2)) (distinct.ne (by decide : (1:Fin 3) ≠ 2)) (q 0) (q 1) (q 2)
  have eb : b = 8*a^2*(1-a)/(27*a+8) := (eq_div_iff nden).mpr (by linarith only [hF])
  dsimp [A] at hA
  dsimp [B] at hB
  have e : 1260*a^3*u*(3*a+2)=0 := by
    linear_combination a*(27*a+8)^2*hB+(27*a+8)^2*(-2*a^2+a+3*b)*hA+
      5*a*(27*a+8)*dF-(6*(27*a+8)+135*a)*u*hF
  have ha : a= -(2/3) := by
    have := (mul_eq_zero.mp e).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 na)) nu)
    linarith
  have hb : b= -(16/27) := by rw [eb,ha]; norm_num
  refine ⟨ha,hb,fun i => ?_⟩
  have he := root i
  rw [ha,hb] at he
  linear_combination 27*he

/-- At a cusp with two equal weights, the repeated weight satisfies a
quadratic. Its two roots lie on opposite sides of one half. -/
theorem repeated_cusp (l d : Triple) (k : ℝ) (hj : cuspJet l d k) (i : Fin 3)
    (same : l (i+1) = l (i+2)) :
    6*l (i+1)^2-9*l (i+1)+2=0 := by
  obtain ⟨mass,dm,dne,nz,hF,dF,hk⟩ := hj
  let z := l (i+1)
  let w := d (i+1)+d (i+2)
  have li : l i=1-2*z := by fin_cases i <;> dsimp [z] at * <;> linarith
  have di : d i= -w := by fin_cases i <;> dsimp [w] <;> linarith
  have a : pairSum l=2*z-3*z^2 := by
    have e : pairSum l=l i*l (i+1)+l i*l (i+2)+l (i+1)*l (i+2) := by
      fin_cases i <;> dsimp [pairSum] <;> ring
    rw [e,li,← same]
    dsimp [z]
    ring
  have b : prod l=z^2*(1-2*z) := by
    have e : prod l=l i*l (i+1)*l (i+2) := by fin_cases i <;> dsimp [prod] <;> ring
    rw [e,li,← same]
    dsimp [z]
    ring
  have u : pairRate l d=(1-3*z)*w := by
    have e : pairRate l d = d i*(l (i+1)+l (i+2))+
        d (i+1)*(l i+l (i+2))+d (i+2)*(l i+l (i+1)) := by
      fin_cases i <;> dsimp [pairRate] <;> ring
    rw [e,li,di,← same]
    dsimp [z,w]
    ring
  have v : prodRate l d=z*(1-3*z)*w := by
    have e : prodRate l d = d i*l (i+1)*l (i+2)+l i*d (i+1)*l (i+2)+
        l i*l (i+1)*d (i+2) := by fin_cases i <;> dsimp [prodRate] <;> ring
    rw [e,li,di,← same]
    dsimp [z,w]
    ring
  rw [a,b] at hF
  unfold fold at hF
  rw [a,b,u,v] at dF
  have n : z ≠ 0 := nz _
  have n3 : 1-3*z ≠ 0 := by
    intro e
    have ez : z=1/3 := by linarith
    rw [ez] at hF
    norm_num at hF
  have p : -3*z^2*((6*z^2-9*z+2)*(12*z^2-15*z+4))=0 := by linear_combination hF
  have p' := (mul_eq_zero.mp p).resolve_left (by positivity)
  have g : (3*z*(72*z^3-141*z^2+75*z-8))*((1-3*z)*w)=0 := by linear_combination dF
  have ng : 72*z^3-141*z^2+75*z-8 ≠ 0 := by
    intro e
    have bad : (792:ℝ)=0 := by
      linear_combination -3*(1656*z^2-1707*z+61)*p' +
        3*(1656*z^3-3018*z^2+1329*z-94)*e
    norm_num at bad
  have ew := (mul_eq_zero.mp ((mul_eq_zero.mp g).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) n) ng))).resolve_left n3
  have nd : d (i+1) ≠ d (i+2) := by
    intro de
    have dz : d (i+1)=0 := by change d (i+1)+d (i+2)=0 at ew; linarith
    obtain ⟨j,hj⟩ := dne
    rw [ew,neg_zero] at di
    fin_cases i <;> fin_cases j <;> dsimp at * <;> grind
  have j1 := hk (i+1)
  have j2 := hk (i+2)
  rw [← same] at j2
  have zero : (2*(1-pairSum l)-5*z)*(d (i+1)-d (i+2))=0 := by
    dsimp [z]
    linear_combination j1-j2
  have ez := (mul_eq_zero.mp zero).resolve_right (sub_ne_zero.mpr nd)
  rw [a] at ez
  linarith

end MaxwellCausticExtremum.Cusps

namespace MaxwellCausticExtremum.Cusps

open Set

private noncomputable def small := (9-Real.sqrt 33)/12
private noncomputable def large := (9+Real.sqrt 33)/12
private noncomputable def low := (1-Real.sqrt 33)/6
private noncomputable def high := (1+Real.sqrt 33)/6

private theorem root_bounds : 0 < small ∧ 2*small < 1 ∧ 1 < 2*large ∧ low < 0 ∧ 0 < high := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have s := Real.sqrt_nonneg 33
  dsimp [small,large,low,high]
  refine ⟨?_,?_,?_,?_,?_⟩ <;> nlinarith

private theorem repeated_root {z : ℝ} (e : 6*z^2-9*z+2=0) : z = small ∨ z = large := by
  have sq := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have eq : (12*z-9+Real.sqrt 33)*(12*z-9-Real.sqrt 33)=0 := by nlinarith
  rcases mul_eq_zero.mp eq with h|h
  · exact Or.inl (by dsimp [small]; linarith)
  · exact Or.inr (by dsimp [large]; linarith)

private theorem cubic_roots {z : ℝ} (e : (3*z-2)*(9*z^2-3*z-8)=0) :
    z = 2/3 ∨ z = low ∨ z = high := by
  rcases mul_eq_zero.mp e with h|h
  · exact Or.inl (by linarith)
  have sq := Real.sq_sqrt (show (0:ℝ) ≤ 33 by norm_num)
  have eq : (6*z-1+Real.sqrt 33)*(6*z-1-Real.sqrt 33)=0 := by nlinarith
  rcases mul_eq_zero.mp eq with h|h
  · exact Or.inr (Or.inl (by dsimp [low]; linarith))
  · exact Or.inr (Or.inr (by dsimp [high]; linarith))

private def tripleAt (i : Fin 3) (a b c : ℝ) : Triple :=
  fun j => if j=i then a else if j=i+1 then b else c

private theorem triple_eq (l : Triple) (i : Fin 3) {a b c : ℝ} (h : l i=a)
    (j : l (i+1)=b) (k : l (i+2)=c) : l=tripleAt i a b c := by
  funext n
  fin_cases i <;> fin_cases n <;> simp [tripleAt] at * <;> assumption

private theorem chamber_cases {l d : Triple} {k : ℝ} (h : cuspJet l d k) :
    (∃ i, ∃ z ∈ ({small,large} : Set ℝ), l=tripleAt i (1-2*z) z z) ∨
    (Function.Injective l ∧ ∀ i, l i=2/3 ∨ l i=low ∨ l i=high) := by
  by_cases hd : Function.Injective l
  · exact Or.inr ⟨hd, fun i => cubic_roots ((distinct_cusp l d k h hd).2.2 i)⟩
  have ex : ∃ i : Fin 3, l (i+1)=l (i+2) := by
    by_contra! ne
    apply hd
    intro i j e
    have a := ne 0
    have b := ne 1
    have c := ne 2
    fin_cases i <;> fin_cases j <;> dsimp at * <;> grind
  obtain ⟨i,eq⟩ := ex
  have r := repeated_root (repeated_cusp l d k h i eq)
  have m := h.1
  refine Or.inl ⟨i,l (i+1),r,triple_eq l i ?_ rfl eq.symm⟩
  fin_cases i <;> dsimp at * <;> linarith

private theorem range_bound (f : Fin 3 → Triple) : (range f).encard ≤ 3 := by
  rw [← image_univ]
  exact (encard_image_le f univ).trans (by simp)

def candidates (l : Triple) := ∃ d k, cuspJet l d k

theorem interior_cusp_bound :
    {l : Triple | candidates l ∧ ∀ i, 0 < l i}.encard ≤ 3 := by
  let f (i : Fin 3) := tripleAt i (1-2*small) small small
  apply le_trans (Set.encard_le_encard ?_) (range_bound f)
  rintro l ⟨⟨d,k,h⟩,hp⟩
  rcases chamber_cases h with ⟨i,z,hz,rfl⟩|⟨inj,roots⟩
  · rcases hz with rfl|rfl
    · exact ⟨i,rfl⟩
    · have := hp i
      simp [tripleAt] at this
      linarith [root_bounds.2.2.1]
  · have two (i : Fin 3) : l i=2/3 ∨ l i=high := by
      rcases roots i with e|e|e
      · exact Or.inl e
      · linarith [hp i,root_bounds.2.2.2.1]
      · exact Or.inr e
    have n01 := inj.ne (by decide : (0:Fin 3) ≠ 1)
    have n02 := inj.ne (by decide : (0:Fin 3) ≠ 2)
    have n12 := inj.ne (by decide : (1:Fin 3) ≠ 2)
    rcases two 0 with h0|h0 <;> rcases two 1 with h1|h1 <;> rcases two 2 with h2|h2 <;> grind

theorem edge_cusp_bound (e : Fin 3) :
    {l : Triple | candidates l ∧ l e < 0 ∧ 0 < l (e+1) ∧ 0 < l (e+2)}.encard ≤ 3 := by
  let f : Fin 3 → Triple := ![tripleAt e (1-2*large) large large,
    tripleAt e low (2/3) high,tripleAt e low high (2/3)]
  apply le_trans (Set.encard_le_encard ?_) (range_bound f)
  rintro l ⟨⟨d,k,h⟩,hn,hp,hq⟩
  rcases chamber_cases h with ⟨i,z,hz,rfl⟩|⟨inj,roots⟩
  · rcases hz with rfl|rfl
    · dsimp [tripleAt] at hn
      split at hn
      · linarith [root_bounds.2.1]
      · split at hn <;> linarith [root_bounds.1]
    · have hi : e=i := by
        by_contra ne
        simp [tripleAt,ne] at hn
        linarith [root_bounds.2.2.1]
      subst i
      exact ⟨0,rfl⟩
  · have hlow : l e=low := by
      rcases roots e with h|h|h
      · linarith
      · exact h
      · linarith [root_bounds.2.2.2.2]
    have two (i : Fin 3) (pos : 0 < l i) : l i=2/3 ∨ l i=high := by
      rcases roots i with h|h|h
      · exact Or.inl h
      · linarith [root_bounds.2.2.2.1]
      · exact Or.inr h
    have ne := inj.ne (show e+1 ≠ e+2 by fin_cases e <;> decide)
    rcases two _ hp with a|a <;> rcases two _ hq with b|b
    · exact (ne (a.trans b.symm)).elim
    · exact ⟨1,(triple_eq l e hlow a b).symm⟩
    · exact ⟨2,(triple_eq l e hlow a b).symm⟩
    · exact (ne (a.trans b.symm)).elim

end MaxwellCausticExtremum.Cusps

namespace MaxwellCausticExtremum.Cusps

noncomputable def logCharge (l : Triple) (i : Fin 3) :=
  Real.log (l i)+(3/2)*Real.log (1-pairSum l-l i)

private theorem pair_deriv {f : ℝ → Triple} {d : Triple} {t : ℝ}
    (df : ∀ i, HasDerivAt (fun z => f z i) (d i) t) :
    HasDerivAt (fun z => pairSum (f z)) (pairRate (f t) d) t := by
  convert! (((df 0).mul (df 1)).add ((df 0).mul (df 2))).add ((df 1).mul (df 2)) using 1
  dsimp [pairRate]
  ring

private theorem prod_deriv {f : ℝ → Triple} {d : Triple} {t : ℝ}
    (df : ∀ i, HasDerivAt (fun z => f z i) (d i) t) :
    HasDerivAt (fun z => prod (f z)) (prodRate (f t) d) t := by
  convert! (((df 0).mul (df 1)).mul (df 2)) using 1
  dsimp [prodRate]
  ring

/-- A stationary charge-ratio point of a regular parametrized equilateral
fold satisfies the algebraic equations used in both cusp bounds. -/
theorem candidate_of_stationary {f : ℝ → Triple} {d : Triple} {t : ℝ}
    (df : ∀ i, HasDerivAt (fun z => f z i) (d i) t) (reg : ∃ i, d i ≠ 0)
    (mass : ∀ z, f z 0+f z 1+f z 2=1) (nz : ∀ i, f t i ≠ 0)
    (rad : ∀ i, 1-pairSum (f t)-f t i ≠ 0)
    (critical : ∀ z, fold (pairSum (f z)) (prod (f z)) = 0)
    (stationary : ∀ i, HasDerivAt (fun z => logCharge (f z) i-logCharge (f z) 0) 0 t) :
    candidates (f t) := by
  have ds := pair_deriv df
  have dp := prod_deriv df
  have m := ((df 0).add (df 1)).add (df 2)
  have dm : d 0+d 1+d 2=0 := m.unique (by
    change HasDerivAt (fun z => f z 0+f z 1+f z 2) 0 t
    simpa only [mass] using (hasDerivAt_const t (1:ℝ)))
  have fld := ((((ds.pow 2).const_mul 8).mul (ds.sub_const 1)).add (((ds.const_mul 27).add_const 8).mul dp))
  have zero : HasDerivAt (fun z => fold (pairSum (f z)) (prod (f z))) 0 t := by
    simpa only [critical] using (hasDerivAt_const t (0:ℝ))
  have balance := fld.unique zero
  let a := pairSum (f t)
  let u := pairRate (f t) d
  let speed (i : Fin 3) := d i/f t i+(3/2)*((-u-d i)/(1-a-f t i))
  have charge (i : Fin 3) : HasDerivAt (fun z => logCharge (f z) i) (speed i) t :=
    ((df i).log (nz i)).add (((((ds.const_sub 1).sub (df i)).log (rad i))).const_mul _)
  refine ⟨d,2*speed 0,mass t,dm,reg,nz,critical t,?_,?_⟩
  · simp only [Pi.pow_apply] at balance
    linear_combination balance
  · intro i
    have same := ((charge i).sub (charge 0)).unique (stationary i)
    rw [← sub_eq_zero.mp same]
    dsimp [speed,u,a]
    field_simp [nz i,rad i]
    ring

end MaxwellCausticExtremum.Cusps

namespace MaxwellCausticExtremum.Cusps

/-- In the normalized unit-side equilateral chart the three squared radii
differ from the corresponding negative barycentric weights by one common term. -/
theorem equilateral_radii (h : ℝ) (hh : h^2=3/4) (l : Triple)
    (mass : l 0+l 1+l 2=1) (i : Fin 3) :
    let X := l 1+l 2/2
    let Y := h*l 2
    (X-(![0,1,1/2] : Triple) i)^2+(Y-(![0,0,h] : Triple) i)^2 =
      1-pairSum l-l i := by
  fin_cases i <;> dsimp [pairSum] <;> rw [show l 0 = 1-l 1-l 2 by linarith]
  · linear_combination (l 2)^2*hh
  · linear_combination (l 2)^2*hh
  · linear_combination (l 2-1)^2*hh

end MaxwellCausticExtremum.Cusps

end

section

noncomputable section
open Set Real
namespace MaxwellCausticExtremum.Chart

private def H := sqrt 3/2
private theorem hH : 0 < H := by dsimp [H]; positivity
private theorem hSq : H^2=3/4 := by dsimp [H]; rw [div_pow,sq_sqrt (by norm_num)]; norm_num

private theorem radius_base (z : Plane) (i : Fin 3) :
    let l := coordinates (1/2) H z.1 z.2
    radii (1/2) H z.1 z.2 i=1-Cusps.pairSum l-l i := by
  let l := coordinates (1/2) H z.1 z.2
  have m : l 0+l 1+l 2=1 := by simpa only [Fin.sum_univ_three] using (bary_moments (1/2) H z hH.ne').1
  have ex : l 1+l 2/2=z.1 := by dsimp [l,coordinates]; ring
  have ey : H*l 2=z.2 := by dsimp [l,coordinates]; field_simp [hH.ne']
  have e := Cusps.equilateral_radii H hSq l m i
  dsimp only at e ⊢
  rw [ex,ey] at e
  simpa [radii_eq,dx,dy,l] using e

private theorem base_fold (z : Plane) (hl : ∀ i, coordinates (1/2) H z.1 z.2 i ≠ 0)
    (crit : detH (1/2) H z.1 z.2=0) :
    let l := coordinates (1/2) H z.1 z.2
    Cusps.fold (Cusps.pairSum l) (Cusps.prod l)=0 := by
  let l := coordinates (1/2) H z.1 z.2
  let r := radii (1/2) H z.1 z.2
  have hr i := (radii_pos_of_chamber (1/2) H z hH.ne' hl i).ne'
  have eq := detH_eq (1/2) H z.1 z.2 hH.ne' hr
  dsimp only at eq
  rw [crit,hSq] at eq
  change 0=9*(3/4)*l 0*l 1*l 2*(∑ i,l i*r i)/(r 0*r 1*r 2)-2 at eq
  have den : r 0*r 1*r 2 ≠ 0 := mul_ne_zero (mul_ne_zero (hr _) (hr _)) (hr _)
  have val := (div_eq_iff den).mp (show 9*(3/4)*l 0*l 1*l 2*(∑ i,l i*r i)/(r 0*r 1*r 2)=2 by linarith only [eq])
  have m : l 0+l 1+l 2=1 := by simpa only [Fin.sum_univ_three] using (bary_moments (1/2) H z hH.ne').1
  have num := Cusps.determinant_numerator l m
  dsimp only
  change Cusps.fold (Cusps.pairSum l) (Cusps.prod l)=0
  rw [← num]
  have r' (i : Fin 3) : 1-Cusps.pairSum l-l i=r i := (radius_base z i).symm
  simp only [r',Cusps.prod]
  linear_combination 4*val

private theorem base_candidate (c : Fin 4) (z : Plane)
    (hz : z ∈ Cusp.source (1/2) H (chamberSigns c)) :
    Cusps.candidates (coordinates (1/2) H z.1 z.2) := by
  obtain ⟨⟨p,n⟩,hp,e⟩ := hz
  change p=z at e; subst p
  have hl i := right_ne_zero_of_mul (hp.1 i).ne'
  have J : detH (1/2) H z.1 z.2=0 := Cusp.det_zero _ _ (z,n) hH.ne' hl hp.2
  let γ := oval (1/2) H hH c
  obtain ⟨t,et⟩ : z ∈ range γ := (Set.ext_iff.mp (oval_range (1/2) H hH c) z).mpr ⟨hp.1,J⟩
  let f (u : ℝ) := coordinates (1/2) H (γ u).1 (γ u).2
  let v := deriv γ t
  let b := coordVelocity (1/2) H v.1 v.2
  have dg : HasDerivAt γ v t := ((oval_C1 _ _ hH c).differentiable (by simp) t).hasDerivAt
  have dx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dg
  have dy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t dg
  have dL (i : Fin 3) : HasDerivAt (fun u => f u i) (b i) t := by
    fin_cases i
    · convert! ((dx.const_sub 1).add ((dy.const_mul (1/2-1:ℝ)).div_const H)) using 1
    · convert! dx.sub ((dy.const_mul (1/2:ℝ)).div_const H) using 1
    · exact dy.div_const H
  have reg : ∃ i, b i ≠ 0 := by
    by_contra! zero
    have bv := (bary_moments (1/2) H (γ t) hH.ne').2.2.2 v.1 v.2
    obtain ⟨_,u,w⟩ := bv
    change (∑ i,b i*_)=v.1 at u
    change (∑ i,b i*_)=v.2 at w
    simp only [zero,zero_mul,Finset.sum_const_zero] at u w
    exact oval_velocity_ne _ _ hH c t (Prod.ext u.symm w.symm)
  have boundary (u : ℝ) : (∀ i, 0 < chamberSigns c i*f u i) ∧ detH (1/2) H (γ u).1 (γ u).2=0 :=
    (Set.ext_iff.mp (oval_range _ _ hH c) (γ u)).mp ⟨u,rfl⟩
  have src : γ t ∈ Cusp.source (1/2) H (chamberSigns c) := et ▸ ⟨(z,n),hp,rfl⟩
  have stationary := (image_deriv _ _ hH c t).congr_deriv ((velocity_zero_iff _ _ hH c t).mpr src)
  have ch (u : ℝ) (i : Fin 3) : Cusps.logCharge (f u) i=logCharge (1/2) H (γ u).1 (γ u).2 i := by
    simp only [Cusps.logCharge,logCharge,radius_base,f]
  rw [← et]
  apply Cusps.candidate_of_stationary dL reg (fun u => by simpa only [Fin.sum_univ_three] using
    (bary_moments (1/2) H (γ u) hH.ne').1)
    (fun i => right_ne_zero_of_mul ((boundary t).1 i).ne')
    (fun i => (radius_base (γ t) i).symm.trans_ne ((radii_pos_of_chamber _ _ _ hH.ne'
      (fun i => right_ne_zero_of_mul ((boundary t).1 i).ne') i).ne'))
    (fun u => base_fold _ (fun i => right_ne_zero_of_mul ((boundary u).1 i).ne') (boundary u).2)
  intro i; simp only [ch]
  fin_cases i
  · change HasDerivAt (fun u => logCharge (1/2) H (γ u).1 (γ u).2 0-logCharge (1/2) H (γ u).1 (γ u).2 0) 0 t
    simpa only [sub_self] using hasDerivAt_const t (0:ℝ)
  · exact (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t stationary
  · exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t stationary

private theorem base_source_bound (c : Fin 4) : (Cusp.source (1/2) H (chamberSigns c)).encard ≤ 3 := by
  let S := Cusp.source (1/2) H (chamberSigns c)
  let L (z : Plane) := coordinates (1/2) H z.1 z.2
  have inj : Function.Injective L := by
    intro z w e
    have a := congrFun e 1
    have b := congrFun e 2
    dsimp [L,coordinates] at a b
    field_simp [hH.ne'] at a b
    apply Prod.ext
    · apply mul_right_cancel₀ (b := H) hH.ne'
      linarith only [a,b]
    · linarith only [b]
  change S.encard ≤ 3
  rw [← inj.encard_image S]
  have cond (z : Plane) (hz : z ∈ S) : Cusps.candidates (L z) ∧ ∀ i, 0 < chamberSigns c i*L z i := by
    refine ⟨base_candidate c z hz,?_⟩
    obtain ⟨w,hw,rfl⟩ := hz
    exact hw.1
  fin_cases c
  · apply le_trans (Set.encard_le_encard ?_) Cusps.interior_cusp_bound
    rintro _ ⟨z,hz,rfl⟩
    have h := cond z hz
    refine ⟨h.1,?_⟩; intro i; have := h.2 i
    fin_cases i <;> simpa [chamberSigns] using this
  case' «1» => apply le_trans (Set.encard_le_encard ?_) (Cusps.edge_cusp_bound 0)
  case' «2» => apply le_trans (Set.encard_le_encard ?_) (Cusps.edge_cusp_bound 1)
  case' «3» => apply le_trans (Set.encard_le_encard ?_) (Cusps.edge_cusp_bound 2)
  all_goals
    rintro _ ⟨z,hz,rfl⟩
    have h := cond z hz
    obtain ⟨hc,hs⟩ := h
    have p := hs 0; have q := hs 1; have r := hs 2
    norm_num [chamberSigns] at p q r
    first | change 0 < (1:ℝ)*L z 2 at r | change 0 < (-1:ℝ)*L z 2 at r
    norm_num at r
    exact ⟨hc,by assumption,by assumption,by assumption⟩

end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum.Chart

theorem cusp_bound (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    (Cusp.source s h (chamberSigns c)).encard ≤ 3 := by
  let S (a : ℝ) := (1-a)/2+a*s
  let T (a : ℝ) := (1-a)*H+a*h
  have hn (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) : T a ≠ 0 := by
    by_cases e : a=0
    · subst a; simpa [T] using hH.ne'
    · have p := mul_pos (lt_of_le_of_ne ha.1 (Ne.symm e)) hh
      have q := mul_nonneg (sub_nonneg.mpr ha.2) hH.le
      dsimp [T]; linarith only [p,q]
  have sign (i : Fin 3) : chamberSigns c i ≠ 0 := by fin_cases c <;> fin_cases i <;> norm_num [chamberSigns]
  have tr := Cusp.cusp_path_count S T (chamberSigns c) (by dsimp [S]; fun_prop)
    (by dsimp [T]; fun_prop) hn sign
  simp only [S,T,sub_zero,sub_self,one_mul,zero_mul,zero_div,zero_add,add_zero] at tr
  rw [Cusp.fiber_pair_count _ _ hH.ne',Cusp.fiber_pair_count _ _ hh.ne'] at tr
  have hb := base_source_bound c
  by_contra! bad
  have ge : (4:ℕ∞) ≤ (Cusp.source s h (chamberSigns c)).encard := (ENat.natCast_add_one_le_iff (m := 3)).mpr bad
  have b1 := mul_le_mul_of_nonneg_right hb (show 0 ≤ (2:ℕ∞) by norm_num)
  have b2 := mul_le_mul_of_nonneg_right ge (show 0 ≤ (2:ℕ∞) by norm_num)
  rw [tr] at b1
  norm_num at b1 b2
  exact (show ¬(8:ℕ∞)≤6 by decide) (b2.trans b1)

theorem boundary_injective (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    InjOn (chargeMap s h) {z : Plane | (∀ i, 0 < chamberSigns c i*coordinates s h z.1 z.2 i) ∧
      detH s h z.1 z.2=0} := by
  let γ := oval s h hh c
  let F := chargeMap s h ∘ γ
  let V := imageVelocity s h hh c
  have period := oval_periodic s h hh c
  have count (a : ℝ) : {t ∈ Ioo a (a+π) | V t=0}.encard ≤ 3 := by
    let S := {t ∈ Ioo a (a+π) | V t=0}
    have sub : S ⊆ Ico a (a+π) := fun t ht => ⟨ht.1.1.le,ht.1.2⟩
    have inj : InjOn γ S := (oval_injective_period s h hh c a).mono sub
    change S.encard ≤ 3
    rw [← inj.encard_image]
    apply le_trans (Set.encard_le_encard ?_) (cusp_bound s h hh c)
    rintro _ ⟨t,ht,rfl⟩
    exact (velocity_zero_iff s h hh c t).mp ht.2
  have direction (t : ℝ) : ∃ k : ℝ, V t=(k*cos t,k*sin t) := by
    have root : γ t ∈ normalFiber s h c t := by rw [normalFiber_eq s h hh c]; rfl
    have hl i := right_ne_zero_of_mul (root.1 i).ne'
    have mass : ∑ i, angleCovector t i=0 := by simp [angleCovector,Fin.sum_univ_three]; ring
    have e := (normalEquations_zero_iff s h (angleCovector t) (γ t) mass hl
      (fun i => (radii_pos_of_chamber s h _ hh.ne' hl i).ne')).mp root.2 (deriv γ t)
    change -sin t*(V t).1+cos t*(V t).2=0 at e
    refine ⟨(V t).1*cos t+(V t).2*sin t,Prod.ext ?_ ?_⟩ <;> dsimp only
    · linear_combination -(V t).1*sin_sq_add_cos_sq t-sin t*e
    · linear_combination -(V t).2*sin_sq_add_cos_sq t+cos t*e
  have inj := Arc.injective_in_angle_parameter F V (fun t => congrArg (chargeMap s h) (period t))
    (image_deriv s h hh c) count direction 0
  rw [← oval_range s h hh c]
  rintro _ ⟨t,rfl⟩ _ ⟨u,rfl⟩ he
  obtain ⟨a,ha,ea⟩ := period.exists_mem_Ico pi_pos t 0
  obtain ⟨b,hb,eb⟩ := period.exists_mem_Ico pi_pos u 0
  rw [ea,eb] at he ⊢
  exact congrArg γ (inj ha hb he)

end MaxwellCausticExtremum.Chart

end
end

section

open Set Filter
open scoped Topology

namespace MaxwellCausticExtremum.Finish

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [T2Space E] [T2Space X] [CompactSpace E] {F : E → X}

private def multiple (F : E → X) : Set E := {x | ∃ y, x ≠ y ∧ F x = F y}

private theorem closed_multiple (hf : Continuous F)
    (loc : ∀ x, ∃ U ∈ 𝓝 x, InjOn F U) : IsClosed (multiple F) := by
  let P : Set (E × E) := {z | z.1 ≠ z.2 ∧ F z.1 = F z.2}
  have hp : IsClosed P := by
    rw [← isOpen_compl_iff,isOpen_iff_mem_nhds]
    rintro ⟨x,y⟩ h
    by_cases e : x = y
    · subst y
      obtain ⟨U,hU,hi⟩ := loc x
      apply mem_of_superset (prod_mem_nhds hU hU)
      exact fun z hz ⟨hne,he⟩ => hne (hi hz.1 hz.2 he)
    · have ne : F x ≠ F y := fun a => h ⟨e,a⟩
      have ho := (isClosed_eq (hf.comp continuous_fst) (hf.comp continuous_snd)).isOpen_compl
      exact mem_of_superset (ho.mem_nhds ne) fun _ hn hP => hn hP.2
  have he : Prod.fst '' P = multiple F := by
    ext x
    exact ⟨fun ⟨z,hz,e⟩ => e ▸ ⟨z.2,hz⟩,fun ⟨y,h⟩ => ⟨(x,y),h,rfl⟩⟩
  exact he ▸ (hp.isCompact.image continuous_fst).isClosed

omit [T2Space X] [CompactSpace E] in
/-- Every double point persists near the first source point if the second
source point is regular. -/
private theorem multiple_mem {B : Set E} (hf : Continuous F)
    (reg : IsLocalHomeomorphOn F Bᶜ) {x y : E} (ne : x ≠ y) (eq : F x = F y)
    (hy : y ∉ B) : multiple F ∈ 𝓝 x := by
  obtain ⟨U,V,hU,hV,hd⟩ := t2_separation_nhds ne
  have hv : F '' V ∈ 𝓝 (F x) := by
    rw [eq,← reg.map_nhds_eq hy]
    exact mem_map.mpr (mem_of_superset hV (fun z hz => ⟨z,hz,rfl⟩))
  filter_upwards [hU,hf.continuousAt.preimage_mem_nhds hv] with z hz hz'
  obtain ⟨w,hw,he⟩ := hz'
  exact ⟨w,fun e => disjoint_left.mp hd hz (e ▸ hw),he.symm⟩

/-- A compact locally injective map to a connected target is injective if it
omits a value, is regular off a connected boundary, and embeds that boundary.
No separation theorem for the image curve is needed. -/
theorem injective_of_connected_boundary [PreconnectedSpace X] (B : Set E)
    (hB : IsPreconnected B) (hf : Continuous F) (reg : IsLocalHomeomorphOn F Bᶜ)
    (boundary : InjOn F B) (loc : ∀ x, ∃ U ∈ 𝓝 x, InjOn F U)
    (miss : ∃ z, z ∉ range F) : Function.Injective F := by
  have hc := closed_multiple hf loc
  have image_nhds (x : E) (hx : x ∉ B) (S : Set E) (hS : S ∈ 𝓝 x) :
      F '' S ∈ 𝓝 (F x) := by
    rw [← reg.map_nhds_eq hx]
    exact mem_map.mpr (mem_of_superset hS fun z hz => ⟨z,hz,rfl⟩)
  have interior_other {x : E} (hx : x ∈ B) {y : E} (ne : x ≠ y) (eq : F x = F y) :
      y ∉ B := fun hy => ne (boundary hx hy eq)
  have excluded (x : E) (hx : x ∈ B) : x ∉ multiple F := by
    intro hm
    let := Subtype.preconnectedSpace hB
    let D : Set B := Subtype.val ⁻¹' multiple F
    have hd : IsClopen D := by
      refine ⟨hc.preimage continuous_subtype_val,isOpen_iff_mem_nhds.mpr ?_⟩
      rintro z ⟨y,ne,eq⟩
      exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        (multiple_mem hf reg ne eq (interior_other z.2 ne eq))
    have allB := hd.eq_univ (show D.Nonempty from ⟨⟨x,hx⟩,hm⟩)
    have openR : IsOpen (range F) := by
      apply isOpen_iff_mem_nhds.mpr
      rintro _ ⟨w,rfl⟩
      have ir (v : E) (hv : v ∉ B) : range F ∈ 𝓝 (F v) := by
        simpa using image_nhds v hv univ univ_mem
      by_cases hw : w ∈ B
      · have md : (⟨w,hw⟩ : B) ∈ D := allB ▸ mem_univ _
        obtain ⟨v,ne,eq⟩ := md
        rw [eq]
        exact ir v (interior_other hw ne eq)
      · exact ir w hw
    obtain ⟨z,hz⟩ := miss
    exact hz ((IsClopen.eq_univ ⟨(isCompact_range hf).isClosed,openR⟩
      ⟨F x,x,rfl⟩) ▸ mem_univ _)
  have hmOpen : IsOpen (F '' multiple F) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,ne,eq⟩ := hx
    have xm : x ∈ multiple F := ⟨y,ne,eq⟩
    have ym : y ∈ multiple F := ⟨x,ne.symm,eq.symm⟩
    exact image_nhds x (fun hb => excluded x hb xm) _ <|
      multiple_mem hf reg ne eq (fun hb => excluded y hb ym)
  intro x y eq
  by_contra ne
  have hi := IsClopen.eq_univ ⟨(hc.isCompact.image hf).isClosed,hmOpen⟩
    (show (F '' multiple F).Nonempty from ⟨F x,x,⟨y,ne,eq⟩,rfl⟩)
  obtain ⟨z,hz⟩ := miss
  exact hz (image_subset_range F (multiple F) (hi ▸ mem_univ _))

end MaxwellCausticExtremum.Finish

namespace MaxwellCausticExtremum.Finish

/-- On a noncompact connected target, such as the log-ratio plane, the
omitted value and the local injectivity at all regular points are automatic. -/
theorem one_sheet {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space E]
    [T2Space X] [CompactSpace E] [PreconnectedSpace X] [NoncompactSpace X] {F : E → X}
    (B : Set E) (hB : IsPreconnected B) (hf : Continuous F) (reg : IsLocalHomeomorphOn F Bᶜ)
    (boundary : InjOn F B) (charts : ∀ x ∈ B, ∃ U ∈ 𝓝 x, InjOn F U) : Function.Injective F := by
  apply injective_of_connected_boundary B hB hf reg boundary
  · intro x
    by_cases h : x ∈ B
    · exact charts x h
    · obtain ⟨e,hs,eq⟩ := reg x h
      exact ⟨e.source,e.open_source.mem_nhds hs,eq ▸ e.injOn⟩
  · by_contra! h
    exact noncompact_univ X ((Set.eq_univ_of_forall h) ▸ isCompact_range hf)

end MaxwellCausticExtremum.Finish

end

section

noncomputable section

open InnerProductSpace
namespace MaxwellCausticExtremum.Frame

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The represented sites have coordinates (0,0), (1,0) and (s,h).
Both the scale and the height are strictly positive. -/
structure Triangle (a : Fin 3 → E) where
  u : E
  v : E
  d : ℝ
  s : ℝ
  h : ℝ
  d_pos : 0 < d
  h_pos : 0 < h
  unit_u : ‖u‖ = 1
  unit_v : ‖v‖ = 1
  perp : ⟪u,v⟫_ℝ = 0
  site_one : a 1 = a 0 + d • u
  site_two : a 2 = a 0 + d • (s • u + h • v)

def point {a : Fin 3 → E} (T : Triangle a) (p : ℝ × ℝ) : E :=
  a 0 + T.d • (p.1 • T.u + p.2 • T.v)

theorem exists_triangle {a : Fin 3 → E} (ha : AffineIndependent ℝ a) : Nonempty (Triangle a) := by
  let A := a 1-a 0
  let B := a 2-a 0
  let d := ‖A‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr (ha.injective.ne (by decide)))
  let u := d⁻¹ • A
  have hu : ‖u‖ = 1 := by simp [u,norm_smul,d,hd.ne']
  have hA : d • u = A := by simp [u,smul_smul,hd.ne']
  let z := ⟪u,B⟫_ℝ
  let C := B-z • u
  have hC : C ≠ 0 := by
    intro hz
    have eq : B = (z*d⁻¹) • A := by
      rw [mul_smul]
      exact sub_eq_zero.mp hz
    let S := affineSpan ℝ (a '' (Set.univ \ {2}))
    have mem (i : Fin 3) (hi : i ≠ 2) : a i ∈ S := subset_affineSpan ℝ _ ⟨i,⟨Set.mem_univ _,hi⟩,rfl⟩
    have hmem := S.smul_vsub_vadd_mem (z*d⁻¹) (mem 1 (by decide)) (mem 0 (by decide)) (mem 0 (by decide))
    change (z*d⁻¹) • A + a 0 ∈ S at hmem
    rw [← eq] at hmem
    exact ha.notMem_affineSpan_sdiff 2 Set.univ (by simpa [B] using hmem)
  let k := ‖C‖
  have hk : 0 < k := norm_pos_iff.mpr hC
  let v := k⁻¹ • C
  have hv : ‖v‖ = 1 := by simp [v,k,norm_smul,hC]
  have hCv : k • v = C := by simp [v,smul_smul,hk.ne']
  have perp : ⟪u,v⟫_ℝ = 0 := by
    simp [v,C,inner_sub_right,real_inner_smul_right,hu,z]
  refine ⟨⟨u,v,d,z/d,k/d,hd,div_pos hk hd,hu,hv,perp,?_,?_⟩⟩
  · rw [hA]; dsimp [A]; abel
  · simp only [smul_add,smul_smul,mul_div_cancel₀ _ hd.ne',hCv]
    dsimp [C,B]
    abel

theorem point_distance_sq {a : Fin 3 → E} (T : Triangle a) (p q : ℝ × ℝ) :
    ‖point T p - point T q‖^2 = T.d^2*((p.1-q.1)^2+(p.2-q.2)^2) := by
  have h : point T p - point T q = T.d • ((p.1-q.1) • T.u + (p.2-q.2) • T.v) := by
    unfold point
    module
  rw [h,norm_smul,Real.norm_eq_abs,abs_of_pos T.d_pos,mul_pow]
  congr 1
  rw [← real_inner_self_eq_norm_sq]
  have uu : ⟪T.u,T.u⟫_ℝ = 1 := by simp [T.unit_u]
  have vv : ⟪T.v,T.v⟫_ℝ = 1 := by simp [T.unit_v]
  have vu : ⟪T.v,T.u⟫_ℝ = 0 := (real_inner_comm T.u T.v).trans T.perp
  simp only [inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    uu,vv,vu,T.perp]
  ring

theorem point_range {a : Fin 3 → E} (T : Triangle a) :
    Set.range (point T) = (affineSpan ℝ (Set.range a) : Set E) := by
  let P := affineSpan ℝ (Set.range a)
  have mem (i : Fin 3) : a i ∈ P := subset_affineSpan ℝ _ ⟨i,rfl⟩
  have ae : T.d • T.u = a 1 - a 0 := by rw [T.site_one]; abel
  have be : T.d • (T.s • T.u+T.h • T.v) = a 2 - a 0 := by rw [T.site_two]; abel
  ext x
  constructor
  · rintro ⟨⟨u,v⟩,rfl⟩
    let b := v/T.h
    let c := u-b*T.s
    have e : point T (u,v) = (c • (a 1-a 0)+b • (a 2-a 0))+a 0 := by
      rw [← ae, ← be]
      unfold point
      simp only [smul_add,smul_smul]
      have h : b*T.h=v := div_mul_cancel₀ _ T.h_pos.ne'
      dsimp only [c]
      rw [← h]
      module
    rw [e]
    exact P.vadd_mem_of_mem_direction (P.direction.add_mem
      (P.direction.smul_mem _ (P.vsub_mem_direction (mem 1) (mem 0)))
      (P.direction.smul_mem _ (P.vsub_mem_direction (mem 2) (mem 0)))) (mem 0)
  · intro hx
    obtain ⟨l,hs,hl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
    refine ⟨(l 1+l 2*T.s,l 2*T.h),?_⟩
    rw [hl,Finset.affineCombination_eq_linear_combination _ _ _ hs,Fin.sum_univ_three,T.site_one,T.site_two]
    rw [Fin.sum_univ_three] at hs
    have e : l 0 = 1-l 1-l 2 := by linarith
    rw [e]
    unfold point
    module

end MaxwellCausticExtremum.Frame

end
end

section

noncomputable section

open scoped BigOperators Gradient RealInnerProductSpace Topology
open Arxiv.«2607.27197» InnerProductSpace Filter

namespace MaxwellCausticExtremum

abbrev E := EuclideanSpace ℝ (Fin 3)

/-- Inverse-cube force weight, with the sign of the charge. -/
def weight (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) (i : Fin 3) : ℝ :=
  q i / ‖x - a i‖ ^ 3

def total (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) : ℝ := ∑ i, weight q a x i

def bary (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) (i : Fin 3) : ℝ :=
  (total q a x)⁻¹ * weight q a x i

theorem equilibrium_iff {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E} :
    x ∈ equilibria q a ↔ x ∉ Set.range a ∧ ∑ i, weight q a x i • (x - a i) = 0 := by
  simpa only [weight, neg_div, neg_smul, Finset.sum_neg_distrib, neg_eq_zero] using
    MaxwellIndexCount.mem_equilibria_iff q a x

theorem total_ne_zero {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (hx : x ∈ equilibria q a) :
    total q a x ≠ 0 := by
  obtain ⟨hoff,hforce⟩ := equilibrium_iff.mp hx
  intro hz
  have he := Finset.sum_smul_const_vsub_eq_neg_weightedVSub
    Finset.univ (weight q a x) a x hz
  rw [show ∑ i, weight q a x i • (x -ᵥ a i) = 0 from hforce, eq_comm, neg_eq_zero] at he
  have h := (affineIndependent_iff_of_fintype ℝ a).1 ha _ hz he 0
  exact (div_ne_zero hq (pow_ne_zero 3 (norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr fun e => hoff ⟨0,e.symm⟩)))) h

theorem equilibrium_barycentric {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (hx : x ∈ equilibria q a) :
    ∑ i, bary q a x i = 1 ∧ ∑ i, bary q a x i • a i = x := by
  have hs : ∑ i, bary q a x i = 1 := by
    simpa [bary, ← Finset.mul_sum, total] using inv_mul_cancel₀ (total_ne_zero ha hq hx)
  refine ⟨hs,?_⟩
  have hf : ∑ i, bary q a x i • (x - a i) = 0 := by
    simp only [bary,mul_smul, ← Finset.smul_sum,(equilibrium_iff.mp hx).2,smul_zero]
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hs, one_smul, sub_eq_zero] at hf
  exact hf.symm

theorem potential_hessian (q : Fin 3 → ℝ) (a : Fin 3 → E) {x : E}
    (hx : x ∉ Set.range a) (v w : E) :
    iteratedFDeriv ℝ 2 (potential q a) x ![v,w] =
      ∑ i, ((3*q i/‖x-a i‖^5) * ⟪x-a i,v⟫_ℝ * ⟪x-a i,w⟫_ℝ -
        weight q a x i * ⟪v,w⟫_ℝ) := by
  simpa only [weight, sub_eq_add_neg, neg_div, neg_mul, add_comm] using
    MaxwellIndexCount.potential_hessian q a hx v w

/-- Two positive barycentric entries characterize the four nonvertex chambers,
when all three entries are nonzero and sum to one. -/
def nonvertex (l : Fin 3 → ℝ) : Prop :=
  (0 < l 0 ∧ 0 < l 1) ∨ (0 < l 1 ∧ 0 < l 2) ∨ (0 < l 0 ∧ 0 < l 2)

private theorem common_positive {l m : Fin 3 → ℝ} (hl : nonvertex l) (hm : nonvertex m) :
    ∃ i, 0 < l i ∧ 0 < m i := by
  rcases hl with hl|hl|hl <;> rcases hm with hm|hm|hm
    <;> first | exact ⟨0,hl.1,hm.1⟩ | exact ⟨1,hl.2,hm.1⟩ | exact ⟨1,hl.1,hm.2⟩
              | exact ⟨1,hl.1,hm.1⟩ | exact ⟨2,hl.2,hm.2⟩

private theorem bary_product {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (hx : x ∉ Set.range a) (hs : total q a x ≠ 0) (i : Fin 3) :
    bary q a x i * total q a x * ‖x-a i‖^3 = q i := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun e => hx ⟨i,e.symm⟩)
  unfold bary weight
  field_simp [hs,hn]

theorem same_nonvertex_chamber {q : Fin 3 → ℝ} {a : Fin 3 → E} {x y : E}
    (ha : AffineIndependent ℝ a) (hq : ∀ i, q i ≠ 0)
    (hx : x ∈ equilibria q a) (hy : y ∈ equilibria q a)
    (hnx : nonvertex (bary q a x)) (hny : nonvertex (bary q a y)) :
    ∀ i, 0 < bary q a x i ↔ 0 < bary q a y i := by
  have sx := total_ne_zero ha (hq 0) hx
  have sy := total_ne_zero ha (hq 0) hy
  have hx' := (equilibrium_iff.mp hx).1
  have hy' := (equilibrium_iff.mp hy).1
  have rx (i : Fin 3) : 0 < ‖x-a i‖^3 := pow_pos
    (norm_pos_iff.mpr (sub_ne_zero.mpr fun e => hx' ⟨i,e.symm⟩)) _
  have ry (i : Fin 3) : 0 < ‖y-a i‖^3 := pow_pos
    (norm_pos_iff.mpr (sub_ne_zero.mpr fun e => hy' ⟨i,e.symm⟩)) _
  have signs (i : Fin 3) : (0 < bary q a x i * total q a x) ↔
      (0 < bary q a y i * total q a y) := by
    calc
      _ ↔ 0 < bary q a x i * total q a x * ‖x-a i‖^3 := (mul_pos_iff_of_pos_right (rx i)).symm
      _ ↔ 0 < bary q a y i * total q a y * ‖y-a i‖^3 := by rw [bary_product hx' sx i,bary_product hy' sy i]
      _ ↔ _ := mul_pos_iff_of_pos_right (ry i)
  obtain ⟨j,hj,kj⟩ := common_positive hnx hny
  have same := signs j
  rw [mul_pos_iff_of_pos_left hj,mul_pos_iff_of_pos_left kj] at same
  intro i
  rcases lt_or_gt_of_ne sx with h|h
  · have k : total q a y < 0 := lt_of_le_of_ne (not_lt.mp (fun e => h.not_gt (same.mpr e))) sy
    have e := signs i
    simp only [mul_pos_iff,h.not_gt,k.not_gt,h,k,and_false,and_true,false_or] at e
    have nx : bary q a x i ≠ 0 := fun t => hq i (by rw [← bary_product hx' sx i,t]; ring)
    have ny : bary q a y i ≠ 0 := fun t => hq i (by rw [← bary_product hy' sy i,t]; ring)
    grind
  · simpa only [mul_pos_iff_of_pos_right h,mul_pos_iff_of_pos_right (same.mp h)] using signs i

end MaxwellCausticExtremum

namespace MaxwellCausticExtremum.SecondVariation

private theorem min_second {f : ℝ → ℝ} (hm : IsLocalMin f 0) (hc : ContinuousAt f 0) :
    0 ≤ deriv (deriv f) 0 := by
  by_contra! hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 0] fun _ => f 0 := by
    filter_upwards [hm,hmax] with x h k
    exact le_antisymm k h
  have he' := he.deriv.deriv_eq
  simp at he'
  linarith

private theorem max_second {f : ℝ → ℝ} (hm : IsLocalMax f 0) (hc : ContinuousAt f 0) :
    deriv (deriv f) 0 ≤ 0 := by
  by_contra! hn
  have hmin := isLocalMin_of_deriv_deriv_pos hn hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 0] fun _ => f 0 := by
    filter_upwards [hm,hmin] with x h k
    exact le_antisymm h k
  have he' := he.deriv.deriv_eq
  simp at he'
  linarith

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def line (x v : V) (t : ℝ) := x + t • v

private theorem line_deriv (x v : V) (t : ℝ) : HasDerivAt (line x v) v t := by
  change HasDerivAt (fun t : ℝ => x + t • v) v t
  convert! (((hasDerivAt_id t).smul_const v).const_add x) using 1
  simp

theorem line_second {F : V → ℝ} {x : V} (v : V) (hc : ContDiffAt ℝ 2 F x) :
    deriv (deriv (F ∘ line x v)) 0 = iteratedFDeriv ℝ 2 F x ![v,v] := by
  have h0 : x = line x v 0 := by simp [line]
  have he : deriv (F ∘ line x v) =ᶠ[𝓝 0] fun t => fderiv ℝ F (line x v t) v := by
    have hlim := (line_deriv x v 0).continuousAt.tendsto
    rw [← h0] at hlim
    filter_upwards [hlim.eventually (hc.eventually (by norm_num))] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (line_deriv x v t)).deriv
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hg := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) (line_deriv x v 0) h0
  have hd := hg.clm_apply (hasDerivAt_const (0:ℝ) v)
  rw [he.deriv_eq,iteratedFDeriv_two_apply]
  simpa using hd.deriv

/-- The choice between the two inequalities is uniform over the entire plane. -/
theorem restricted_semidefinite {F : V → ℝ} {P : AffineSubspace ℝ V} {x : V}
    (hc : ContDiffAt ℝ 2 F x) (hx : x ∈ P) (hm : IsLocalExtrOn F (P : Set V) x) :
    (∀ v ∈ P.direction, 0 ≤ iteratedFDeriv ℝ 2 F x ![v,v]) ∨
    (∀ v ∈ P.direction, iteratedFDeriv ℝ 2 F x ![v,v] ≤ 0) := by
  have hmemb (v : V) (hv : v ∈ P.direction) (t : ℝ) : line x v t ∈ P := by
    simpa [line,add_comm] using P.vadd_mem_of_mem_direction (P.direction.smul_mem t hv) hx
  have hlim (v : V) (hv : v ∈ P.direction) : Tendsto (line x v) (𝓝 0) (𝓝[(P : Set V)] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa [line] using (line_deriv x v 0).continuousAt.tendsto,
      Eventually.of_forall (hmemb v hv)⟩
  have ct (v : V) : ContinuousAt (F ∘ line x v) 0 :=
    (by simpa [line] using hc.continuousAt : ContinuousAt F (line x v 0)).comp
      (line_deriv x v 0).continuousAt
  rcases hm with hm|hm
  · left
    intro v hv
    have hm' : IsLocalMinOn F (P : Set V) (line x v 0) := by
      rw [show line x v 0 = x by simp [line]]
      exact hm
    rw [← line_second v hc]
    exact min_second (hm'.comp_tendsto (by simpa [line] using hlim v hv)) (ct v)
  · right
    intro v hv
    have hm' : IsLocalMaxOn F (P : Set V) (line x v 0) := by
      rw [show line x v 0 = x by simp [line]]
      exact hm
    rw [← line_second v hc]
    exact max_second (hm'.comp_tendsto (by simpa [line] using hlim v hv)) (ct v)

abbrev E := EuclideanSpace ℝ (Fin 3)

theorem coulomb_semidefinite {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    {P : AffineSubspace ℝ E} (hx : x ∈ P) (he : x ∈ equilibria q a)
    (hm : IsLocalExtrOn (potential q a) (P : Set E) x) :
    (∀ v ∈ P.direction, 0 ≤ iteratedFDeriv ℝ 2 (potential q a) x ![v,v]) ∨
    (∀ v ∈ P.direction, iteratedFDeriv ℝ 2 (potential q a) x ![v,v] ≤ 0) := by
  apply restricted_semidefinite _ hx hm
  unfold potential
  apply ContDiffAt.sum
  intro i _
  have hn : x ≠ a i := fun e => he.1 ⟨i,e.symm⟩
  exact contDiffAt_const.div (contDiffAt_id.dist ℝ contDiffAt_const hn) (dist_ne_zero.mpr hn)

end MaxwellCausticExtremum.SecondVariation

namespace MaxwellCausticExtremum

def siteUnit (a : Fin 3 → E) (x : E) (i : Fin 3) : E := ‖x-a i‖⁻¹ • (x-a i)

theorem norm_siteUnit {a : Fin 3 → E} {x : E} (hx : x ∉ Set.range a) (i : Fin 3) :
    ‖siteUnit a x i‖ = 1 := by
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun e => hx ⟨i,e.symm⟩)
  simp [siteUnit,norm_smul,hn]

def normalizedForm (a : Fin 3 → E) (x : E) (l : Fin 3 → ℝ) (v w : E) : ℝ :=
  3*(∑ i, l i * ⟪siteUnit a x i,v⟫_ℝ * ⟪siteUnit a x i,w⟫_ℝ) - ⟪v,w⟫_ℝ

theorem normalized_hessian {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a) (v w : E) :
    fderiv ℝ (fderiv ℝ (potential q a)) x v w =
      total q a x * normalizedForm a x (bary q a x) v w := by
  have hB : fderiv ℝ (fderiv ℝ (potential q a)) x v w =
      iteratedFDeriv ℝ 2 (potential q a) x ![v,w] := by rw [iteratedFDeriv_two_apply]; rfl
  have hs := total_ne_zero ha hq he
  have hsum := (equilibrium_barycentric ha hq he).1
  rw [hB,potential_hessian q a he.1]
  unfold normalizedForm
  conv_rhs => rw [← one_mul ⟪v,w⟫_ℝ, ← hsum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hn := norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun e => he.1 ⟨i,e.symm⟩)
  simp only [bary,weight,siteUnit,real_inner_smul_left]
  field_simp [hs,hn]

theorem normalized_second {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a) (v : E) :
    iteratedFDeriv ℝ 2 (potential q a) x ![v,v] = total q a x *
      (3*(∑ i, bary q a x i * ⟪siteUnit a x i,v⟫_ℝ ^ 2)-‖v‖^2) := by
  rw [iteratedFDeriv_two_apply]
  change fderiv ℝ (fderiv ℝ (potential q a)) x v v = _
  rw [normalized_hessian ha hq he]
  simp only [normalizedForm, real_inner_self_eq_norm_sq, pow_two, mul_assoc]

private theorem exists_transverse (D : Submodule ℝ E) (hd : Module.finrank ℝ D = 2) (n : E) :
    ∃ v ∈ D, v ≠ 0 ∧ ⟪n,v⟫_ℝ = 0 := by
  let f := ((innerSL ℝ n).toLinearMap).comp D.subtype
  have hker : LinearMap.ker f ≠ ⊥ := by
    intro h
    have le := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp h)
    simp [hd] at le
  obtain ⟨v,hv,hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v,v.property,fun e => hne (Subtype.ext e),hv⟩

/-- A local extremum cannot have two negative barycentric coordinates.
The normalized second variation is positive in the direction of the exceptional
site and negative in a perpendicular direction in the same plane. -/
theorem exclude_vertex {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a)
    (hx : x ∈ affineSpan ℝ (Set.range a))
    (hm : IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x)
    (k : Fin 3) : ¬ (∀ i ≠ k, bary q a x i ≤ 0) := by
  intro hneg
  let P := affineSpan ℝ (Set.range a)
  let n := siteUnit a x
  let l := bary q a x
  let Q (v : E) := 3*(∑ i, l i * ⟪n i,v⟫_ℝ^2)-‖v‖^2
  have hs : ∑ i, l i = 1 := (equilibrium_barycentric ha hq he).1
  have hn (i : Fin 3) : ‖n i‖ = 1 := norm_siteUnit he.1 i
  have hk : n k ∈ P.direction := P.direction.smul_mem _
    (P.vsub_mem_direction hx (subset_affineSpan ℝ _ ⟨k,rfl⟩))
  have hd : Module.finrank ℝ P.direction = 2 := by
    rw [show P.direction = vectorSpan ℝ (Set.range a) from direction_affineSpan ..]
    exact ha.finrank_vectorSpan (by decide)
  obtain ⟨w,hw,hw0,hwk⟩ := exists_transverse P.direction hd (n k)
  have pos : 0 < Q (n k) := by
    have hcmp : ∑ i, l i ≤ ∑ i, l i * ⟪n i,n k⟫_ℝ^2 := by
      apply Finset.sum_le_sum
      intro i _
      by_cases e : i=k
      · simp [e,hn]
      · have bound := abs_real_inner_le_norm (n i) (n k)
        rw [hn,hn,one_mul] at bound
        have sq : ⟪n i,n k⟫_ℝ^2 ≤ 1 := by
          have := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr bound
          simpa using this
        simpa using mul_le_mul_of_nonpos_left sq (hneg i e)
    rw [hs] at hcmp
    dsimp only [Q]
    rw [hn]
    linarith
  have neg : Q w < 0 := by
    have hsum : ∑ i, l i * ⟪n i,w⟫_ℝ^2 ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      by_cases e : i=k
      · simp [e,hwk]
      · exact mul_nonpos_of_nonpos_of_nonneg (hneg i e) (sq_nonneg _)
    dsimp only [Q]
    linarith [sq_pos_of_pos (norm_pos_iff.mpr hw0)]
  have eq (v : E) : iteratedFDeriv ℝ 2 (potential q a) x ![v,v] = total q a x * Q v :=
    normalized_second ha hq he v
  have semi := SecondVariation.coulomb_semidefinite hx he hm
  rcases semi with semi|semi
  · have e := semi (n k) hk
    have f := semi w hw
    rw [eq] at e f
    rcases lt_or_gt_of_ne (total_ne_zero ha hq he) with s|s
    · exact (mul_neg_of_neg_of_pos s pos).not_ge e
    · exact (mul_neg_of_pos_of_neg s neg).not_ge f
  · have e := semi (n k) hk
    have f := semi w hw
    rw [eq] at e f
    rcases lt_or_gt_of_ne (total_ne_zero ha hq he) with s|s
    · exact (mul_pos_of_neg_of_neg s neg).not_ge f
    · exact (mul_pos s pos).not_ge e

theorem extremum_nonvertex {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a)
    (hx : x ∈ affineSpan ℝ (Set.range a))
    (hm : IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x) :
    nonvertex (bary q a x) := by
  have hn := exclude_vertex ha hq he hx hm
  by_contra h
  unfold nonvertex at h
  by_cases h0 : 0 < bary q a x 0
  · apply hn 0
    intro i hi
    fin_cases i <;> simp_all
  by_cases h1 : 0 < bary q a x 1
  · apply hn 1
    intro i hi
    fin_cases i <;> simp_all
  · apply hn 2
    intro i hi
    fin_cases i <;> simp_all

end MaxwellCausticExtremum

namespace MaxwellCausticExtremum

private theorem expand_quadratic (B : E →L[ℝ] (E →L[ℝ] ℝ))
    (sym : ∀ v w, B v w = B w v) (u v : E) (t : ℝ) :
    B (t • u+v) (t • u+v) = B u u*(t*t) + (2*B u v)*t + B v v := by
  simp only [map_add,map_smul,add_apply,smul_apply,
    smul_eq_mul,sym v u]
  ring

/-- At a nondegenerate equilibrium that is an extremum on the source plane,
the planar Hessian determinant is strictly positive in any independent frame. -/
theorem extremum_det_pos {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (he : x ∈ equilibria q a)
    (hnd : HasNondegenerateHessianAt (potential q a) x)
    (hx : x ∈ affineSpan ℝ (Set.range a))
    (hm : IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x)
    (v w : E) (hv : v ∈ (affineSpan ℝ (Set.range a)).direction)
    (hw : w ∈ (affineSpan ℝ (Set.range a)).direction)
    (hv0 : v ≠ 0) (hind : ∀ t : ℝ, t • v + w ≠ 0) :
    let B := fderiv ℝ (fderiv ℝ (potential q a)) x
    0 < B v v * B w w - (B v w)^2 := by
  let P := affineSpan ℝ (Set.range a)
  let D := P.direction
  let B := fderiv ℝ (fderiv ℝ (potential q a)) x
  have hb (u z : E) : iteratedFDeriv ℝ 2 (potential q a) x ![u,z] = B u z := by
    rw [iteratedFDeriv_two_apply]; rfl
  have sym (u z : E) : B u z = B z u := by
    rw [← hb, ← hb, potential_hessian q a he.1,potential_hessian q a he.1]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm z u]
    ring
  have semi := SecondVariation.coulomb_semidefinite hx he hm
  simp only [hb] at semi
  have nz (u : E) (hu : u ∈ D) (hne : u ≠ 0) : B u u ≠ 0 := by
    intro hz
    obtain ⟨d,hd,hy⟩ := MaxwellIndexCount.planar_hessian_nondegenerate q a he.1 hx hnd u hu hne
    rw [hb] at hy
    have quad (t : ℝ) := expand_quadratic B sym d u t
    have mem (t : ℝ) := D.add_mem (D.smul_mem t hd) hu
    have discr : discrim (B d d) (2*B d u) (B u u) ≤ 0 := by
      rcases semi with hp|hn
      · exact discrim_le_zero fun t => (quad t) ▸ hp _ (mem t)
      · exact discrim_le_zero_of_nonpos fun t => (quad t) ▸ hn _ (mem t)
    simp only [discrim,hz,mul_zero,sub_zero] at discr
    have e : B d u = 0 := by nlinarith [sq_nonneg (B d u)]
    exact hy ((sym u d).trans e)
  have lineMem (t : ℝ) := D.add_mem (D.smul_mem t hv) hw
  have expand := expand_quadratic B sym v w
  have discr : discrim (B v v) (2*B v w) (B w w) < 0 := by
    rcases semi with hp|hn
    · apply discrim_lt_zero (nz v hv hv0)
      intro t
      rw [← expand]
      exact lt_of_le_of_ne (hp _ (lineMem t)) (nz _ (lineMem t) (hind t)).symm
    · apply discrim_lt_zero_of_neg (nz v hv hv0)
      intro t
      rw [← expand]
      exact lt_of_le_of_ne (hn _ (lineMem t)) (nz _ (lineMem t) (hind t))
  change 0 < B v v * B w w - (B v w)^2
  unfold discrim at discr
  linarith

end MaxwellCausticExtremum

namespace MaxwellCausticExtremum

/-- Charges prescribed by a point and its affine coordinates, before rescaling. -/
def prescribed (a : Fin 3 → E) (x : E) (l : Fin 3 → ℝ) (i : Fin 3) :=
  l i * ‖x-a i‖^3

def logRatios (Q : Fin 3 → ℝ) : ℝ × ℝ :=
  (Real.log |Q 1/Q 0|, Real.log |Q 2/Q 0|)

/-- The positive-determinant region, expressed without prescribing fixed charges.
Using all independent frames makes this predicate independent of a choice of axes. -/
def positiveSheet (a : Fin 3 → E) (x : E) (l : Fin 3 → ℝ) : Prop :=
  let D := (affineSpan ℝ (Set.range a)).direction
  let H := normalizedForm a x l
  ∀ v ∈ D, ∀ w ∈ D, v ≠ 0 → (∀ t : ℝ, t • v+w ≠ 0) →
    0 < H v v*H w w-(H v w)^2

theorem extremum_on_positiveSheet {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a)
    (hnd : HasNondegenerateHessianAt (potential q a) x)
    (hx : x ∈ affineSpan ℝ (Set.range a))
    (hm : IsLocalExtrOn (potential q a) (affineSpan ℝ (Set.range a) : Set E) x) :
    positiveSheet a x (bary q a x) := by
  intro v hv w hw hv0 hind
  have hp := extremum_det_pos he hnd hx hm v w hv hw hv0 hind
  dsimp only at hp
  simp only [normalized_hessian ha hq he] at hp
  let H := normalizedForm a x (bary q a x)
  have e : 0 < (total q a x)^2 * (H v v*H w w-(H v w)^2) := by
    dsimp only [H]
    linarith only [hp]
  exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero (total_ne_zero ha hq he))).mp e

theorem equilibrium_logRatios {q : Fin 3 → ℝ} {a : Fin 3 → E} {x : E}
    (ha : AffineIndependent ℝ a) (hq : q 0 ≠ 0) (he : x ∈ equilibria q a) :
    logRatios (prescribed a x (bary q a x)) = logRatios q := by
  have hs := total_ne_zero ha hq he
  have hp (i : Fin 3) : prescribed a x (bary q a x) i = q i / total q a x := by
    apply (eq_div_iff hs).mpr
    unfold prescribed
    rw [mul_right_comm,bary_product he.1 hs]
  simp [logRatios,hp,div_div_div_cancel_right₀ hs]

/-- The remaining uniqueness assertion is entirely about the prescribed charge
map on one sign chamber of the positive sheet. -/
theorem extremum_count_of_sheet_injectivity
    (hinj : ∀ (a : Fin 3 → E), AffineIndependent ℝ a → ∀ (x y : E) (l m : Fin 3 → ℝ),
      (∑ i, l i = 1) → (∑ i, l i • a i = x) →
      (∑ i, m i = 1) → (∑ i, m i • a i = y) →
      x ∉ Set.range a → y ∉ Set.range a →
      (∀ i, l i ≠ 0) → (∀ i, m i ≠ 0) → nonvertex l →
      (∀ i, 0 < l i ↔ 0 < m i) → positiveSheet a x l → positiveSheet a y m →
      logRatios (prescribed a x l) = logRatios (prescribed a y m) → x = y) :
    ∀ (q : Fin 3 → ℝ) (a : Fin 3 → E),
      AffineIndependent ℝ a → (∀ i, q i ≠ 0) →
      (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
      let P := (affineSpan ℝ (Set.range a) : Set E)
      {x | x ∈ P ∧ x ∈ equilibria q a ∧ IsLocalExtrOn (potential q a) P x}.encard ≤ 1 := by
  intro q a ha hq hnd
  apply Set.encard_le_one_iff_subsingleton.mpr
  intro x hx y hy
  obtain ⟨hpx,hex,hmx⟩ := hx
  obtain ⟨hpy,hey,hmy⟩ := hy
  have nz {z : E} (he : z ∈ equilibria q a) (i : Fin 3) : bary q a z i ≠ 0 := by
    intro e
    exact hq i (by rw [← bary_product he.1 (total_ne_zero ha (hq 0) he) i,e]; ring)
  obtain ⟨sx,mx⟩ := equilibrium_barycentric ha (hq 0) hex
  obtain ⟨sy,my⟩ := equilibrium_barycentric ha (hq 0) hey
  have nx := extremum_nonvertex ha (hq 0) hex hpx hmx
  have ny := extremum_nonvertex ha (hq 0) hey hpy hmy
  exact hinj a ha x y _ _ sx mx sy my hex.1 hey.1 (nz hex) (nz hey) nx
    (same_nonvertex_chamber ha hq hex hey nx ny)
    (extremum_on_positiveSheet ha (hq 0) hex (hnd x hex) hpx hmx)
    (extremum_on_positiveSheet ha (hq 0) hey (hnd y hey) hpy hmy)
    ((equilibrium_logRatios ha (hq 0) hex).trans (equilibrium_logRatios ha (hq 0) hey).symm)

end MaxwellCausticExtremum

end
end

section

noncomputable section
open Set InnerProductSpace
namespace MaxwellCausticExtremum

namespace Frame
def site (s h : ℝ) : Fin 3 → ℝ × ℝ := ![(0,0),(1,0),(s,h)]

theorem point_site {a : Fin 3 → E} (T : Triangle a) (i : Fin 3) : point T (site T.s T.h i)=a i := by
  fin_cases i <;> simp [point,site,T.site_one,T.site_two]

def fromWeights {a : Fin 3 → E} (T : Triangle a) (l : Fin 3 → ℝ) : ℝ × ℝ :=
  (l 1+T.s*l 2,T.h*l 2)

theorem weights_point {a : Fin 3 → E} (T : Triangle a) (l : Fin 3 → ℝ) (mass : ∑ i,l i=1) :
    point T (fromWeights T l)=∑ i,l i • a i := by
  simp only [Fin.sum_univ_three] at mass ⊢
  rw [T.site_one,T.site_two,show l 0=1-l 1-l 2 by linarith]
  dsimp [point,fromWeights]; module

theorem chart_weights {a : Fin 3 → E} (T : Triangle a) (l : Fin 3 → ℝ) (mass : ∑ i,l i=1) :
    Chart.coordinates T.s T.h (fromWeights T l).1 (fromWeights T l).2=l := by
  simp only [Fin.sum_univ_three] at mass
  funext i; fin_cases i <;> dsimp [Chart.coordinates,fromWeights] <;> field_simp [T.h_pos.ne'] <;> linarith

private theorem diff_site {a : Fin 3 → E} (T : Triangle a) (p : ℝ × ℝ) (i : Fin 3) :
    point T p-a i=T.d • (Chart.dx T.s p.1 i • T.u+Chart.dy T.h p.2 i • T.v) := by
  rw [← point_site T i]
  fin_cases i <;> dsimp [point,site,Chart.dx,Chart.dy] <;> module

theorem dist_site {a : Fin 3 → E} (T : Triangle a) (p : ℝ × ℝ) (i : Fin 3) :
    ‖point T p-a i‖=T.d*Real.sqrt (Chart.radii T.s T.h p.1 p.2 i) := by
  have e := point_distance_sq T p (site T.s T.h i)
  rw [point_site] at e
  have rad : (p.1-(site T.s T.h i).1)^2+(p.2-(site T.s T.h i).2)^2=Chart.radii T.s T.h p.1 p.2 i := by
    fin_cases i <;> simp [site,Chart.radii]
  rw [rad] at e
  have pos : 0≤Chart.radii T.s T.h p.1 p.2 i := by rw [Chart.radii_eq]; positivity
  exact (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg T.d_pos.le (Real.sqrt_nonneg _))).mp
    (by rw [mul_pow,Real.sq_sqrt pos]; exact e)

theorem charge_coords {a : Fin 3 → E} (T : Triangle a) (p : Chart.Plane) (l : Fin 3 → ℝ)
    (el : Chart.coordinates T.s T.h p.1 p.2=l) (hl : ∀ i,l i ≠ 0) :
    logRatios (prescribed a (point T p) l)=Chart.chargeMap T.s T.h p := by
  let r := Chart.radii T.s T.h p.1 p.2
  have hp i := Chart.radii_pos_of_chamber _ _ p T.h_pos.ne' (el ▸ hl) i
  have eq (i : Fin 3) : Real.log |prescribed a (point T p) l i|=
      Chart.logCharge T.s T.h p.1 p.2 i+3*Real.log T.d := by
    rw [Chart.logCharge_eq _ _ _ _ i (el ▸ hl i) (hp i),el]
    simp only [prescribed,dist_site,mul_pow,Real.log_abs]
    have nzR : Real.sqrt (r i)^3 ≠ 0 := pow_ne_zero _ (Real.sqrt_pos.mpr (hp i)).ne'
    rw [Real.log_mul (hl i) (mul_ne_zero (pow_ne_zero 3 T.d_pos.ne') nzR),
      Real.log_mul (pow_ne_zero 3 T.d_pos.ne') nzR,
      Real.log_mul (hl i) nzR,Real.log_pow]; ring
  have nz (i : Fin 3) : prescribed a (point T p) l i ≠ 0 :=
    mul_ne_zero (hl i) (by rw [dist_site]; exact pow_ne_zero _ (mul_ne_zero T.d_pos.ne' (Real.sqrt_pos.mpr (hp i)).ne'))
  apply Prod.ext <;> dsimp [logRatios,Chart.chargeMap] <;>
    rw [Real.log_abs,Real.log_div (nz _) (nz _)] <;>
    simp only [Real.log_abs] at eq <;> rw [eq,eq] <;> ring

theorem sheet_det_pos {a : Fin 3 → E} (T : Triangle a) (p : Chart.Plane) (l : Fin 3 → ℝ)
    (el : Chart.coordinates T.s T.h p.1 p.2=l) (hl : ∀ i,l i ≠ 0)
    (pos : positiveSheet a (point T p) l) : 0<Chart.detH T.s T.h p.1 p.2 := by
  let D := (affineSpan ℝ (range a)).direction
  have mem (z : Chart.Plane) : point T z ∈ affineSpan ℝ (range a) := (Set.ext_iff.mp (point_range T) _).mp ⟨z,rfl⟩
  have basis (z : Chart.Plane) : z.1 • T.u+z.2 • T.v ∈ D := by
    have d := (affineSpan ℝ (range a)).vsub_mem_direction (mem z) (mem (0,0))
    have tmp : T.d • (z.1 • T.u+z.2 • T.v) ∈ D := by simpa [point] using d
    simpa [smul_smul,T.d_pos.ne'] using D.smul_mem T.d⁻¹ tmp
  have pu := pos T.u (by simpa using basis (1,0)) T.v (by simpa using basis (0,1))
    (norm_ne_zero_iff.mp (T.unit_u.trans_ne one_ne_zero)) (by
      intro t eq
      have e := congrArg (fun w => ⟪w,T.v⟫_ℝ) eq
      simp [inner_add_left,real_inner_smul_left,T.perp,T.unit_v] at e)
  have vu := (real_inner_comm T.u T.v).trans T.perp
  let r := Chart.radii T.s T.h p.1 p.2
  let x := Chart.dx T.s p.1
  let y := Chart.dy T.h p.2
  have hp (i : Fin 3) : 0 < r i := Chart.radii_pos_of_chamber _ _ p T.h_pos.ne' (el ▸ hl) i
  have iu i : ⟪siteUnit a (point T p) i,T.u⟫_ℝ=x i/Real.sqrt (r i) := by
    unfold siteUnit
    rw [dist_site,diff_site]
    simp [x,r,inner_add_left,real_inner_smul_left,vu,T.unit_u,div_eq_mul_inv,mul_comm,mul_left_comm]
    field_simp [T.d_pos.ne']
  have iv i : ⟪siteUnit a (point T p) i,T.v⟫_ℝ=y i/Real.sqrt (r i) := by
    unfold siteUnit
    rw [dist_site,diff_site]
    simp [y,r,inner_add_left,real_inner_smul_left,T.perp,T.unit_v,div_eq_mul_inv,mul_comm,mul_left_comm]
    field_simp [T.d_pos.ne']
  let G (f g : Fin 3 → ℝ) := ∑ i,l i/r i*f i*g i
  have entry (f g : Fin 3 → ℝ) :
      (∑ i,l i*(f i/Real.sqrt (r i))*(g i/Real.sqrt (r i)))=G f g := by
    apply Finset.sum_congr rfl; intro i _
    rw [show l i*(f i/Real.sqrt (r i))*(g i/Real.sqrt (r i))=l i*f i*g i/Real.sqrt (r i)^2 by ring,
      Real.sq_sqrt (hp i).le]; ring
  simp only [normalizedForm,iu,iv,entry,real_inner_self_eq_norm_sq,T.unit_u,T.unit_v,one_pow,T.perp,sub_zero] at pu
  change 0 < (3*G x x-1)*(3*G y y-1)-(3*G x y)^2 at pu
  unfold Chart.detH
  rw [el]
  convert! pu using 1
  simp [G,x,y,r,Chart.dx,Chart.dy,Fin.sum_univ_three,pow_two,mul_assoc,Matrix.cons_val_two]

end Frame

theorem extremum_of_chart_injective
    (inj : ∀ s h : ℝ, 0<h → ∀ c : Fin 4, InjOn (Chart.chargeMap s h)
      {p | (∀ i, 0<Chart.chamberSigns c i*Chart.coordinates s h p.1 p.2 i) ∧ 0≤Chart.detH s h p.1 p.2}) :
    ∀ (q : Fin 3 → ℝ) (a : Fin 3 → E), AffineIndependent ℝ a → (∀ i, q i ≠ 0) →
      (∀ x ∈ Arxiv.«2607.27197».equilibria q a, Arxiv.«2607.27197».HasNondegenerateHessianAt
        (Arxiv.«2607.27197».potential q a) x) →
      let P := (affineSpan ℝ (range a) : Set E)
      {x | x ∈ P ∧ x ∈ Arxiv.«2607.27197».equilibria q a ∧
        IsLocalExtrOn (Arxiv.«2607.27197».potential q a) P x}.encard ≤ 1 := by
  apply extremum_count_of_sheet_injectivity
  intro a ha x y l m ls lx ms mx _ _ nl nm nv same px py eq
  obtain ⟨T⟩ := Frame.exists_triangle ha
  let p := Frame.fromWeights T l
  let r := Frame.fromWeights T m
  have ep : Frame.point T p=x := (Frame.weights_point T l ls).trans lx
  have er : Frame.point T r=y := (Frame.weights_point T m ms).trans mx
  have el := Frame.chart_weights T l ls
  have em := Frame.chart_weights T m ms
  have ch : ∃ c : Fin 4, ∀ i, 0<Chart.chamberSigns c i*l i := by
    unfold nonvertex at nv
    by_cases a : l 0 < 0
    · have b : 0<l 1 := by grind
      have d : 0<l 2 := by grind
      exact ⟨1,by intro i; fin_cases i <;> norm_num [Chart.chamberSigns,Matrix.cons_val_two] <;> assumption⟩
    have ap : 0<l 0 := lt_of_le_of_ne (le_of_not_gt a) (Ne.symm (nl 0))
    by_cases b : l 1 < 0
    · have d : 0<l 2 := by grind
      exact ⟨2,by intro i; fin_cases i <;> norm_num [Chart.chamberSigns,Matrix.cons_val_two] <;> assumption⟩
    have bp : 0<l 1 := lt_of_le_of_ne (le_of_not_gt b) (Ne.symm (nl 1))
    by_cases d : l 2 < 0
    · exact ⟨3,by
        intro i; fin_cases i
        · change 0 < (1:ℝ)*l 0; simpa using ap
        · change 0 < (1:ℝ)*l 1; simpa using bp
        · change 0 < (-1:ℝ)*l 2; simpa using d⟩
    have dp : 0<l 2 := lt_of_le_of_ne (le_of_not_gt d) (Ne.symm (nl 2))
    exact ⟨0,by intro i; fin_cases i <;> norm_num [Chart.chamberSigns,Matrix.cons_val_two] <;> assumption⟩
  obtain ⟨c,hc⟩ := ch
  have mc i : 0<Chart.chamberSigns c i*m i := by
    rcases mul_pos_iff.mp (hc i) with ⟨sl,lp⟩|⟨sl,ln⟩
    · exact mul_pos sl ((same i).mp lp)
    · exact mul_pos_of_neg_of_neg sl (lt_of_le_of_ne (le_of_not_gt fun h => ln.not_gt ((same i).mpr h)) (nm i))
  rw [← ep] at px
  rw [← er] at py
  rw [← ep,← er] at eq ⊢
  have e : p=r := inj T.s T.h T.h_pos c (by
    exact ⟨el ▸ hc,(Frame.sheet_det_pos T p l el nl px).le⟩) (by
    exact ⟨em ▸ mc,(Frame.sheet_det_pos T r m em nm py).le⟩)
    (by rwa [← Frame.charge_coords T p l el nl,← Frame.charge_coords T r m em nm])
  rw [e]
end MaxwellCausticExtremum

end
end

section

noncomputable section
open Set Filter Topology
namespace MaxwellCausticExtremum.Chart

theorem sheet_injective (s h : ℝ) (hh : 0<h) (c : Fin 4) :
    InjOn (chargeMap s h) {p : Plane | (∀ i, 0<chamberSigns c i*coordinates s h p.1 p.2 i) ∧
      0≤detH s h p.1 p.2} := by
  let C := {p : Plane | ∀ i, 0<chamberSigns c i*coordinates s h p.1 p.2 i}
  let J (p : Plane) := detH s h p.1 p.2
  let S := {p : Plane | p ∈ C ∧ 0≤J p}
  let T := {p : Plane | p ∈ C ∧ J p=0}
  let B : Set S := Subtype.val ⁻¹' T
  let F (p : S) := chargeMap s h p.val
  have hc : IsOpen C := by
    have e := path_chamber_open (fun _ => s) (fun _ => h) (chamberSigns c) continuous_const continuous_const
    have ext : C=(fun z : Plane => ((0:ℝ),z)) ⁻¹' {p : ℝ × Plane | h≠0 ∧
        ∀ i, 0<chamberSigns c i*coordinates s h p.2.1 p.2.2 i} := by ext; simp [C,hh.ne']
    rw [ext]; exact e.preimage (by fun_prop)
  have signs (i : Fin 3) : chamberSigns c i≠0 := by fin_cases c <;> fin_cases i <;> norm_num [chamberSigns]
  have comp : IsCompact S := by
    have cp := path_sheet_compact (fun _ => s) (fun _ => h) (chamberSigns c) continuous_const continuous_const
      (fun _ _ => hh.ne') signs
    have res : Prod.snd '' {p : ℝ × Plane | p.1 ∈ Icc (0:ℝ) 1 ∧ p.2 ∈ S}=S := by
      ext z; exact ⟨fun ⟨v,h,e⟩ => e ▸ h.2,fun hz => ⟨(0,z),⟨by simp,hz⟩,rfl⟩⟩
    rw [← res]; exact cp.image continuous_snd
  let := isCompact_iff_compactSpace.mp comp
  have pc : IsPreconnected B := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    have e : Subtype.val '' B=T := by
      ext p
      exact ⟨fun ⟨z,hz,he⟩ => he ▸ hz,fun hp => ⟨⟨p,hp.1,hp.2.ge⟩,hp,rfl⟩⟩
    rw [e]; exact boundary_preconnected s h hh c
  have hl (p : S) (i : Fin 3) := right_ne_zero_of_mul (p.2.1 i).ne'
  have hr (p : S) (i : Fin 3) := (radii_pos_of_chamber s h p.1 hh.ne' (hl p) i).ne'
  have cont : Continuous F := continuous_iff_continuousAt.mpr fun p =>
    (chargeMap_smooth s h p.1 (hl p) (hr p)).continuousAt.comp continuous_subtype_val.continuousAt
  have nz {p : S} (hp : p ∈ Bᶜ) : J p.1 ≠ 0 := fun e => hp ⟨p.2.1,e⟩
  have localVal : IsLocalHomeomorphOn (Subtype.val : S → Plane) Bᶜ := by
    apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
    intro p hp
    have diff : ContinuousAt J p.1 := by
      have rr (i : Fin 3) : ContinuousAt (fun z : Plane => radii s h z.1 z.2 i) p.1 := by
        fin_cases i <;> dsimp [radii] <;> fun_prop
      have dl (i : Fin 3) : ContinuousAt (fun z : Plane => coordinates s h z.1 z.2 i) p.1 := by
        fin_cases i <;> dsimp [coordinates] <;> fun_prop
      unfold J detH
      dsimp only [Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      fun_prop (disch := exact hr p _)
    have mem : p.1 ∈ interior S := mem_interior_iff_mem_nhds.mpr <|
      inter_mem (hc.mem_nhds p.2.1) ((continuousAt_const.eventually_lt diff (lt_of_le_of_ne p.2.2 (nz hp).symm)).mono
        fun _ h => h.le)
    let U : Set S := Subtype.val ⁻¹' interior S
    refine ⟨U,continuous_subtype_val.continuousAt.preimage_mem_nhds (isOpen_interior.mem_nhds mem),?_⟩
    have eq : range (U.domRestrict (Subtype.val : S → Plane))=interior S := by
      ext p; exact ⟨fun ⟨v,h⟩ => h ▸ v.2,fun h => ⟨⟨⟨p,interior_subset h⟩,h⟩,rfl⟩⟩
    exact ⟨IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal,eq ▸ isOpen_interior⟩
  have regular : IsLocalHomeomorphOn F Bᶜ :=
    (chargeMap_regular s h hh.ne').comp localVal (fun p hp => ⟨hl p,hr p,nz hp⟩)
  have binj : InjOn F B := fun p hp q hq eq => Subtype.ext (boundary_injective s h hh c hp hq eq)
  have loc (p : S) (hp : p ∈ B) : ∃ U ∈ 𝓝 p, InjOn F U := by
    obtain ⟨U,hU,inj⟩ := boundary_local s h hh (chamberSigns c) p.1 p.2.1 hp.2
    exact ⟨Subtype.val ⁻¹' U,continuous_subtype_val.continuousAt.preimage_mem_nhds hU,
      fun v hv w hw eq => Subtype.ext (inj ⟨hv,v.2⟩ ⟨hw,w.2⟩ eq)⟩
  have inj := Finish.one_sheet B pc cont regular binj loc
  intro p hp q hq eq
  exact congrArg Subtype.val (inj (a₁ := ⟨p,hp⟩) (a₂ := ⟨q,hq⟩) eq)

end MaxwellCausticExtremum.Chart

namespace MaxwellCausticExtremum
open Arxiv.«2607.27197»

theorem at_most_one_extremum :
    ∀ (q : Fin 3 → ℝ) (a : Fin 3 → E), AffineIndependent ℝ a → (∀ i,q i ≠ 0) →
      (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
      let P := (affineSpan ℝ (Set.range a) : Set E)
      {x | x ∈ P ∧ x ∈ equilibria q a ∧ IsLocalExtrOn (potential q a) P x}.encard ≤ 1 :=
  extremum_of_chart_injective Chart.sheet_injective

end MaxwellCausticExtremum

end
end

theorem OMA.solution : OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_charges_R1.H1 := by
  intro q a ha hq hnd
  have extrema := MaxwellCausticExtremum.at_most_one_extremum q a ha hq hnd
  exact (MaxwellIndexCount.index_count_bound q a ha hq hnd).trans (calc
    _ ≤ 2*(1:ℕ∞)+2 := add_le_add (mul_le_mul_of_nonneg_left extrema (by norm_num)) le_rfl
    _ = 4 := by norm_num)
