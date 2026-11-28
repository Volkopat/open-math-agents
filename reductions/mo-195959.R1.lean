import OMAStatements.S_mo_195959

open MeasureTheory Filter Set
open scoped Topology NNReal BoundedContinuousFunction

namespace OMA.R_mo_195959_R1

lemma crossing (t s m : ℝ) (x y : ℝ≥0)
    (hx : Real.exp (-(x:ℝ)*m) < (Real.exp (-(x:ℝ)*t)+Real.exp (-(x:ℝ)*s))/2)
    (hy : (Real.exp (-(y:ℝ)*t)+Real.exp (-(y:ℝ)*s))/2 < Real.exp (-(y:ℝ)*m)) :
    y ≤ x := by
  by_contra! hxy
  let F := fun z : ℝ => Real.exp ((m-t)*z) + Real.exp ((m-s)*z)
  have linear_exp (c : ℝ) : ConvexOn ℝ Set.univ (fun z : ℝ => Real.exp (c*z)) := by
    convert! convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ c) using 1
  have cv : ConvexOn ℝ Set.univ F := (linear_exp _).add (linear_exp _)
  have hrep (z : ℝ) : F z =
      (Real.exp (-z*t)+Real.exp (-z*s))*Real.exp (z*m) := by
    dsimp [F]
    rw [add_mul,← Real.exp_add,← Real.exp_add]
    congr 2 <;> ring
  have one (z : ℝ) : Real.exp (-z*m)*Real.exp (z*m)=1 := by
    rw [← Real.exp_add,show -z*m+z*m=0 by ring,Real.exp_zero]
  have xgt := mul_lt_mul_of_pos_right hx (Real.exp_pos ((x:ℝ)*m))
  have ylt := mul_lt_mul_of_pos_right hy (Real.exp_pos ((y:ℝ)*m))
  rw [one] at xgt ylt
  have hx' : 2 < F x := by rw [hrep]; linarith
  have hy' : F y < 2 := by rw [hrep]; linarith
  have hz : F 0 = 2 := by norm_num [F]
  have inside : (x:ℝ) ∈ segment ℝ 0 (y:ℝ) := by
    exact Icc_subset_segment (show (x:ℝ) ∈ Set.Icc (0:ℝ) (y:ℝ) from ⟨x.2,hxy.le⟩)
  have h := cv.le_on_segment (Set.mem_univ 0) (Set.mem_univ _) inside
  rw [hz,max_eq_left hy'.le] at h
  linarith

lemma threshold (Z H : ℝ≥0 → ℝ) (hZ : Antitone Z) (hH : Antitone H)
    (bounded : ∀ x, 0≤Z x+H x ∧ Z x+H x≤2)
    (order : ∀ x y, Z x < H x → H y < Z y → y ≤ x) :
    ∃ d : ℝ, ∀ x, 0 ≤ (Z x-H x)*(Z x+H x-d) := by
  let S : Set ℝ := insert 0 ((fun x => Z x+H x) '' {x | Z x < H x})
  have bdd : BddAbove S := by
    refine ⟨2,?_⟩
    rintro a (rfl | ⟨x,_,rfl⟩)
    · norm_num
    · exact (bounded x).2
  refine ⟨sSup S, fun x => ?_⟩
  rcases lt_trichotomy (Z x) (H x) with h|h|h
  · have hh : Z x+H x ≤ sSup S := le_csSup bdd (Or.inr ⟨x,h,rfl⟩)
    exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  · simp [h]
  · have hh : sSup S ≤ Z x+H x := by
      apply csSup_le (Set.insert_nonempty _ _)
      rintro a (rfl | ⟨y,hy,rfl⟩)
      · exact (bounded x).1
      · exact add_le_add (hZ (order y x hy h)) (hH (order y x hy h))
    exact mul_nonneg (by linarith) (by linarith)

lemma positive_variance (E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ) (unity : E 1=1)
    (pos : ∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g) (D : ℝ≥0 →ᵇ ℝ) :
    (E D)^2 ≤ E (D*D) := by
  have h := pos (D*D - (2*E D) • D + ((E D)^2) • 1) (fun x => by
    change 0 ≤ D x * D x - (2*E D)*D x + (E D)^2*1
    nlinarith [sq_nonneg (D x-E D)])
  simp only [map_add,map_sub,map_smul,smul_eq_mul,unity,mul_one] at h
  nlinarith

lemma compare (E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ) (unity : E 1=1)
    (pos : ∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g)
    (A B Z : ℝ≥0 →ᵇ ℝ) (avg : E Z = (E A+E B)/2)
    (cross : ∃ d : ℝ, ∀ x, 0 ≤ (Z x-(A x+B x)/2)*(Z x+(A x+B x)/2-d)) :
    E (A*B)-E A*E B ≤ E (Z*Z)-(E Z)^2 := by
  let H : ℝ≥0 →ᵇ ℝ := (1/2:ℝ) • (A+B)
  let D : ℝ≥0 →ᵇ ℝ := (1/2:ℝ) • (A-B)
  have hH : E H = (E A+E B)/2 := by simp [H]; ring
  have hD : E D = (E A-E B)/2 := by simp [D]; ring
  obtain ⟨d,hd⟩ := cross
  have hz := pos (Z*Z - H*H - d • (Z-H)) (fun x => by
    change 0 ≤ Z x*Z x - (1/2*(A x+B x))*(1/2*(A x+B x))-d*(Z x-1/2*(A x+B x))
    nlinarith [hd x])
  have prod : H*H-D*D = A*B := by
    ext x
    change (1/2*(A x+B x))*(1/2*(A x+B x)) -
      (1/2*(A x-B x))*(1/2*(A x-B x)) = A x*B x
    ring
  have hh := congrArg E prod
  simp only [map_sub,map_smul,smul_eq_mul,hH,avg,sub_self,mul_zero,sub_zero] at hz
  rw [map_sub] at hh
  have hv := positive_variance E unity pos D
  rw [hD] at hv
  rw [avg]
  nlinarith


open OMA.S_mo_195959

/-- Finite-measure Bernstein-Widder representation on the open positive half-line. -/
def H1 : Prop := ∀ f : ℝ → ℝ, ContinuousOn f (Set.Ici 0) → f 0 = 1 →
    CompletelyMonotoneOn f (Set.Ioi 0) →
    ∃ μ : Measure ℝ≥0, IsFiniteMeasure μ ∧
      ∀ t : ℝ, 0 < t → f t = ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ

/-- The right limit at zero of a finite measure's Laplace transform is its mass. -/
def H2 : Prop := ∀ μ : Measure ℝ≥0, IsFiniteMeasure μ →
    Tendsto (fun t : ℝ => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ)
      (𝓝[>] (0:ℝ)) (𝓝 (∫ _ : ℝ≥0, (1:ℝ) ∂μ))

lemma normalized_integral (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (mass : (∫ _ : ℝ≥0, (1:ℝ) ∂μ) = 1) :
    ∃ E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ, E 1 = 1 ∧
      (∀ g : ℝ≥0 →ᵇ ℝ, (∀ x, 0≤g x) → 0≤E g) ∧
      ∀ g : ℝ≥0 →ᵇ ℝ, E g = ∫ r, g r ∂μ := by
  let E : (ℝ≥0 →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun g => ∫ r, g r ∂μ
      map_add' := fun g h => integral_add (BoundedContinuousFunction.integrable μ g)
        (BoundedContinuousFunction.integrable μ h)
      map_smul' := fun c g => integral_const_mul c (fun x => g x) }
  refine ⟨E,?_,fun g hg => integral_nonneg hg,fun _ => rfl⟩
  change (∫ _ : ℝ≥0, (1:ℝ) ∂μ) = 1
  exact mass

lemma inverse_value {f : ℝ → ℝ} (hc : ContinuousOn f (Set.Ici 0)) (h₀ : f 0=1)
    (hl : Tendsto f atTop (𝓝 0)) (u : ℝ) (hu : 0<u) (h1 : u≤1) :
    0 ≤ Function.invFunOn f (Set.Ici 0) u ∧ f (Function.invFunOn f (Set.Ici 0) u) = u := by
  obtain ⟨N,hN,hfN⟩ := ((eventually_ge_atTop (0:ℝ)).and (hl.eventually (Iio_mem_nhds hu))).exists
  have hx : u ∈ f '' Set.Icc 0 N :=
    intermediate_value_Icc' hN (hc.mono (fun _ h => h.1)) ⟨hfN.le, h₀ ▸ h1⟩
  obtain ⟨z,hz,he⟩ := hx
  have h : ∃ z ∈ Set.Ici (0:ℝ), f z = u := ⟨z,hz.1,he⟩
  exact ⟨Function.invFunOn_mem h,Function.invFunOn_eq h⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_195959.main := by
  intro repr atZero f hc h₀ hl hcm u hu v hv
  obtain ⟨μ,hμ,repPos⟩ := repr f hc h₀ hcm
  let _ := hμ
  have ft : Tendsto f (𝓝[>] (0:ℝ)) (𝓝 1) := by
    rw [← h₀]
    exact (hc 0 (Set.mem_Ici.mpr le_rfl)).mono (Set.Ioi_subset_Ici_self)
  have eqp : f =ᶠ[𝓝[>] (0:ℝ)] (fun t => ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ) :=
    Filter.mem_of_superset self_mem_nhdsWithin (fun t ht => repPos t ht)
  have mass := tendsto_nhds_unique (atZero μ hμ) (ft.congr' eqp)
  have rep (t : ℝ) (ht : 0 ≤ t) : f t = ∫ x : ℝ≥0, Real.exp (-(x:ℝ)*t) ∂μ := by
    rcases eq_or_lt_of_le ht with he|hp
    · subst t
      simpa only [mul_zero,Real.exp_zero,h₀] using mass.symm
    · exact repPos t hp
  obtain ⟨E,one,pos,eval⟩ := normalized_integral μ mass
  let K (t : ℝ) (ht : 0≤t) : ℝ≥0 →ᵇ ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x : ℝ≥0 => Real.exp (-(x:ℝ)*t)) (by fun_prop) 1 (fun x => by
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr x.2) ht)
  have bounds (t : ℝ) (ht : 0≤t) (x : ℝ≥0) : 0≤K t ht x ∧ K t ht x≤1 := by
    exact ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr x.2) ht)⟩
  have anti (t : ℝ) (ht : 0≤t) : Antitone (K t ht) := by
    intro x y hxy
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hxy) ht)
  have mean (t : ℝ) (ht : 0≤t) : E (K t ht) = f t := (eval _).trans (rep t ht).symm
  have both (t s : ℝ) (ht : 0≤t) (hs : 0 ≤ s) : E (K t ht*K s hs) = f (t+s) := by
    have eq : K t ht * K s hs = K (t+s) (add_nonneg ht hs) := by
      ext r
      change Real.exp (-(r:ℝ)*t)*Real.exp (-(r:ℝ)*s) = Real.exp (-(r:ℝ)*(t+s))
      rw [← Real.exp_add,mul_add]
    rw [eq]
    exact mean (t+s) (add_nonneg ht hs)
  let a := (u+v)/2
  have hu₀ := hu.1
  have hv₀ := hv.1
  have hu₁ := hu.2
  have hv₁ := hv.2
  change archC f u v-u*v ≤ archC f a a - a^2
  by_cases ha : a = 0
  · have u0 : u = 0 := by dsimp [a] at ha; linarith
    have v0 : v = 0 := by dsimp [a] at ha; linarith
    simp [ha,u0,v0,archC]
  let m := Function.invFunOn f (Set.Ici 0) a
  have ha₀ : 0<a := lt_of_le_of_ne (by dsimp [a]; linarith) (Ne.symm ha)
  have ha₁ : a≤1 := by dsimp [a]; linarith
  obtain ⟨hm,hmv⟩ := inverse_value hc h₀ hl a ha₀ ha₁
  have mmean : E (K m hm) = a := (mean m hm).trans hmv
  have md : archC f a a = E (K m hm * K m hm) := by
    simp only [archC, if_neg (not_or.mpr ⟨ha,ha⟩)]
    exact (both m m hm hm).symm
  rw [md]
  by_cases hzero : u=0 ∨ v=0
  · have hvar := positive_variance E one pos (K m hm)
    rw [mmean] at hvar
    have uvzero : u*v=0 := mul_eq_zero.mpr hzero
    simp only [archC,if_pos hzero,uvzero,sub_self]
    linarith
  have hn := not_or.mp hzero
  let t := Function.invFunOn f (Set.Ici 0) u
  let s := Function.invFunOn f (Set.Ici 0) v
  obtain ⟨ht,htu⟩ := inverse_value hc h₀ hl u (lt_of_le_of_ne hu₀ (Ne.symm hn.1)) hu₁
  obtain ⟨hs,hsv⟩ := inverse_value hc h₀ hl v (lt_of_le_of_ne hv₀ (Ne.symm hn.2)) hv₁
  have tmean : E (K t ht) = u := (mean t ht).trans htu
  have smean : E (K s hs) = v := (mean s hs).trans hsv
  have huv : archC f u v = E (K t ht*K s hs) := by
    rw [archC,if_neg hzero]; exact (both t s ht hs).symm
  have meanEq : E (K m hm) = (E (K t ht)+E (K s hs))/2 := by rw [mmean,tmean,smean]
  have cross := threshold (K m hm) (fun x => (K t ht x+K s hs x)/2) (anti m hm)
    (fun x y hxy => by linarith [anti t ht hxy,anti s hs hxy])
    (fun x => by
      obtain ⟨h₁,h₂⟩ := bounds m hm x
      obtain ⟨h₃,h₄⟩ := bounds t ht x
      obtain ⟨h₅,h₆⟩ := bounds s hs x
      constructor <;> linarith) (crossing t s m)
  have conclusion := compare E one pos (K t ht) (K s hs) (K m hm) meanEq cross
  rwa [← huv,tmean,smean,mmean] at conclusion

end OMA.R_mo_195959_R1
