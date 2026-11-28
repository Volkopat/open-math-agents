import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Ideal-class theta reciprocity in arbitrary signature. Periodize the Gaussian on the integer coordinate torus of each ideal basis. The real trace pairing identifies its frequencies with the trace-dual fractional ideal. Each complex place contributes two axes to the Gaussian integral and a factor of two to the trace. After normalization by the covolume, the product of the archimedean factors gives the reciprocal scale. Finally a logarithmic translation removes the choice of ideal representative before averaging. -/

namespace OMA.IdealThetaReciprocity

namespace DedekindDualIdeals

open NumberField
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev Frac := FractionalIdeal (𝓞 K)⁰ K

noncomputable def dual (J : (Frac K)ˣ) : (Frac K)ˣ :=
  Units.mk0 (FractionalIdeal.dual ℤ ℚ (J : Frac K)) (FractionalIdeal.dual_ne_zero ℤ ℚ J.ne_zero)

theorem dual_apply (J : (Frac K)ˣ) : dual K J = dual K 1 * J⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, dual, Units.val_mk0, Units.val_one]
  exact FractionalIdeal.dual_eq_mul_inv ℤ ℚ (J : Frac K)

noncomputable def classPerm : Equiv.Perm (ClassGroup (𝓞 K)) where
  toFun C := ClassGroup.mk K (dual K 1) * C⁻¹
  invFun C := ClassGroup.mk K (dual K 1) * C⁻¹
  left_inv C := by simp [mul_left_comm, mul_comm, mul_assoc]
  right_inv C := by simp [mul_left_comm, mul_comm, mul_assoc]

theorem class_dual (J : (Frac K)ˣ) : ClassGroup.mk K (dual K J) = classPerm K (ClassGroup.mk K J) := by
  rw [dual_apply, map_mul, map_inv]; rfl

theorem absNorm_dual (J : (Frac K)ˣ) :
    FractionalIdeal.absNorm (dual K J : Frac K) = (((discr K).natAbs : ℚ) * FractionalIdeal.absNorm (J : Frac K))⁻¹ := by
  have hD : FractionalIdeal.dual ℤ ℚ (1 : Frac K) = ((differentIdeal ℤ (𝓞 K) : Frac K))⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]
  change FractionalIdeal.absNorm (FractionalIdeal.dual ℤ ℚ (J : Frac K)) = _
  rw [FractionalIdeal.dual_eq_mul_inv, hD, map_mul, map_inv₀, map_inv₀, FractionalIdeal.coeIdeal_absNorm,
    absNorm_differentIdeal K (𝓞 K), mul_inv]

end DedekindDualIdeals

namespace DedekindIdealPlane
open NumberField NumberField.mixedEmbedding
open scoped NumberField nonZeroDivisors
variable (K : Type*) [Field K] [NumberField K]

noncomputable abbrev Lattice (J : (Ideal (𝓞 K))⁰) := idealLattice K (FractionalIdeal.mk0 K J)

end DedekindIdealPlane

namespace DedekindRealUnits

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem unit_lattice {J : (Ideal (𝓞 K))⁰} (u : (𝓞 K)ˣ) {x : mixedSpace K} (hx : x ∈ Lattice K J) :
    u • x ∈ Lattice K J := by
  obtain ⟨y, hy, rfl⟩ := (mem_idealLattice K _).mp hx
  apply (mem_idealLattice K _).mpr
  let I := ((FractionalIdeal.mk0 K J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
  refine ⟨(u : 𝓞 K) • y, (I : Submodule (𝓞 K) K).smul_mem (u : 𝓞 K) hy, ?_⟩
  change mixedEmbedding K ((u : K) * y) = _
  rw [unitSMul_smul, map_mul]

end DedekindRealUnits

namespace DedekindUnitVectors

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev Exponents := Fin (rank K) → ℤ

noncomputable def unit (k : Exponents K) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ k i

end DedekindUnitVectors

namespace DedekindUnitDomain

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace
open MeasureTheory Module DedekindUnitVectors Additive
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def domain : Set (logSpace K) := ZSpan.fundamentalDomain ((basisUnitLattice K).ofZLatticeBasis ℝ _)

theorem fundamental : IsAddFundamentalDomain (unitLattice K) (domain K) volume :=
  ZLattice.isAddFundamentalDomain (basisUnitLattice K) volume



noncomputable def latticeEquiv : Exponents K ≃ unitLattice K := (basisUnitLattice K).equivFun.toEquiv.symm

theorem log_unit (k : Exponents K) : logEmbedding K (ofMul (unit K k)) = (latticeEquiv K k : logSpace K) := by
  change logEmbedding K (ofMul (∏ i, fundSystem K i ^ k i)) = ↑((basisUnitLattice K).equivFun.symm k)
  simp only [ofMul_prod, ofMul_zpow, map_sum, map_zsmul, logEmbedding_fundSystem,
    Basis.equivFun_symm_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower]



noncomputable def fullCoordinate (y : logSpace K) (w : InfinitePlace K) : ℝ :=
  if h : w = w₀ then -∑ v, y v else y ⟨w, h⟩

theorem full_sum (y : logSpace K) : ∑ w, fullCoordinate K y w = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  have he (w : {w : InfinitePlace K // w ≠ w₀}) : fullCoordinate K y w.val = y w := by simp only [fullCoordinate, dif_neg w.prop]
  have hb : fullCoordinate K y w₀ = -∑ v, y v := dif_pos rfl
  rw [hb, Finset.sum_congr rfl (fun i _ => he i), neg_add_cancel]

theorem full_log_unit (u : (𝓞 K)ˣ) (w : InfinitePlace K) :
    fullCoordinate K (logEmbedding K (ofMul u)) w = (mult w : ℝ) * Real.log (w (u : K)) := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl, sum_logEmbedding_component, neg_mul, neg_neg]
  · simp [fullCoordinate, hw, logEmbedding_component]

end DedekindUnitDomain

namespace DedekindUnitGaussian

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitVectors MeasureTheory Additive
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def dilation (y : logSpace K) (w : InfinitePlace K) : ℝ := Real.exp (fullCoordinate K y w / mult w)

theorem add_coord (y z : logSpace K) (w : InfinitePlace K) : fullCoordinate K (y+z) w = fullCoordinate K y w + fullCoordinate K z w := by
  by_cases h : w = w₀ <;> simp [fullCoordinate, h, Finset.sum_add_distrib, add_comm]

theorem determinant (y : logSpace K) : ∏ w, (dilation K y w) ^ mult w = 1 := by
  have he (w : InfinitePlace K) : (dilation K y w) ^ mult w = Real.exp (fullCoordinate K y w) := by
    rw [dilation, ← Real.exp_nat_mul]; congr 1; field_simp [mult_coe_ne_zero]
  simp_rw [he, ← Real.exp_sum, full_sum, Real.exp_zero]

theorem dilation_unit (u : (𝓞 K)ˣ) (y : logSpace K) (w : InfinitePlace K) :
    dilation K (y + logEmbedding K (ofMul u)) w = dilation K y w * w (u : K) := by
  rw [dilation, add_coord, add_div, Real.exp_add, full_log_unit,
    mul_div_cancel_left₀ _ mult_coe_ne_zero, Real.exp_log (pos_at_place u w)]
  rfl

noncomputable def gaussian (t : ℝ) (a : mixedSpace K) (y : logSpace K) : ℂ :=
  Real.exp (-(Real.pi * t) * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2)

theorem gaussian_unit (u : (𝓞 K)ˣ) (a : mixedSpace K) (t : ℝ) (y : logSpace K) :
    gaussian K t (u • a) y = gaussian K t a (y + logEmbedding K (ofMul u)) := by
  simp only [gaussian, dilation_unit, unitSMul_smul, map_mul, normAtPlace_apply, mul_assoc]

end DedekindUnitGaussian

namespace DedekindRadialOrbit

open NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem NumberField.mixedEmbedding
open DedekindUnitDomain DedekindUnitGaussian MeasureTheory
open scoped NumberField Classical

variable (K : Type*) [Field K] [NumberField K]

theorem complete_zero_sum (b : InfinitePlace K → ℝ) (hb : ∑ w, b w = 0) (w : InfinitePlace K) :
    fullCoordinate K (fun v => b v.val) w = b w := by
  by_cases hw : w = w₀
  · subst w
    rw [fullCoordinate, dif_pos rfl]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hb
    linarith
  · simp only [fullCoordinate, dif_neg hw]

noncomputable def radius (a : mixedSpace K) : ℝ := Real.exp (Real.log (mixedEmbedding.norm a) / Module.finrank ℚ K)

theorem abs_decompose (a : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (w : InfinitePlace K) :
    normAtPlace w a = radius K a * dilation K (logMap a) w := by
  let n : ℝ := Module.finrank ℚ K
  let L := Real.log (mixedEmbedding.norm a)
  let b (v : InfinitePlace K) := (mult v : ℝ) * (Real.log (normAtPlace v a) - L / n)
  have hn : n ≠ 0 := by dsimp only [n]; exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hmul : ∑ v : InfinitePlace K, (mult v : ℝ) = n := by dsimp only [n]; exact_mod_cast (sum_mult_eq (K := K))
  have hlog : ∑ v : InfinitePlace K, (mult v : ℝ) * Real.log (normAtPlace v a) = L := by
    simp only [L, mixedEmbedding.norm_apply, Real.log_prod (fun i _ => pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp ha i)), Real.log_pow]
  have hb : ∑ v, b v = 0 := by
    simp only [b, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hlog, hmul]
    field_simp; ring
  have he : logMap a = fun v => b v.val := by ext v; simp only [logMap_apply, b, L, n, div_eq_mul_inv]
  rw [radius, dilation, he, complete_zero_sum K b hb, ← Real.exp_add]
  change normAtPlace w a = Real.exp (L/n + ((mult w : ℝ) * (Real.log (normAtPlace w a) - L/n)) / mult w)
  rw [mul_div_cancel_left₀ _ mult_coe_ne_zero, add_sub_cancel, Real.exp_log]
  exact lt_of_le_of_ne (normAtPlace_nonneg w a) (mixedEmbedding.norm_ne_zero_iff.mp ha w).symm

end DedekindRadialOrbit

namespace DedekindGeneralTheta

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding MeasureTheory
open DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def rep (C : ClassGroup (𝓞 K)) : (Ideal (𝓞 K))⁰ := (ClassGroup.mk0_surjective C⁻¹).choose

theorem rep_class (C : ClassGroup (𝓞 K)) : ClassGroup.mk0 (rep K C) = C⁻¹ := (ClassGroup.mk0_surjective C⁻¹).choose_spec

noncomputable def dualLabel : Equiv.Perm (ClassGroup (𝓞 K)) :=
  ((Equiv.inv _).trans (DedekindDualIdeals.classPerm K)).trans (Equiv.inv _)

noncomputable def q := (Real.sqrt ((discr K).natAbs : ℝ))⁻¹

noncomputable def avg (C : ClassGroup (𝓞 K)) (t : ℝ) : ℂ :=
  let J := rep K C
  let s := (q K * t / Ideal.absNorm (J : Ideal (𝓞 K))) ^ ((2 : ℝ) / Module.finrank ℚ K)
  ∫ y in DedekindUnitDomain.domain K, ∑' a : Lattice K J, DedekindUnitGaussian.gaussian K s a.val y



def Reciprocal : Prop := ∀ (C : ClassGroup (𝓞 K)) (t : ℝ), 0 < t →
  avg K C (1/t) = (t : ℂ) * avg K (dualLabel K C) t

end DedekindGeneralTheta

namespace DedekindClassPeriods

open MeasureTheory NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.InfinitePlace NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitGaussian
open DedekindUnitVectors DedekindRadialOrbit DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical Pointwise

variable (K : Type*) [Field K] [NumberField K]

theorem affine_average (f : logSpace K → ℂ) (hf : ∀ (v : unitLattice K) y, f (v.val + y) = f y)
    (b : logSpace K) : (∫ y in domain K, f (b - y)) = ∫ y in domain K, f y := by
  let : MeasurableVAdd (unitLattice K) (logSpace K) := (inferInstance : MeasurableVAdd (unitLattice K).toAddSubgroup (logSpace K))
  let : VAddInvariantMeasure (unitLattice K) (logSpace K) volume := (inferInstance : VAddInvariantMeasure (unitLattice K).toAddSubgroup (logSpace K) volume)
  let e : logSpace K ≃ logSpace K := { toFun := fun y => b-y, invFun := fun y => b-y,
                                        left_inv := sub_sub_cancel b, right_inv := sub_sub_cancel b }
  have hm := Measure.measurePreserving_sub_left (volume : Measure (logSpace K)) b
  have he : MeasurableEmbedding (fun y : logSpace K => b - y) :=
    (Homeomorph.subLeft b).measurableEmbedding
  have hD : IsAddFundamentalDomain (unitLattice K) (e '' domain K) volume :=
    (fundamental K).image_of_equiv e hm.quasiMeasurePreserving (Equiv.neg _) (by
      intro v y; change b - (-v.val + y) = v.val + (b-y); abel)
  exact (hm.setIntegral_image_emb he f (domain K)).symm.trans (hD.setIntegral_eq (fundamental K) hf)



theorem gaussian_mul (a b : mixedSpace K) (ha : mixedEmbedding.norm a ≠ 0) (s : ℝ) (y : logSpace K) :
    gaussian K s (a*b) y = gaussian K (s * radius K a ^ 2) b (y + logMap a) := by
  have hd (w : InfinitePlace K) : dilation K (y + logMap a) w = dilation K y w * dilation K (logMap a) w := by
    rw [dilation, add_coord, add_div, Real.exp_add]; rfl
  have hw (w : InfinitePlace K) : (mult w : ℝ) * (dilation K y w * normAtPlace w (a*b)) ^ 2 =
      radius K a ^ 2 * ((mult w : ℝ) * (dilation K (y+logMap a) w * normAtPlace w b) ^ 2) := by
    rw [map_mul, abs_decompose K a ha w, hd]; ring
  simp only [gaussian, hw, ← Finset.mul_sum]; congr 2; ring

theorem integral_unit_periodic (J : (Ideal (𝓞 K))⁰) (s : ℝ) (v : unitLattice K) (y : logSpace K) :
    (∑' a : Lattice K J, gaussian K s a.val (v.val + y)) = ∑' a : Lattice K J, gaussian K s a.val y := by
  let k := (latticeEquiv K).symm v
  let u := unit K k
  have hv : v.val = logEmbedding K (Additive.ofMul u) := by rw [log_unit]; exact congrArg Subtype.val ((latticeEquiv K).apply_symm_apply v).symm
  let e : Lattice K J ≃ Lattice K J := {
    toFun := fun a => ⟨u • a.val, DedekindRealUnits.unit_lattice K u a.prop⟩
    invFun := fun a => ⟨u⁻¹ • a.val, DedekindRealUnits.unit_lattice K u⁻¹ a.prop⟩
    left_inv := fun a => Subtype.ext (inv_smul_smul u a.val)
    right_inv := fun a => Subtype.ext (smul_inv_smul u a.val) }
  rw [hv, add_comm]
  simp_rw [← gaussian_unit]
  exact e.tsum_eq (fun a => gaussian K s a.val y)

end DedekindClassPeriods

namespace DedekindFractionalTheta

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindGeneralTheta DedekindDualIdeals DedekindClassPeriods
open DedekindUnitDomain DedekindUnitGaussian DedekindRadialOrbit
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

abbrev FIdeal := (Frac K)ˣ
abbrev Carrier (J : FIdeal K) := ↥((J.val : Frac K) : Submodule (𝓞 K) K)

noncomputable def embed (J : FIdeal K) : Carrier K J ≃ idealLattice K J :=
  Equiv.ofBijective (fun a => ⟨mixedEmbedding K a.val, (mem_idealLattice K J).mpr ⟨a.val,a.prop,rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mixedEmbedding_injective (K := K) (congrArg Subtype.val h)), by
      intro x; obtain ⟨y, hy, he⟩ := (mem_idealLattice K J).mp x.prop; exact ⟨⟨y,hy⟩,Subtype.ext he⟩⟩

noncomputable def normF (J : FIdeal K) : ℝ := FractionalIdeal.absNorm J.val

theorem normF_pos (J : FIdeal K) : 0 < normF K J := by
  dsimp only [normF]; exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J.val) (Ne.symm (FractionalIdeal.absNorm_eq_zero_iff.not.mpr J.ne_zero))

noncomputable def scale (J : FIdeal K) (t : ℝ) := (q K * t / normF K J) ^ ((2 : ℝ) / Module.finrank ℚ K)

noncomputable def theta (J : FIdeal K) (t : ℝ) (y : logSpace K) : ℂ :=
  ∑' a : Carrier K J, gaussian K (scale K J t) (mixedEmbedding K a.val) y

theorem theta_lattice (J : FIdeal K) (t : ℝ) (y : logSpace K) : theta K J t y =
    ∑' a : idealLattice K J, gaussian K (scale K J t) a.val y :=
  (embed K J).tsum_eq (fun a => gaussian K (scale K J t) a.val y)

theorem avg_eq (C : ClassGroup (𝓞 K)) (t : ℝ) : avg K C t =
    ∫ y in domain K, theta K (FractionalIdeal.mk0 K (rep K C)) t y := by
  simp only [avg, theta_lattice, scale, normF, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast]

theorem same_class {I J : FIdeal K} (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    ∃ u : Kˣ, J = toPrincipalIdeal (𝓞 K) K u * I := by
  have h₁ : ClassGroup.mk K (J / I) = 1 := by simp only [map_div, ← h, div_self']
  have hp := ClassGroup.mk_eq_one_iff.mp h₁
  obtain ⟨a,ha⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hp
  have he : ((J / I : FIdeal K) : Frac K) = FractionalIdeal.spanSingleton (𝓞 K)⁰ a := by
    apply Subtype.coe_injective; simp only [FractionalIdeal.val_eq_coe, ha, FractionalIdeal.coe_spanSingleton]
  have hn : a ≠ 0 := by intro hz; apply (J / I).ne_zero; simpa [hz] using he
  let u := Units.mk0 a hn
  have hI : toPrincipalIdeal (𝓞 K) K u = J / I := (toPrincipalIdeal_eq_iff).mpr he.symm
  exact ⟨u, by rw [hI, div_mul_cancel]⟩

variable (I : FIdeal K) (u : Kˣ)

theorem mem_principal_mul (z : K) :
    z ∈ (↑(toPrincipalIdeal (𝓞 K) K u * I) : Frac K) ↔ ∃ a ∈ I.val, z = (u : K) * a := by
  rw [Units.val_mul, coe_toPrincipalIdeal, FractionalIdeal.mem_singleton_mul]

noncomputable def principalEquiv : Carrier K I ≃ Carrier K (toPrincipalIdeal (𝓞 K) K u * I) :=
  Equiv.ofBijective (fun a => ⟨(u : K) * a.val,(mem_principal_mul K I u _).mpr ⟨a.val,a.prop,rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (mul_left_cancel₀ u.ne_zero (congrArg Subtype.val h)), by
      intro z; obtain ⟨a,ha,hz⟩ := (mem_principal_mul K I u _).mp z.prop; exact ⟨⟨a,ha⟩,Subtype.ext hz.symm⟩⟩

theorem normF_principal : normF K (toPrincipalIdeal (𝓞 K) K u * I) =
    mixedEmbedding.norm (mixedEmbedding K u.val) * normF K I := by
  simp only [normF, Units.val_mul, map_mul, coe_toPrincipalIdeal, FractionalIdeal.absNorm_span_singleton,
    norm_eq_norm, Rat.cast_mul, Rat.cast_abs]

theorem principal_theta (t : ℝ) (ht : 0 < t) (y : logSpace K) :
    theta K (toPrincipalIdeal (𝓞 K) K u * I) t y = theta K I t (y + logMap (mixedEmbedding K u.val)) := by
  let a := mixedEmbedding K u.val
  have hA : 0 < mixedEmbedding.norm a := lt_of_le_of_ne (mixedEmbedding.norm_nonneg a)
    (Ne.symm ((mixedEmbedding.norm_eq_zero_iff' ⟨u.val,rfl⟩).not.mpr (fun hz => u.ne_zero ((mixedEmbedding_injective (K := K)) (hz.trans (map_zero (mixedEmbedding K)).symm)))))
  have hq : 0 < q K := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))
  have ha : radius K a ^ 2 = mixedEmbedding.norm a ^ ((2 : ℝ) / Module.finrank ℚ K) := by
    rw [radius, pow_two, ← Real.exp_add, Real.rpow_def_of_pos hA]; congr 1; ring
  have hscale : scale K (toPrincipalIdeal (𝓞 K) K u * I) t * radius K a ^ 2 = scale K I t := by
    rw [scale, scale, normF_principal, ha, ← Real.mul_rpow (div_pos (mul_pos hq ht) (mul_pos hA (normF_pos K I))).le hA.le]
    congr 1; change q K * t / (mixedEmbedding.norm a * normF K I) * mixedEmbedding.norm a = q K * t / normF K I
    field_simp [hA.ne']
  unfold theta; rw [← (principalEquiv K I u).tsum_eq]; apply tsum_congr
  intro z
  change gaussian K _ (mixedEmbedding K ((u : K) * z.val)) y = _
  rw [map_mul, gaussian_mul K a _ hA.ne', hscale]

theorem theta_periodic_rep (C : ClassGroup (𝓞 K)) (t : ℝ) (v : unitLattice K) (y : logSpace K) :
    theta K (FractionalIdeal.mk0 K (rep K C)) t (v.val + y) = theta K (FractionalIdeal.mk0 K (rep K C)) t y := by
  simp only [theta_lattice]; exact integral_unit_periodic K (rep K C) _ v y

theorem label_class (C : ClassGroup (𝓞 K)) :
    ClassGroup.mk K (dual K (FractionalIdeal.mk0 K (rep K C))) =
      ClassGroup.mk K (FractionalIdeal.mk0 K (rep K (dualLabel K C))) := by
  rw [class_dual, ClassGroup.mk_mk0, ClassGroup.mk_mk0, rep_class, rep_class]
  simp [dualLabel]

theorem reciprocal_of_pointwise
    (hP : ∀ (C : ClassGroup (𝓞 K)) (t : ℝ), 0 < t → ∀ y : logSpace K,
      let I := FractionalIdeal.mk0 K (rep K C)
      theta K I (1/t) y = (t : ℂ) * theta K (dual K I) t (-y)) : Reciprocal K := by
  intro C t ht
  let I := FractionalIdeal.mk0 K (rep K C)
  let J := FractionalIdeal.mk0 K (rep K (dualLabel K C))
  obtain ⟨u,hu⟩ := same_class K (label_class K C).symm
  have he (y : logSpace K) : theta K (dual K I) t (-y) = theta K J t (logMap (mixedEmbedding K u.val) - y) := by
    rw [show dual K I = toPrincipalIdeal (𝓞 K) K u * J from hu, principal_theta K J u t ht, sub_eq_add_neg, add_comm]
  rw [avg_eq, avg_eq]; change (∫ y in domain K, theta K I (1/t) y) = (t : ℂ) * ∫ y in domain K, theta K J t y
  simp_rw [show ∀ y, theta K I (1/t) y = (t : ℂ) * theta K (dual K I) t (-y) from hP C t ht, he, integral_const_mul]
  exact congrArg ((t : ℂ) * ·) (affine_average K (theta K J t) (theta_periodic_rep K (dualLabel K C) t) _)

end DedekindFractionalTheta

namespace DedekindThetaScales

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindDualIdeals DedekindFractionalTheta DedekindGeneralTheta
open DedekindUnitGaussian
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

theorem q_pos : 0 < q K := inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero K)))

theorem q_sq : q K ^ 2 = ((discr K).natAbs : ℝ)⁻¹ := by
  dsimp [q]; rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem normF_dual (I : FIdeal K) : normF K (dual K I) = q K ^ 2 / normF K I := by
  rw [q_sq]; simp only [normF, absNorm_dual, Rat.cast_inv, Rat.cast_mul, Rat.cast_natCast, mul_inv, div_eq_mul_inv]

theorem scale_dual (I : FIdeal K) {t : ℝ} (ht : 0 < t) : scale K (dual K I) t = (scale K I (1/t))⁻¹ := by
  have hq := q_pos K; have hN := normF_pos K I
  rw [scale, scale, normF_dual, ← Real.inv_rpow (div_nonneg (mul_nonneg hq.le (one_div_pos.mpr ht).le) hN.le)]
  congr 1; field_simp

theorem scale_weight (I : FIdeal K) {t : ℝ} (ht : 0 < t) :
    (q K / normF K I) * (scale K I (1/t)) ^ (-(Module.finrank ℚ K : ℝ) / 2) = t := by
  have hq := q_pos K; have hN := normF_pos K I
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [scale, ← Real.rpow_mul (div_nonneg (mul_nonneg hq.le (one_div_pos.mpr ht).le) hN.le),
    show ((2 : ℝ) / Module.finrank ℚ K) * (-(Module.finrank ℚ K : ℝ)/2) = -1 by field_simp,
    Real.rpow_neg_one]; field_simp

theorem covolume_weight (I : FIdeal K) :
    (2 : ℝ) ^ nrComplexPlaces K * ZLattice.covolume (idealLattice K I) = normF K I / q K := by
  rw [mixedEmbedding.covolume_idealLattice]
  simp only [normF, q, div_inv_eq_mul, Nat.cast_natAbs, Int.cast_abs]
  rw [show (2 : ℝ)⁻¹ ^ nrComplexPlaces K = ((2 : ℝ) ^ nrComplexPlaces K)⁻¹ by rw [inv_pow]]
  field_simp

noncomputable def raw (I : FIdeal K) (s : ℝ) (y : logSpace K) : ℂ :=
  ∑' a : Carrier K I, gaussian K s (mixedEmbedding K a.val) y

def LatticePoisson : Prop := ∀ (I : FIdeal K) (s : ℝ), 0 < s → ∀ y : logSpace K,
    raw K I s y = (((q K / normF K I) * s ^ (-(Module.finrank ℚ K : ℝ) / 2) : ℝ) : ℂ) * raw K (dual K I) s⁻¹ (-y)

theorem reciprocal (h : LatticePoisson K) : Reciprocal K := by
  apply reciprocal_of_pointwise K; intro C t ht y
  let I := FractionalIdeal.mk0 K (rep K C)
  have hs : 0 < scale K I (1/t) := Real.rpow_pos_of_pos (div_pos (mul_pos (q_pos K) (one_div_pos.mpr ht)) (normF_pos K I)) _
  have he := h I _ hs y
  rw [scale_weight K I ht, ← scale_dual K I ht] at he
  exact he

end DedekindThetaScales

namespace DedekindTorusPoisson

open MeasureTheory Set UnitAddTorus Filter Topology
open scoped Classical

variable {d : Type*} [Fintype d]

noncomputable def grid (k : d → ℤ) : d → ℝ := fun i => k i

noncomputable def proj (x : d → ℝ) : UnitAddTorus d := fun i => x i

theorem proj_open : IsOpenQuotientMap (proj (d := d)) :=
  IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

theorem proj_grid (k : d → ℤ) : proj (grid k) = 0 := by
  funext i; change ((k i : ℝ) : UnitAddCircle) = 0
  exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨k i, by simp⟩

theorem proj_add (x y : d → ℝ) : proj (x+y) = proj x + proj y := rfl

theorem same_proj {x y : d → ℝ} (h : proj x = proj y) : ∃ k : d → ℤ, x = y + grid k := by
  have he (i : d) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    have hh : (((x i - y i : ℝ)) : UnitAddCircle) = 0 := by
      change ((x i : UnitAddCircle) - (y i : UnitAddCircle)) = 0; exact sub_eq_zero.mpr (congrFun h i)
    simpa using ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hh)
  choose k hk using he
  exact ⟨k, funext fun i => by change x i = y i + (k i : ℝ); rw [hk]; ring⟩

noncomputable def period (f : (d → ℝ) → ℂ) (x : d → ℝ) := ∑' k : d → ℤ, f (x + grid k)

theorem period_add (f : (d → ℝ) → ℂ) (x : d → ℝ) (k : d → ℤ) : period f (x + grid k) = period f x := by
  have he (n : d → ℤ) : x + grid k + grid n = x + grid (k+n) := by ext i; simp [grid,add_assoc]
  simp only [period, he]; exact (Equiv.addLeft k).tsum_eq (fun n => f (x + grid n))

def UniformBound (f : (d → ℝ) → ℂ) : Prop := ∀ S : Set (d → ℝ), IsCompact S →
    ∃ B : (d → ℤ) → ℝ, Summable B ∧ ∀ k, ∀ x ∈ S, ‖f (x + grid k)‖ ≤ B k

theorem continuous_period {f : (d → ℝ) → ℂ} (hf : Continuous f) (hB : UniformBound f) : Continuous (period f) := by
  apply continuous_iff_continuousAt.mpr; intro x
  obtain ⟨B,hS,h⟩ := hB _ (isCompact_closedBall x 1)
  have hc : ContinuousOn (period f) (Metric.closedBall x 1) :=
    continuousOn_tsum (fun k => (hf.comp (continuous_id.add continuous_const)).continuousOn) hS h
  exact (hc x (Metric.mem_closedBall_self zero_le_one)).continuousAt (Metric.closedBall_mem_nhds _ zero_lt_one)

theorem lift_period {f : (d → ℝ) → ℂ} (hf : Continuous f) (hB : UniformBound f) :
    ∃ F : C(UnitAddTorus d, ℂ), ∀ x, F (proj x) = period f x := by
  let p := proj (d := d)
  let g (z : UnitAddTorus d) := (proj_open.surjective z).choose
  let F (z : UnitAddTorus d) := period f (g z)
  have he (x : d → ℝ) : F (p x) = period f x := by
    obtain ⟨k,hk⟩ := same_proj ((proj_open.surjective (p x)).choose_spec)
    change period f (g (p x)) = _; rw [show g (p x) = x + grid k from hk, period_add]
  refine ⟨⟨F, proj_open.isQuotientMap.continuous_iff.mpr ?_⟩,he⟩
  change Continuous (F ∘ p); rw [show F ∘ p = period f from funext he]; exact continuous_period hf hB

noncomputable def cube (d : Type*) := {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1}

theorem cube_measurable : MeasurableSet (cube d) := MeasurableSet.univ_pi' fun _ => measurableSet_Ioc

theorem cube_subset : cube d ⊆ Icc (0 : d → ℝ) 1 := fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

theorem grid_integral (G : (d → ℝ) → ℂ) (hG : Integrable G) :
    (∫ x, G x) = ∑' k : d → ℤ, ∫ x in cube d, G (x + grid k) := by
  letI : AddAction (d → ℤ) (d → ℝ) := {
    vadd := fun k x => grid k + x
    zero_vadd := fun x => by funext i; change ((0 : ℤ) : ℝ) + x i = x i; simp
    add_vadd := fun k l x => by funext i; change ((k i + l i : ℤ) : ℝ) + x i = (k i : ℝ) + ((l i : ℝ) + x i); simp [add_assoc] }
  letI : MeasurableConstVAdd (d → ℤ) (d → ℝ) := ⟨fun k => measurable_const_add _⟩
  letI : VAddInvariantMeasure (d → ℤ) (d → ℝ) volume :=
    ⟨fun k _ h => (measurePreserving_add_left volume (grid k)).measure_preimage h.nullMeasurableSet⟩
  have hD : IsAddFundamentalDomain (d → ℤ) (cube d) volume := by
    apply IsAddFundamentalDomain.mk' cube_measurable.nullMeasurableSet
    intro x
    have hi (i : d) : ∃! n : ℤ, (n : ℝ) + x i ∈ Ioc 0 1 := by
      simpa only [zero_add, zsmul_eq_mul, mul_one, add_comm (x i)] using existsUnique_add_zsmul_mem_Ioc (zero_lt_one : 0 < (1 : ℝ)) (x i) 0
    choose n hn hu using hi
    exact ⟨n,hn,fun k hk => funext fun i => hu i (k i) (hk i)⟩
  rw [hD.integral_eq_tsum'' G hG]; apply tsum_congr; intro k
  change (∫ x in cube d, G (grid k + x)) = _
  simp_rw [add_comm (grid k)]

noncomputable def character (n : d → ℤ) (x : d → ℝ) : ℂ := mFourier (-n) (proj x)

theorem char_norm (n : d → ℤ) (x : d → ℝ) : ‖character n x‖ = 1 := by
  simp [character,mFourier,fourier_apply,norm_prod,Circle.norm_coe]

theorem coefficient {f : (d → ℝ) → ℂ} (hf : Continuous f) (hi : Integrable f) (hb : UniformBound f)
    (F : C(UnitAddTorus d, ℂ)) (hF : ∀ x, F (proj x) = period f x) (n : d → ℤ) :
    mFourierCoeff F n = ∫ x, character n x * f x := by
  let e := character n
  let G (x : d → ℝ) := e x * f x
  have he : Continuous e := (mFourier (-n)).continuous.comp proj_open.continuous
  have hG : Integrable G := hi.norm.mono' (he.mul hf).aestronglyMeasurable (.of_forall fun x => by
    simp only [G,e,norm_mul,char_norm,one_mul,le_rfl])
  have hper (x : d → ℝ) (k : d → ℤ) : e (x+grid k) = e x := by simp [e,character,proj_add,proj_grid]
  obtain ⟨B,hB,h⟩ := hb _ (isCompact_Icc (a := (0 : d → ℝ)) (b := 1))
  have hbound (k : d → ℤ) (x : d → ℝ) (hx : x ∈ cube d) : ‖G (x + grid k)‖ ≤ B k := by
    simp only [G,e,norm_mul,char_norm,one_mul]; exact h k x (cube_subset hx)
  have hs : HasSum (fun k : d → ℤ => ∫ x in cube d, G (x+grid k)) (∫ x in cube d, ∑' k, G (x+grid k)) := by
    apply hasSum_integral_of_dominated_convergence (fun k _ => B k)
    · intro k; exact ((he.mul hf).comp (continuous_id.add continuous_const)).aestronglyMeasurable
    · intro k; filter_upwards [ae_restrict_mem cube_measurable] with x hx using hbound k x hx
    · exact .of_forall fun _ => hB
    · exact integrableOn_const ((measure_mono cube_subset).trans_lt isCompact_Icc.measure_lt_top).ne
    · filter_upwards [ae_restrict_mem cube_measurable] with x hx
      exact (hB.of_norm_bounded (fun k => hbound k x hx)).hasSum
  rw [mFourierCoeff_eq_integral F n 0, grid_integral G hG, hs.tsum_eq]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul]
  change (∫ x in cube d, e x * F (proj x)) = _
  simp only [G,hper,← tsum_mul_left,hF,period]

theorem poisson {f : (d → ℝ) → ℂ} (hf : Continuous f) (hi : Integrable f) (hb : UniformBound f)
    (hD : Summable fun n : d → ℤ => ∫ x, character n x * f x) :
    (∑' k : d → ℤ, f (grid k)) = ∑' n : d → ℤ, ∫ x, character n x * f x := by
  obtain ⟨F,hF⟩ := lift_period hf hb
  have hcoeff := coefficient hf hi hb F hF
  have hS : Summable (mFourierCoeff F) := hD.congr fun n => (hcoeff n).symm
  have h0 (n : d → ℤ) : mFourier n (proj (0 : d → ℝ)) = 1 := by simp [mFourier,proj]
  have hsum := (hasSum_mFourier_series_apply_of_summable hS (proj 0)).tsum_eq.symm
  simpa only [h0,smul_eq_mul,mul_one,hF,period,zero_add,hcoeff] using hsum

end DedekindTorusPoisson

namespace DedekindTraceCoordinates

open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open DedekindDualIdeals DedekindFractionalTheta
open scoped NumberField nonZeroDivisors Classical

variable (K : Type*) [Field K] [NumberField K]

noncomputable def archTrace (z : mixedSpace K) : ℝ := (∑ w, z.1 w) + ∑ w, 2 * (z.2 w).re

theorem archTrace_embedding (a : K) : archTrace K (mixedEmbedding K a) = (Algebra.trace ℚ K a : ℝ) := by
  let e := (indexEquiv K).trans (RingHom.equivRatAlgHom K ℂ)
  have hh := trace_eq_sum_embeddings (K := ℚ) (L := K) ℂ (x := a)
  rw [← e.sum_comp (fun σ : K →ₐ[ℚ] ℂ => σ a)] at hh
  have h := congrArg Complex.re hh
  simp only [eq_ratCast, Complex.ratCast_re, Complex.re_sum, Fintype.sum_sum_type,
    Finset.univ_product_univ.symm, Finset.sum_product, Fin.sum_univ_two, e, Equiv.trans_apply,
    RingHom.equivRatAlgHom_apply, RingHom.toRatAlgHom_apply, indexEquiv_apply_isReal,
    indexEquiv_apply_isComplex_fst, indexEquiv_apply_isComplex_snd, ComplexEmbedding.conjugate_coe_eq,
    Complex.conj_re, ← two_mul, Complex.add_re] at h
  have hr (w : {w : InfinitePlace K // IsReal w}) : (w.val.embedding a).re = embedding_of_isReal w.prop a := by
    rw [← embedding_of_isReal_apply w.prop a, Complex.ofReal_re]
  simpa only [archTrace,mixedEmbedding_apply_isReal,mixedEmbedding_apply_isComplex,
    hr] using h.symm

noncomputable def tracePair (x z : mixedSpace K) : ℝ := archTrace K (x * z)

theorem tracePair_embed (x z : K) : tracePair K (mixedEmbedding K x) (mixedEmbedding K z) =
    (Algebra.trace ℚ K (x*z) : ℝ) := by rw [tracePair, ← map_mul, archTrace_embedding]

theorem tracePair_sum {ι : Type*} [Fintype ι] (b : ι → mixedSpace K) (x : ι → ℝ) (z : mixedSpace K) :
    tracePair K (∑ i, x i • b i) z = ∑ i, x i * tracePair K (b i) z := by
  let A : mixedSpace K →ₗ[ℝ] ℝ := {
    toFun := archTrace K
    map_add' := fun u v => by simp only [archTrace,Prod.fst_add,Prod.snd_add,Pi.add_apply,Complex.add_re,mul_add,Finset.sum_add_distrib]; ring
    map_smul' := fun c u => by simp only [archTrace,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,smul_eq_mul,Complex.smul_re, RingHom.id_apply, mul_add,Finset.mul_sum]; ring_nf }
  change A ((∑ i, x i • b i) * z) = ∑ i, x i * A (b i * z)
  simp only [Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul]

variable (I : FIdeal K)

abbrev Idx := Free.ChooseBasisIndex ℤ I

theorem dual_span : Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I).traceDual) =
    (((dual K I).val : Submodule (𝓞 K) K).restrictScalars ℤ) := by
  have h : (I.val : Submodule (𝓞 K) K).restrictScalars ℤ = Submodule.span ℤ (Set.range (basisOfFractionalIdeal K I)) := by
    ext x; exact (mem_span_basisOfFractionalIdeal K).symm
  change _ = ((FractionalIdeal.dual ℤ ℚ I.val : Submodule (𝓞 K) K).restrictScalars ℤ)
  rw [FractionalIdeal.coe_dual ℤ ℚ I.ne_zero]
  exact (Submodule.traceDual_span_of_basis ℤ (I.val : Submodule (𝓞 K) K) (basisOfFractionalIdeal K I) h).symm

noncomputable def frequency : (Idx K I → ℤ) ≃ Carrier K (dual K I) :=
  (((basisOfFractionalIdeal K I).traceDual.restrictScalars ℤ).equivFun.toEquiv.symm).trans
    (Equiv.subtypeEquivRight fun x => SetLike.ext_iff.mp (dual_span K I) x)

theorem frequency_coord (n : Idx K I → ℤ) (i : Idx K I) :
    Algebra.trace ℚ K ((frequency K I n).val * basisOfFractionalIdeal K I i) = (n i : ℚ) := by
  let b := (basisOfFractionalIdeal K I).traceDual
  let z := (b.restrictScalars ℤ).equivFun.symm n
  have h := b.restrictScalars_repr_apply ℤ z i
  have hz : (b.restrictScalars ℤ).repr z i = n i := congrFun ((b.restrictScalars ℤ).equivFun.apply_symm_apply n) i
  rw [hz] at h
  change Algebra.trace ℚ K (z.val * basisOfFractionalIdeal K I i) = _
  simpa [b,Basis.traceDual_repr_apply,Algebra.traceForm_apply] using h.symm

theorem frequency_pair (n : Idx K I → ℤ) (x : Idx K I → ℝ) :
    tracePair K ((fractionalIdealLatticeBasis K I).equivFun.symm x) (mixedEmbedding K (frequency K I n).val) =
      ∑ i, x i * (n i : ℝ) := by
  rw [Basis.equivFun_symm_apply,tracePair_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [fractionalIdealLatticeBasis_apply, tracePair_embed, mul_comm (basisOfFractionalIdeal K I i), frequency_coord, Rat.cast_intCast]

end DedekindTraceCoordinates

namespace DedekindDiagonalTransform

open MeasureTheory Complex
open scoped Classical

variable {d : Type*} [Fintype d]

noncomputable def phase (t : ℝ) : ℂ := Complex.exp (-(2 * Real.pi * I) * t)

theorem character_eq (n : d → ℤ) (x : d → ℝ) : DedekindTorusPoisson.character n x =
    phase (∑ i, x i * (n i : ℝ)) := by
  simp only [DedekindTorusPoisson.character,UnitAddTorus.mFourier,ContinuousMap.coe_mk,
    DedekindTorusPoisson.proj,Pi.neg_apply,fourier_coe_apply,Int.cast_neg,ofReal_one,div_one,
    phase,ofReal_sum,Finset.mul_sum,ofReal_mul,ofReal_intCast,Complex.exp_sum]
  apply Finset.prod_congr rfl; intro i _; congr 1; ring

noncomputable def wave (a f x : d → ℝ) : ℂ :=
  phase (∑ i, x i * f i) * (Real.exp (-Real.pi * ∑ i, a i * (x i)^2) : ℂ)

theorem wave_eq (a f x : d → ℝ) : wave a f x = Complex.exp
    (-(∑ i, (Real.pi * a i : ℝ) * (x i : ℂ)^2) + ∑ i, (-(2 * Real.pi * I) * f i) * x i) := by
  simp only [wave,phase,Complex.ofReal_exp,← Complex.exp_add,ofReal_neg,ofReal_sum,ofReal_mul,ofReal_pow,
    Finset.mul_sum,neg_mul,Finset.sum_neg_distrib]
  congr 1
  rw [add_comm]; congr 1 <;> try apply congrArg Neg.neg <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem integrable_wave (a f : d → ℝ) (ha : ∀ i, 0 < a i) : Integrable (wave a f) := by
  simp_rw [funext (wave_eq a f)]
  exact GaussianFourier.integrable_cexp_neg_sum_mul_add (fun i => (show 0 < (↑(Real.pi * a i) : ℂ).re from mul_pos Real.pi_pos (ha i))) _

theorem integral_wave (a f : d → ℝ) (ha : ∀ i, 0 < a i) :
    (∫ x, wave a f x) = ((∏ i, (a i) ^ (-(1/2) : ℝ)) : ℝ) *
      (Real.exp (-Real.pi * ∑ i, (f i)^2 / a i) : ℂ) := by
  simp_rw [wave_eq]
  rw [GaussianFourier.integral_cexp_neg_sum_mul_add (fun i => (show 0 < (↑(Real.pi * a i) : ℂ).re from mul_pos Real.pi_pos (ha i))), Finset.prod_mul_distrib]
  congr 1
  · rw [ofReal_prod]; apply Finset.prod_congr rfl; intro i _
    rw [show ((Real.pi : ℂ) / ↑(Real.pi * a i)) = ((a i)⁻¹ : ℝ) by push_cast; field_simp [Real.pi_ne_zero],
      show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (inv_nonneg.mpr (ha i).le), Real.inv_rpow (ha i).le, Real.rpow_neg (ha i).le]
  · rw [← Complex.exp_sum, ofReal_exp]; congr 1
    simp only [ofReal_mul,ofReal_neg,ofReal_sum,ofReal_div,ofReal_pow,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hai : (a i : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ha i).ne'
    field_simp; ring_nf; simp [I_sq]

end DedekindDiagonalTransform

namespace DedekindBasisMeasure

open MeasureTheory MeasureTheory.Measure Module ZSpan
open NumberField NumberField.mixedEmbedding DedekindFractionalTheta
open scoped Classical NumberField nonZeroDivisors

variable {d E : Type*} [Fintype d] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem coords_map (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] :
    μ.map b.equivFunL = μ (fundamentalDomain b) • (volume : Measure (d → ℝ)) := by
  have he : b.map b.equivFunL.toLinearEquiv = Pi.basisFun ℝ d := by
    ext i : 1; funext j
    simp [Pi.basisFun_apply,Basis.repr_self,Pi.single_apply,Finsupp.single_apply,eq_comm]
  have hm := addHaarMeasure_unique μ b.parallelepiped
  have hb : μ = μ (fundamentalDomain b) • b.addHaar := by
    rw [measure_congr (fundamentalDomain_ae_parallelepiped b μ)]
    simpa only [Basis.coe_parallelepiped,Basis.addHaar_def] using hm
  conv_lhs => rw [hb,Measure.map_smul,b.map_addHaar,he,Basis.addHaar_def,Basis.parallelepiped_basisFun,addHaarMeasure_eq_volume_pi]

theorem integrate (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] (f : E → ℂ) :
    (∫ x, f x ∂μ) = μ.real (fundamentalDomain b) • ∫ u, f (b.equivFun.symm u) := by
  let e := b.equivFunL.toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.integral_map (μ := μ) (fun u => f (b.equivFun.symm u))
  change (∫ u, f (b.equivFun.symm u) ∂μ.map b.equivFunL) = ∫ x, f (b.equivFun.symm (b.equivFun x)) ∂μ at h
  simpa only [LinearEquiv.symm_apply_apply,coords_map,integral_smul_measure,measureReal_def] using h.symm

theorem integrable_iff (b : Basis d ℝ E) (μ : Measure E) [IsAddHaarMeasure μ] (f : E → ℂ) :
    Integrable f μ ↔ Integrable (fun u => f (b.equivFun.symm u)) := by
  let e := b.equivFunL.toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.integrable_map_iff (μ := μ) (g := fun u => f (b.equivFun.symm u))
  change Integrable _ (μ.map b.equivFunL) ↔ Integrable (fun x => f (b.equivFun.symm (b.equivFun x))) μ at h
  rw [coords_map,integrable_smul_measure (measure_fundamentalDomain_ne_zero (μ := μ) b) (fundamentalDomain_isBounded b).measure_lt_top.ne] at h
  simpa using h.symm

end DedekindBasisMeasure

namespace DedekindLatticeGaussian

open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open NumberField.mixedEmbedding DedekindUnitDomain DedekindUnitGaussian DedekindIdealPlane
open scoped NumberField nonZeroDivisors Classical

theorem summable_gaussian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {b : ℝ} (hb : 0 < b) : Summable (fun x : L => Real.exp (-b * ‖x‖ ^ 2)) := by
  let m := Module.finrank ℤ L + 1
  let r : ℝ := -((2 * m : ℕ) : ℝ)
  have hr : r < -(Module.finrank ℤ L : ℝ) := by dsimp [r, m]; push_cast; linarith
  apply Summable.of_norm_bounded_eventually ((ZLattice.summable_norm_rpow L r hr).mul_left ((m.factorial : ℝ) / b ^ m))
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with x hx
  have hX : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hF : 0 < (m.factorial : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (b * ‖x‖ ^ 2) (mul_nonneg hb.le (sq_nonneg ‖x‖)) m
  have hrx : ‖x‖ ^ r = (‖x‖ ^ (2 * m))⁻¹ := by dsimp only [r]; rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, hrx, neg_mul, Real.exp_neg]
  rw [mul_pow, ← pow_mul] at h
  calc (Real.exp (b * ‖x‖ ^ 2))⁻¹ ≤ (b ^ m * ‖x‖ ^ (2 * m) / (m.factorial : ℝ))⁻¹ := by
         simpa only [one_div] using one_div_le_one_div_of_le (div_pos (mul_pos (pow_pos hb _) (pow_pos hX _)) hF) h
       _ = (m.factorial : ℝ) / b ^ m * (‖x‖ ^ (2 * m))⁻¹ := by rw [inv_div, ← div_eq_mul_inv, div_div]

variable (K : Type*) [Field K] [NumberField K]



theorem quadratic_lower {c : ℝ} (hc : 0 < c) (y : logSpace K) (hy : ∀ w, c ≤ dilation K y w)
    (a : mixedSpace K) : c ^ 2 * ‖a‖ ^ 2 ≤
      ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w a) ^ 2 := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun w : InfinitePlace K => normAtPlace w a)
  rw [norm_eq_sup'_normAtPlace, hw, ← mul_pow]
  have h := mul_le_mul_of_nonneg_right (hy w) (normAtPlace_nonneg w a)
  calc _ ≤ (dilation K y w * normAtPlace w a) ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le (normAtPlace_nonneg w a)) h 2
       _ ≤ (mult w : ℝ) * _ := le_mul_of_one_le_left (sq_nonneg _) one_le_mult
       _ ≤ _ := Finset.single_le_sum (fun v _ => mul_nonneg (Nat.cast_nonneg (mult v)) (sq_nonneg (dilation K y v * normAtPlace v a))) (Finset.mem_univ w)

end DedekindLatticeGaussian

namespace DedekindGaussianConvergence

open MeasureTheory Module NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem DedekindFractionalTheta DedekindTraceCoordinates
open DedekindLatticeGaussian DedekindUnitGaussian DedekindTorusPoisson
open scoped Classical NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def point (I : FIdeal K) : (Idx K I → ℤ) ≃ idealLattice K I :=
  (((fractionalIdealLatticeBasis K I).restrictScalars ℤ).equivFun.toEquiv.symm).trans
    (Equiv.subtypeEquivRight fun x => SetLike.ext_iff.mp (span_idealLatticeBasis K I) x)

theorem point_eq (I : FIdeal K) (k : Idx K I → ℤ) : (point K I k).val =
    (fractionalIdealLatticeBasis K I).equivFun.symm (grid k) := by
  let b := fractionalIdealLatticeBasis K I
  let v := (b.restrictScalars ℤ).equivFun.symm k
  apply b.equivFun.injective; rw [LinearEquiv.apply_symm_apply]; funext i
  have h := b.restrictScalars_repr_apply ℤ v i
  have hv : (b.restrictScalars ℤ).repr v i = k i := congrFun ((b.restrictScalars ℤ).equivFun.apply_symm_apply k) i
  rw [hv] at h
  change b.repr v.val i = (k i : ℝ)
  simpa using h.symm

theorem bound {s : ℝ} (hs : 0 < s) (y : logSpace K) : ∃ b : ℝ, 0 < b ∧ ∀ z : mixedSpace K,
    ‖gaussian K s z y‖ ≤ Real.exp (-b * ‖z‖^2) := by
  obtain ⟨w,_,hw⟩ := Finset.univ.exists_min_image (dilation K y) Finset.univ_nonempty
  let c := dilation K y w
  have hc : 0 < c := Real.exp_pos _
  refine ⟨Real.pi * s * c^2,mul_pos (mul_pos Real.pi_pos hs) (sq_pos_of_pos hc),fun z => ?_⟩
  simp only [gaussian,Complex.norm_of_nonneg (Real.exp_pos _).le,Real.exp_le_exp]
  have h := mul_le_mul_of_nonpos_left (quadratic_lower K hc y (fun v => hw v (Finset.mem_univ _)) z) (neg_nonpos.mpr (mul_pos Real.pi_pos hs).le)
  linarith only [h]

theorem abs_sum (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) :
    Summable fun z : Carrier K I => gaussian K s (mixedEmbedding K z.val) y := by
  obtain ⟨b,hb,h⟩ := bound K hs y
  exact (embed K I).summable_iff.mpr ((summable_gaussian (idealLattice K I) hb).of_norm_bounded (fun z => h z.val))

noncomputable def sample (I : FIdeal K) (s : ℝ) (y : logSpace K) (x : Idx K I → ℝ) :=
  gaussian K s ((fractionalIdealLatticeBasis K I).equivFun.symm x) y

theorem continuous_sample (I : FIdeal K) (s : ℝ) (y : logSpace K) : Continuous (sample K I s y) := by
  have h (w : InfinitePlace K) := (continuous_normAtPlace w).comp (fractionalIdealLatticeBasis K I).equivFunL.symm.continuous
  unfold sample gaussian
  exact Complex.continuous_ofReal.comp (Continuous.rexp (continuous_const.mul (continuous_finsetSum _ (fun w _ => continuous_const.mul ((continuous_const.mul (h w)).pow 2)))))

theorem uniform (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) : UniformBound (sample K I s y) := by
  intro S hS
  let e := (fractionalIdealLatticeBasis K I).equivFunL.symm
  obtain ⟨R,hR,hSR⟩ := (hS.image e.continuous).isBounded.exists_pos_norm_le
  obtain ⟨b,hb,h⟩ := bound K hs y
  let B (z : idealLattice K I) := Real.exp (b * R^2) * Real.exp (-(b/2) * ‖z‖^2)
  refine ⟨fun k => B (point K I k),(point K I).summable_iff.mpr ((summable_gaussian _ (half_pos hb)).mul_left _),?_⟩
  intro k x hx
  let z := (point K I k).val
  have hz : e (grid k) = z := (point_eq K I k).symm
  have hR' : ‖e x‖ ≤ R := hSR _ ⟨_,hx,rfl⟩
  have ht : ‖z‖ ≤ R + ‖e x + z‖ := by
    have := norm_sub_le (e x + z) (e x)
    rw [add_sub_cancel_left] at this; linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg z) ht 2
  have hh : ‖z‖^2 / 2 - R^2 ≤ ‖e x + z‖^2 := by nlinarith [sq_nonneg (R-‖e x+z‖)]
  change ‖gaussian K s (e (x+grid k)) y‖ ≤ Real.exp (b*R^2) * Real.exp (-(b/2)*‖z‖^2)
  rw [map_add,hz,← Real.exp_add]; apply (h _).trans; apply Real.exp_le_exp.mpr
  linarith only [mul_le_mul_of_nonneg_left hh hb.le]

end DedekindGaussianConvergence

namespace DedekindMixedAxes

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open DedekindTraceCoordinates DedekindUnitGaussian DedekindUnitDomain
open scoped Classical NumberField

variable (K : Type*) [Field K] [NumberField K]

def place : index K → InfinitePlace K := Sum.elim Subtype.val (fun p => p.1.val)

def sign : index K → ℝ := Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 1 else -1)

noncomputable def coord (z : mixedSpace K) := (stdBasis K).equivFun z

noncomputable def a (s : ℝ) (y : logSpace K) (i : index K) : ℝ :=
  s * (mult (place K i) : ℝ) * dilation K y (place K i) ^ 2

noncomputable def f (z : mixedSpace K) (i : index K) : ℝ :=
  mult (place K i) * sign K i * coord K z i

theorem a_pos {s : ℝ} (hs : 0 < s) (y : logSpace K) (i : index K) : 0 < a K s y i :=
  mul_pos (mul_pos hs (Nat.cast_pos.mpr mult_pos)) (sq_pos_of_pos (Real.exp_pos _))

theorem neg_dilation (y : logSpace K) (w : InfinitePlace K) : dilation K (-y) w = (dilation K y w)⁻¹ := by
  have h : fullCoordinate K (-y) w = -fullCoordinate K y w := by
    by_cases hw : w = w₀ <;> simp [fullCoordinate,hw,Finset.sum_neg_distrib]
  rw [dilation,dilation,h,neg_div,Real.exp_neg]

theorem quadratic (s : ℝ) (y : logSpace K) (z : mixedSpace K) :
    ∑ i, a K s y i * (coord K z i)^2 = s * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K y w * normAtPlace w z)^2 := by
  rw [sum_eq_sum_add_sum (fun w : InfinitePlace K => (mult w : ℝ) * _),mul_add]
  simp only [Fintype.sum_sum_type,← Finset.univ_product_univ,Finset.sum_product,Fin.sum_univ_two,
    a,place,Sum.elim_inl,Sum.elim_inr,coord,Module.Basis.equivFun_apply,stdBasis_apply_isReal,
    stdBasis_apply_isComplex_fst,stdBasis_apply_isComplex_snd,mult_isReal,mult_isComplex,
    Finset.mul_sum,Nat.cast_one,Nat.cast_ofNat]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _
  · rw [normAtPlace_apply_of_isReal w.prop]; simp [Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc]
  · rw [normAtPlace_apply_of_isComplex w.prop]; simp [mul_pow,Complex.sq_norm,Complex.normSq_apply]; ring

theorem pairing (u z : mixedSpace K) : ∑ i, coord K u i * f K z i = tracePair K u z := by
  simp only [f,sign,place,coord,Module.Basis.equivFun_apply,Fintype.sum_sum_type,← Finset.univ_product_univ,
    Finset.sum_product,Fin.sum_univ_two,Sum.elim_inl,Sum.elim_inr,stdBasis_apply_isReal,
    stdBasis_apply_isComplex_fst,stdBasis_apply_isComplex_snd,mult_isReal,mult_isComplex,
    tracePair,archTrace,Prod.fst_mul,Prod.snd_mul,Pi.mul_apply,Complex.mul_re]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro w _ <;> norm_num <;> ring

theorem sign_sq (i : index K) : sign K i ^ 2 = 1 := by
  rcases i with w | ⟨w,j⟩ <;> simp [sign]

theorem inverse_quad {s : ℝ} (hs : 0 < s) (y : logSpace K) (z : mixedSpace K) :
    ∑ i, (f K z i)^2 / a K s y i = s⁻¹ * ∑ w : InfinitePlace K, (mult w : ℝ) * (dilation K (-y) w * normAtPlace w z)^2 := by
  rw [← quadratic]; apply Finset.sum_congr rfl; intro i _
  simp only [a,f,neg_dilation,mul_pow,sign_sq,mul_one,inv_pow]
  have hd : dilation K y (place K i) ≠ 0 := (Real.exp_pos _).ne'
  field_simp [hs.ne',mult_coe_ne_zero,hd]

theorem index_prod (g : InfinitePlace K → ℝ) : (∏ i : index K, g (place K i)) = ∏ w, (g w) ^ mult w := by
  rw [prod_eq_prod_mul_prod (fun w : InfinitePlace K => (g w)^mult w)]
  simp [Fintype.prod_sum_type,← Finset.univ_product_univ,Finset.prod_product,Fin.prod_univ_two,place,mult_isReal,mult_isComplex,pow_two]

theorem amplitude {s : ℝ} (hs : 0 < s) (y : logSpace K) :
    (∏ i, (a K s y i)^(-(1/2):ℝ)) = ((2:ℝ)^nrComplexPlaces K)⁻¹ * s^(-(Module.finrank ℚ K : ℝ)/2) := by
  let p : ℝ := -(1/2)
  have hD (w : InfinitePlace K) : (dilation K y w ^ 2) ^ p = (dilation K y w)⁻¹ := by
    have hd : 0 ≤ dilation K y w := (Real.exp_pos _).le
    rw [← Real.rpow_natCast_mul hd]; norm_num [p,Real.rpow_neg_one]
  have hM : (∏ i : index K, (mult (place K i) : ℝ)^p) = ((2:ℝ)^nrComplexPlaces K)⁻¹ := by
    rw [index_prod K (fun w => (mult w : ℝ)^p),prod_eq_prod_mul_prod]
    simp only [mult_isReal,mult_isComplex,Nat.cast_one,Real.one_rpow,one_pow,Finset.prod_const_one,one_mul,
      Nat.cast_ofNat,← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
    norm_num [p, nrComplexPlaces, inv_pow]
  have hV : (∏ i : index K, (dilation K y (place K i))⁻¹) = 1 := by
    rw [Finset.prod_inv_distrib,index_prod,determinant,inv_one]
  simp only [a,Real.mul_rpow (mul_nonneg hs.le (Nat.cast_nonneg _)) (sq_nonneg _),Real.mul_rpow hs.le (Nat.cast_nonneg _),Finset.prod_mul_distrib]
  change _ * (∏ i, (mult (place K i) : ℝ)^p) * (∏ i, (dilation K y (place K i)^2)^p) = _
  simp only [hD,hV,hM,mul_one,Finset.prod_const,Finset.card_univ,← Real.rpow_mul_natCast hs.le]
  rw [← Module.finrank_eq_card_basis (stdBasis K),mixedEmbedding.finrank]
  ring_nf

end DedekindMixedAxes

namespace DedekindIdealPoisson

open MeasureTheory NumberField NumberField.mixedEmbedding NumberField.InfinitePlace NumberField.Units.dirichletUnitTheorem
open DedekindFractionalTheta DedekindDualIdeals DedekindTraceCoordinates DedekindUnitGaussian
open DedekindThetaScales DedekindGaussianConvergence DedekindMixedAxes DedekindDiagonalTransform DedekindGeneralTheta
open scoped Classical NumberField nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

noncomputable def G (s : ℝ) (y : logSpace K) (z w : mixedSpace K) : ℂ :=
  phase (tracePair K w z) * gaussian K s w y

theorem G_coord (s : ℝ) (y : logSpace K) (z w : mixedSpace K) :
    G K s y z w = wave (a K s y) (f K z) (coord K w) := by
  simp only [G,wave,pairing,gaussian,quadratic,neg_mul,mul_assoc]

theorem G_standard (s : ℝ) (y : logSpace K) (z : mixedSpace K) (u : index K → ℝ) :
    G K s y z ((stdBasis K).equivFun.symm u) = wave (a K s y) (f K z) u := by
  rw [G_coord,coord,LinearEquiv.apply_symm_apply]

theorem integral_G {s : ℝ} (hs : 0 < s) (y : logSpace K) (z : mixedSpace K) :
    (∫ w, G K s y z w) = ((((2:ℝ)^nrComplexPlaces K)⁻¹ * s^(-(Module.finrank ℚ K : ℝ)/2) : ℝ) : ℂ) * gaussian K s⁻¹ z (-y) := by
  rw [DedekindBasisMeasure.integrate (stdBasis K) volume]
  simp only [measureReal_def,volume_fundamentalDomain_stdBasis,ENNReal.toReal_one,one_smul,G_standard,
    integral_wave _ _ (a_pos K hs y),amplitude K hs,inverse_quad K hs]
  simp only [gaussian,← mul_assoc,neg_mul]

theorem G_integer (I : FIdeal K) (s : ℝ) (y : logSpace K) (n : Idx K I → ℤ) (x : Idx K I → ℝ) :
    G K s y (mixedEmbedding K (frequency K I n).val) ((fractionalIdealLatticeBasis K I).equivFun.symm x) =
      DedekindTorusPoisson.character n x * sample K I s y x := by
  rw [G,frequency_pair,character_eq]; rfl

theorem int_sample (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) : Integrable (sample K I s y) := by
  have hi : Integrable (G K s y 0) := (DedekindBasisMeasure.integrable_iff (stdBasis K) volume _).mpr (by
    simp only [G_standard]; exact integrable_wave _ _ (a_pos K hs y))
  have h := (DedekindBasisMeasure.integrable_iff (fractionalIdealLatticeBasis K I) volume _).mp hi
  change Integrable (fun u : Idx K I → ℝ => gaussian K s ((fractionalIdealLatticeBasis K I).equivFun.symm u) y)
  simpa only [G,tracePair,mul_zero,archTrace,Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,Complex.zero_re,
    Finset.sum_const_zero,zero_add,phase,Complex.ofReal_zero,Complex.exp_zero,one_mul] using h

noncomputable def factor (I : FIdeal K) (s : ℝ) : ℂ := ((q K / normF K I) * s^(-(Module.finrank ℚ K : ℝ)/2) : ℝ)

theorem coefficient (I : FIdeal K) {s : ℝ} (hs : 0 < s) (y : logSpace K) (n : Idx K I → ℤ) :
    (∫ x, DedekindTorusPoisson.character n x * sample K I s y x) =
      factor K I s * gaussian K s⁻¹ (mixedEmbedding K (frequency K I n).val) (-y) := by
  let z := mixedEmbedding K (frequency K I n).val
  let V := ZLattice.covolume (idealLattice K I)
  let m := s^(-(Module.finrank ℚ K : ℝ)/2)
  have hV : V ≠ 0 := ZLattice.covolume_ne_zero (idealLattice K I) volume
  have hA : (2:ℝ)^nrComplexPlaces K * V = normF K I / q K := covolume_weight K I
  have hfactor : V * (q K / normF K I * m) = ((2:ℝ)^nrComplexPlaces K)⁻¹ * m := by
    field_simp [(normF_pos K I).ne',(q_pos K).ne'] at hA ⊢; linear_combination m*hA
  have h := DedekindBasisMeasure.integrate (fractionalIdealLatticeBasis K I) volume (G K s y z)
  rw [← ZLattice.covolume_eq_measure_fundamentalDomain _ _ (fundamentalDomain_idealLattice K I),Complex.real_smul,
    integral_G K hs] at h
  simp only [z,G_integer] at h
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hV)
  rw [← h,← mul_assoc]
  change _ = ((V : ℂ) * ((q K / normF K I * m : ℝ) : ℂ)) * _
  rw [← Complex.ofReal_mul,hfactor]

theorem latticePoisson : LatticePoisson K := by
  intro I s hs y
  let b := fractionalIdealLatticeBasis K I
  let g (z : Carrier K (dual K I)) := gaussian K s⁻¹ (mixedEmbedding K z.val) (-y)
  have hD : Summable fun n : Idx K I → ℤ => ∫ x, DedekindTorusPoisson.character n x * sample K I s y x := by
    simp only [coefficient K I hs y]
    exact ((frequency K I).summable_iff.mpr (abs_sum K (dual K I) (inv_pos.mpr hs) (-y))).mul_left _
  have hP := DedekindTorusPoisson.poisson (continuous_sample K I s y) (int_sample K I hs y) (uniform K I hs y) hD
  have he : raw K I s y = ∑' k : Idx K I → ℤ, sample K I s y (DedekindTorusPoisson.grid k) := by
    calc raw K I s y = ∑' z : idealLattice K I, gaussian K s z.val y :=
           (embed K I).tsum_eq (fun z => gaussian K s z.val y)
         _ = _ := by rw [← (point K I).tsum_eq]; simp only [point_eq,sample]
  rw [he,hP]; simp only [coefficient K I hs y,tsum_mul_left]
  exact congrArg (factor K I s * ·) ((frequency K I).tsum_eq g)

theorem reciprocity : Reciprocal K := reciprocal K (latticePoisson K)

end DedekindIdealPoisson

end OMA.IdealThetaReciprocity

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro K _ _ _
  exact ⟨OMA.IdealThetaReciprocity.DedekindGeneralTheta.dualLabel K, OMA.IdealThetaReciprocity.DedekindIdealPoisson.reciprocity K⟩
