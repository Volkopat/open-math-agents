import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib

namespace TunnellFiniteSymbols
end TunnellFiniteSymbols
namespace TunnellFullClassTheta
end TunnellFullClassTheta
namespace TunnellGaussCalibration
end TunnellGaussCalibration
namespace TunnellRankin
end TunnellRankin
namespace TunnellRankinCalibration
end TunnellRankinCalibration
namespace TunnellRankinEisenstein
end TunnellRankinEisenstein
namespace TunnellToric
end TunnellToric

/- TunnellFrickePrimitive -/
section
namespace TunnellFricke
open Complex hiding eta
open Function ModularForm Set Filter Metric
open UpperHalfPlane hiding I
open scoped Real Topology
noncomputable def h (z : ℂ) := eta z ^2 * eta (2*z)^2
noncomputable def disk (q : ℂ) := (∏' n : ℕ, (1-(q^4)^(n+1)))^2 *
  (∏' n : ℕ, (1-(q^8)^(n+1)))^2
lemma disk_rot (q : ℂ) : disk (I*q) = disk q := by
  simp [disk,mul_pow,I_pow_four,show Complex.I^8=1 by rw [show 8=4*2 by decide,pow_mul,I_pow_four,one_pow]]
lemma present (z : ℂ) : h z = Periodic.qParam 4 z * disk (Periodic.qParam 4 z) := by
  have h1 : Periodic.qParam 1 z = Periodic.qParam 4 z ^4 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h2 : Periodic.qParam 1 (2*z) = Periodic.qParam 4 z ^8 := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul]; push_cast; congr 1; ring
  have h0 : Periodic.qParam 24 z ^2 * Periodic.qParam 24 (2*z)^2 = Periodic.qParam 4 z := by
    simp only [Periodic.qParam,← Complex.exp_nat_mul,← Complex.exp_add]; push_cast; congr 1; ring
  simp only [h,eta,eta_q,h1,h2,mul_pow,disk]
  linear_combination (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 4)^(k+1)))^2 *
    (∏' k : ℕ, (1-(Periodic.qParam 4 z ^ 8)^(k+1)))^2 * h0
lemma q_T (z : ℂ) : Periodic.qParam 4 (z+1) = I*Periodic.qParam 4 z := by
  simp only [Periodic.qParam]
  push_cast
  rw [show 2*(Real.pi:ℂ)*I*(z+1)/4 = Real.pi/2*I + 2*Real.pi*I*z/4 by ring,
    exp_add,exp_pi_div_two_mul_I]
end TunnellFricke
end


/- TunnellBaseActual -/
section
namespace TunnellRoot
open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open scoped Manifold Topology
end TunnellRoot
namespace TunnellRoot
open Complex UpperHalfPlane Matrix MatrixGroups ModularForm
open Matrix.GeneralLinearGroup Matrix.SpecialLinearGroup ConjAct Pointwise
open scoped Manifold
end TunnellRoot
namespace TunnellEtaUniform
open Filter Finset Polynomial
open scoped Topology
end TunnellEtaUniform
namespace TunnellTaylor
open Filter Polynomial Finset
open scoped Topology
end TunnellTaylor
namespace TunnellEtaValue
open UpperHalfPlane Function MatrixGroups ModularForm
open scoped Manifold Real Topology
noncomputable def etaValue (z : ℍ) : ℂ :=
  eta (4*(z:ℂ))^2 * eta (8*(z:ℂ))^2
end TunnellEtaValue
open UpperHalfPlane MatrixGroups
open TunnellEtaValue
end


/- TunnellEtaLevelGenerators -/
section
namespace TunnellEtaLevel
open Complex TunnellFricke Matrix MatrixGroups ModularGroup
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section
lemma trans_one (z : ℂ) : h (z+1)=I*h z := by
  rw [present,q_T,disk_rot,present z,mul_assoc]
lemma trans (n : ℤ) (z : ℂ) : h (z+(n:ℂ))=I^n*h z := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    simpa [zpow_add₀ I_ne_zero,add_assoc,mul_left_comm,mul_comm,mul_assoc] using
      (trans_one (z+k)).trans (congrArg (I*·) ih)
  | pred k ih =>
    let m : ℤ := -(k:ℤ)
    change h (z+(m:ℂ))=I^m*h z at ih
    change h (z+((m-1:ℤ):ℂ))=I^(m-1)*h z
    have he := trans_one (z+(m:ℂ)-1)
    rw [sub_add_cancel,ih] at he
    simp only [Int.cast_sub,Int.cast_one]
    rw [show z+((m:ℂ)-1)=z+(m:ℂ)-1 by ring]
    apply mul_left_cancel₀ I_ne_zero
    rw [←he,zpow_sub₀ I_ne_zero,zpow_one]
    field_simp
end
end TunnellEtaLevel
end


/- TunnellEtaCongruence -/
section
namespace TunnellEtaLevel
open Complex TunnellFricke Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellEtaValue
open UpperHalfPlane hiding I
open scoped ModularForm
noncomputable section
lemma physical (z : ℍ) : etaValue z = h (4*(z:ℂ)) := by
  simp [etaValue,h,show 2*(4*(z:ℂ))=8*z by ring]
end
end TunnellEtaLevel
end


/- TunnellHalfConjugate -/
section
namespace TunnellHalfNormalizer
open Matrix MatrixGroups ModularGroup CongruenceSubgroup
noncomputable section
def tau (s : ℤ) : SL(2,ℝ) := ⟨!![1,(s:ℝ)/2;0,1],by simp [Matrix.det_fin_two]⟩
lemma tau_neg (s : ℤ) : tau (-s)*tau s=1 := by
  apply Subtype.ext
  change !![(1:ℝ),((-s:ℤ):ℝ)/2;0,1]*!![1,(s:ℝ)/2;0,1]=1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_fin_two,Matrix.one_apply] <;> ring
lemma model (g : Gamma0 32) : ∃ a b k l : ℤ, g.val.val=!![a,b;32*k,a+2*l] := by
  let a := g.val 0 0
  let b := g.val 0 1
  let e := g.val 1 1
  obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp g.property)
  have H := g.val.property
  rw [Matrix.det_fin_two,hk] at H
  change a*e-b*(32*k)=1 at H
  have h := congrArg (fun x : ℤ => (x:ZMod 2)) H
  push_cast at h
  have hz : (32:ZMod 2)=0 := by decide
  rw [hz,zero_mul,mul_zero,sub_zero] at h
  have same : ∀ a e : ZMod 2, a*e=1 → a=e := by decide
  obtain ⟨l,hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub a e 2).mp (same _ _ h)
  refine ⟨a,b,k,l,?_⟩
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · exact hk
  · change e=a+2*l; omega
lemma exists_shift (s : ℤ) (g : Gamma0 32) :
    ∃ h : Gamma0 32, tau s*(g.val:SL(2,ℝ))=(h.val:SL(2,ℝ))*tau s := by
  obtain ⟨a,b,k,l,H⟩ := model g
  have hdet := g.val.property
  rw [H,Matrix.det_fin_two] at hdet
  change a*(a+2*l)-b*(32*k)=1 at hdet
  let h : SL(2,ℤ) := ⟨!![a+16*s*k,b+s*l-8*s^2*k;32*k,a+2*l-16*s*k],by
    rw [Matrix.det_fin_two]; change (a+16*s*k)*(a+2*l-16*s*k)-(b+s*l-8*s^2*k)*(32*k)=1
    linear_combination hdet⟩
  have hh : h∈Gamma0 32 := by apply Gamma0_mem.mpr; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨k,rfl⟩
  refine ⟨⟨h,hh⟩,?_⟩
  apply Subtype.ext
  change (tau s).val*(g.val:SL(2,ℝ)).val=(h:SL(2,ℝ)).val*(tau s).val
  rw [SpecialLinearGroup.coe_matrix_coe,SpecialLinearGroup.coe_matrix_coe,H]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,tau,h,Matrix.map_apply] <;> ring
def shift (s : ℤ) (g : Gamma0 32) := (exists_shift s g).choose
lemma shift_spec (s : ℤ) (g : Gamma0 32) :
    tau s*(g.val:SL(2,ℝ))=((shift s g).val:SL(2,ℝ))*tau s := (exists_shift s g).choose_spec
lemma undo (s : ℤ) (g : Gamma0 32) : shift (-s) (shift s g)=g := by
  apply Subtype.ext
  apply SpecialLinearGroup.map_intCast_injective (R:=ℝ)
  have h : (tau (-s)*tau s)*(g.val:SL(2,ℝ))=
      ((shift (-s) (shift s g)).val:SL(2,ℝ))*(tau (-s)*tau s) := by
    rw [mul_assoc,shift_spec,←mul_assoc (tau (-s)),shift_spec,mul_assoc]
  simpa only [tau_neg,one_mul,mul_one] using h.symm
def conjugate : Gamma0 32 ≃ Gamma0 32 where
  toFun := shift 1
  invFun := shift (-1)
  left_inv := undo 1
  right_inv g := by simpa using undo (-1) g
end
end TunnellHalfNormalizer
end


/- TunnellHalfNormalizer -/
section
namespace TunnellHalfNormalizer
open Matrix MatrixGroups ModularGroup CongruenceSubgroup MeasureTheory
open UpperHalfPlane hiding I
noncomputable section
def U : ℍ ≃ᵐ ℍ := MeasurableEquiv.smul (SpecialLinearGroup.mapGL ℝ (tau 1))
lemma preserving : MeasurePreserving U := measurePreserving_smul (SpecialLinearGroup.mapGL ℝ (tau 1)) volume
lemma cast_action (g : SL(2,ℤ)) (z : ℍ) : (g:SL(2,ℝ)) • z=g • z := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply (g:SL(2,ℝ)),coe_specialLinearGroup_apply g] <;> rfl
theorem intertwine (g : Gamma0 32) (z : ℍ) : U (g.val • z) = (conjugate g).val • U z := by
  change tau 1 • (g.val • z)=(shift 1 g).val • (tau 1 • z)
  rw [←cast_action g.val,←cast_action (shift 1 g).val,←mul_smul,shift_spec,mul_smul]
lemma U_coe (z : ℍ) : (U z:ℂ)=(z:ℂ)+1/2 := by
  change ((tau 1 • z:ℍ):ℂ)=(z:ℂ)+1/2
  rw [coe_specialLinearGroup_apply]
  norm_num [tau]
lemma U_im (z : ℍ) : (U z).im=z.im := by
  change (↑(U z):ℂ).im=(z:ℂ).im; rw [U_coe]; norm_num
end
end TunnellHalfNormalizer
end


/- TunnellTraceExpansion -/
section
namespace TunnellHalfFourier
open scoped UpperHalfPlane
noncomputable section
abbrev q (z : ℍ) := Function.Periodic.qParam 1 (z:ℂ)
def Expansion (F : ℍ→ℂ) (a : ℕ→ℂ) := ∀ z, HasSum (fun m : ℕ => a m*q z^m) (F z)
end
end TunnellHalfFourier
end


/- TunnellHalfFourier -/
section
namespace TunnellHalfFourier
open TunnellHalfNormalizer
open UpperHalfPlane hiding I
noncomputable section
lemma half_q (z : ℍ) : q (U z)= -q z := by
  rw [q,q,U_coe]
  unfold Function.Periodic.qParam
  simp only [Complex.ofReal_one]
  rw [show 2*(Real.pi:ℂ)*Complex.I*((z:ℂ)+1/2)/1 =
    (2*(Real.pi:ℂ)*Complex.I*(z:ℂ)/1)+(Real.pi:ℂ)*Complex.I by ring,Complex.exp_add,Complex.exp_pi_mul_I]
  ring
theorem even_fixed {F : ℍ→ℂ} {a : ℕ→ℂ} (hF : Expansion F a) (hodd : ∀ m, Odd m → a m=0) (z : ℍ) :
    F (U z)=F z := by
  apply (hF (U z)).unique
  apply (hF z).congr_fun
  intro n
  rcases Nat.even_or_odd n with hn|hn
  · rw [half_q,hn.neg_pow]
  · rw [hodd n hn,zero_mul,zero_mul]
def remainder (u v w : ℂ) (F F₁ F₁₇ : ℍ→ℂ) (z : ℍ) := u*F z - v*F₁ z-w*F₁₇ z
end
end TunnellHalfFourier
end


/- TunnellTraceRegular -/
section
namespace TunnellHalfPairing
open ModularForm Complex MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup UpperHalfPlane
open scoped UpperHalfPlane ComplexConjugate
noncomputable section
def pair (F : ℍ→ℂ) (z : ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*conj (F z)
def regular (F : ℍ→ℂ) :=
  Measurable (pair F) ∧ (∀ (g : Gamma0 32) z, pair F (g.val • z)=pair F z) ∧
  ∀ q : SL(2,ℤ) ⧸ Gamma0 32, IntegrableOn (fun z => pair F (q.out⁻¹ • z)) fdo
end
end TunnellHalfPairing
end


/- TunnellShell -/
section
namespace TunnellShell
open OMA.R_CongruentNumber_Tunnell_even_R1 CongruentNumber Finset
open scoped PowerSeries.WithPiTopology
abbrev Triple := ℤ × ℤ × ℤ
def normSq (v : Triple) : ℤ := v.1^2+v.2.1^2+v.2.2^2
def shell (N : ℕ) : Finset Triple :=
  let I := Finset.Icc (-(N:ℤ)-1) (N+1:ℤ)
  (I ×ˢ (I ×ˢ I)).filter (fun v => normSq v=N)
end TunnellShell
end


/- TunnellRankinCosetTiles -/
section
namespace TunnellRankinIntegral
open Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein
noncomputable section
abbrev Cosets (L : ℕ) := SL(2,ℤ) ⧸ Gamma0 L
def rep {L : ℕ} (q : Cosets L) : SL(2,ℤ) := q.out⁻¹
def cosetProd {L : ℕ} (p : Cosets L × Gamma0 L) : SL(2,ℤ) := p.2.val*rep p.1
lemma cosetProd_class {L : ℕ} (q : Cosets L) (g : Gamma0 L) :
    (QuotientGroup.mk (cosetProd (q,g))⁻¹:Cosets L)=q := by
  change QuotientGroup.mk ((g.val*q.out⁻¹)⁻¹)=q
  rw [_root_.mul_inv_rev,inv_inv,QuotientGroup.mk_mul_of_mem _ ((Gamma0 L).inv_mem g.property)]
  exact Quotient.out_eq' _
lemma cosetProd_bijective (L : ℕ) : Function.Bijective (cosetProd (L:=L)) := by
  constructor
  · rintro ⟨q,g⟩ ⟨w,h⟩ eq
    have e := congrArg (fun γ : SL(2,ℤ) => (QuotientGroup.mk γ⁻¹:Cosets L)) eq
    rw [cosetProd_class,cosetProd_class] at e
    subst w
    exact Prod.ext rfl (Subtype.ext (mul_right_cancel eq))
  · intro g
    let q : Cosets L := QuotientGroup.mk g⁻¹
    have he : ((g⁻¹:SL(2,ℤ)):Cosets L)=((q.out:SL(2,ℤ)):Cosets L) := (Quotient.out_eq' q).symm
    have hh := QuotientGroup.eq.mp he
    rw [inv_inv] at hh
    exact ⟨(q,⟨g*q.out,hh⟩),by simp [cosetProd,rep]⟩
end
end TunnellRankinIntegral
end


/- TunnellRankinModularDomain -/
section
namespace TunnellRankinDomain
open Complex Matrix MatrixGroups ModularGroup UpperHalfPlane Set MeasureTheory Metric
open scoped Pointwise Modular
noncomputable section
lemma vertical_null (r : ℝ) : volume {z : ℂ | z.re=r}=0 := by
  let s := ({r}:Set ℝ) ×ˢ (univ:Set ℝ)
  have e : ({z : ℂ | z.re=r}:Set ℂ) = measurableEquivRealProd ⁻¹' s := by ext; simp [s]
  rw [e,volume_preserving_equiv_real_prod.measure_preimage_equiv,Measure.volume_eq_prod]
  simp [s]
lemma boundary_null : volume (fd\fdo)=0 := by
  have h : volume (UpperHalfPlane.coe '' (fd\fdo))=0 := by
    apply measure_mono_null (t:=(sphere (0:ℂ) 1 ∪ {z : ℂ | z.re=1/2}) ∪ {z : ℂ | z.re= -(1/2)})
    · rintro _ ⟨z,⟨hz,hn⟩,rfl⟩
      change 1≤normSq (z:ℂ) ∧ |z.re|≤1/2 at hz
      change ¬(1<normSq (z:ℂ) ∧ |z.re|<1/2) at hn
      by_cases eq : ‖(z:ℂ)‖=1
      · exact Or.inl (Or.inl (by simpa using eq))
      have hnorm : 1<normSq (z:ℂ) := by
        rw [normSq_eq_norm_sq] at hz ⊢
        apply (one_lt_sq_iff₀ (norm_nonneg _)).mpr
        exact lt_of_le_of_ne ((one_le_sq_iff₀ (norm_nonneg _)).mp hz.1) (Ne.symm eq)
      have ha : |z.re|=1/2 := le_antisymm hz.2 (le_of_not_gt fun hh => hn ⟨hnorm,hh⟩)
      rcases abs_choice z.re with h|h
      · exact Or.inl (Or.inr (by change z.re=1/2; linarith))
      · exact Or.inr (by change z.re= -(1/2); linarith)
    · exact measure_union_null (measure_union_null (Measure.addHaar_sphere volume (0:ℂ) 1) (vertical_null _)) (vertical_null _)
  rw [UpperHalfPlane.volume_eq_lintegral,Measure.restrict_eq_zero.mpr h,lintegral_zero_measure]
lemma smul_null (g : SL(2,ℤ)) (s : Set ℍ) (hs : volume s=0) :
    volume ((g • ·) ⁻¹' s) = 0 :=
  measure_preimage_smul_null hs (g:GL (Fin 2) ℝ)
theorem ae_pair : ∀ᵐ z : ℍ, ∃ g : SL(2,ℤ),
    ∀ h : SL(2,ℤ), h • z∈fdo ↔ h=g ∨ h= -g := by
  letI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2→Fin 2→ℤ))
  letI : Countable (SL(2,ℤ)) := Function.Injective.countable (f:=fun g : SL(2,ℤ) => g.val) Subtype.val_injective
  have he : ∀ᵐ z : ℍ, ∀ g : SL(2,ℤ), g • z∉fd\fdo := by
    apply ae_all_iff.mpr
    intro g
    apply ae_iff.mpr
    convert smul_null g _ boundary_null using 2
    ext z
    simp
  filter_upwards [he] with z hz
  obtain ⟨g,hg⟩ := exists_smul_mem_fd z
  have hg' : g • z∈fdo := by by_contra e; exact hz g ⟨hg,e⟩
  refine ⟨g,fun h => ⟨fun hh => ?_,?_⟩⟩
  · have H : (h*g⁻¹) • (g • z)∈fdo := by simpa [mul_smul] using hh
    rcases eq_one_or_neg_one_of_mem_fdo_mem_fdo hg' H with eq|eq
    · left; exact mul_inv_eq_one.mp eq
    · right
      calc
        h=(h*g⁻¹)*g := by simp
        _= -g := by rw [eq]; simp
  · rintro (rfl|rfl) <;> simpa only [SL_neg_smul] using hg'
end
end TunnellRankinDomain
end


/- TunnellRankinTileIntegral -/
section
namespace TunnellRankinDomain
open Complex Matrix MatrixGroups ModularGroup UpperHalfPlane Set MeasureTheory
open scoped Pointwise ENNReal
noncomputable section
local instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2→Fin 2→ℤ))
local instance : Countable (SL(2,ℤ)) := Function.Injective.countable (f:=fun g : SL(2,ℤ) => g.val) Subtype.val_injective
def mark : ℍ→ℝ≥0∞ := fdo.indicator (fun _ => 1)
lemma mark_meas : Measurable mark := measurable_const.indicator isOpen_fdo.measurableSet
lemma neg_distinct (g : SL(2,ℤ)) : g≠ -g := by
  intro eq
  have e := congrArg (·*g⁻¹) eq
  have h : (1:SL(2,ℤ))= -1 := by simpa using e
  have := congrArg (fun m : SL(2,ℤ) => m.val 0 0) h
  norm_num at this
lemma ae_mark : ∀ᵐ z : ℍ, ∑' g : SL(2,ℤ), mark (g⁻¹ • z)=2 := by
  classical
  filter_upwards [ae_pair] with z hz
  obtain ⟨w,hw⟩ := hz
  change (∑' g : SL(2,ℤ),mark (((Equiv.inv _) g) • z))=2
  rw [(Equiv.inv (SL(2,ℤ))).tsum_eq (fun g => mark (g • z))]
  have e : ∀ g : SL(2,ℤ), mark (g • z) = if g=w ∨ g= -w then 1 else 0 := by
    intro g
    change (if g • z ∈ fdo then 1 else 0)=_
    rw [hw]
    split_ifs <;> rfl
  simp_rw [e]
  rw [tsum_eq_sum (s:={w,-w}) (fun x hx => if_neg (by simpa using hx))]
  rw [Finset.sum_insert (by simpa using neg_distinct w),Finset.sum_singleton]
  norm_num
def pull (g : SL(2,ℤ)) (f : ℍ→ℝ≥0∞) (z : ℍ) := mark (g⁻¹ • z)*f z
lemma pull_meas (g : SL(2,ℤ)) {f : ℍ→ℝ≥0∞} (hf : Measurable f) : Measurable (pull g f) :=
  (mark_meas.comp (measurePreserving_smul ((g⁻¹:SL(2,ℤ)):GL (Fin 2) ℝ) volume).measurable).mul hf
lemma pull_eq (g : SL(2,ℤ)) {f : ℍ→ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z in fdo, f (g • z)=∫⁻ z, pull g f z := by
  have h : MeasurePreserving (fun z : ℍ => g • z) := measurePreserving_smul (g:GL (Fin 2) ℝ) volume
  rw [←h.lintegral_comp (pull_meas g hf),←lintegral_indicator isOpen_fdo.measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : z∈fdo <;> simp [pull,mark,hz]
end
end TunnellRankinDomain
end


/- TunnellRankinPetersson -/
section
namespace TunnellRankinIntegral
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup TunnellRankinEisenstein TunnellRankin
open TunnellShell TunnellFullClassTheta TunnellEtaValue Set MeasureTheory
open UpperHalfPlane hiding I
open scoped ComplexConjugate ENNReal
noncomputable section
def petersson (L : ℕ) (F : ℍ→ℂ) : ℂ :=
  ∑' q : Cosets L, ∫ z in fdo,F (rep q • z)
variable {d : ℕ} {b : Triple} (hsq : Squarefree (2*d)) (hd : d%4=1) (hb : b∈shell (2*d))
end
end TunnellRankinIntegral
end


/- TunnellHalfPairing -/
section
namespace TunnellHalfNormalizer
open TunnellEtaLevel TunnellEtaValue TunnellFricke
open UpperHalfPlane hiding I
lemma eta_anti (z : ℍ) : etaValue (U z)= -etaValue z := by
  rw [physical,physical,U_coe,show 4*((z:ℂ)+1/2)=4*(z:ℂ)+((2:ℤ):ℂ) by push_cast; ring,trans]
  norm_num [Complex.I_sq]
end TunnellHalfNormalizer
namespace TunnellHalfPairing
open Complex MeasureTheory Set TunnellRankinIntegral TunnellEtaValue TunnellHalfNormalizer TunnellHalfFourier
open MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane
open scoped ComplexConjugate
noncomputable section
lemma pair_eta (F : ℍ→ℂ) (z : ℍ) : pair F z=(z.im:ℂ)^2*etaValue z*conj (F z) := rfl
theorem anti {F : ℍ→ℂ} (he : ∀ z, F (U z)=F z) : pair F ∘ U=fun z => -pair F z := by
  funext z
  simp [Function.comp_def,pair_eta,U_im,eta_anti,he]
theorem value (u v w : ℝ) (F G H : ℍ→ℂ) (z : ℍ) :
    pair (remainder u v w F G H) z=(u:ℂ)*pair F z-(v:ℂ)*pair G z-(w:ℂ)*pair H z := by
  simp only [pair,remainder,map_sub,map_mul,Complex.conj_ofReal]
  ring
theorem regular_sub (u v w : ℝ) {F G H : ℍ→ℂ} (hf : regular F) (hg : regular G) (hh : regular H) :
    regular (remainder u v w F G H) := by
  refine ⟨?_,?_,?_⟩
  · rw [show pair (remainder u v w F G H)=fun z => (u:ℂ)*pair F z-(v:ℂ)*pair G z-(w:ℂ)*pair H z from funext (value u v w F G H)]
    exact ((hf.1.const_mul _).sub (hg.1.const_mul _)).sub (hh.1.const_mul _)
  · intro a z; simp only [value,hf.2.1,hg.2.1,hh.2.1]
  · intro q; simp only [value]
    exact (((hf.2.2 q).const_mul _).sub ((hg.2.2 q).const_mul _)).sub ((hh.2.2 q).const_mul _)
theorem linear (u v w : ℝ) {F G H : ℍ→ℂ} (hf : regular F) (hg : regular G) (hh : regular H) :
    petersson 32 (pair (remainder u v w F G H))=
      (u:ℂ)*petersson 32 (pair F)-(v:ℂ)*petersson 32 (pair G)-(w:ℂ)*petersson 32 (pair H) := by
  classical
  letI := Fintype.ofFinite (Cosets 32)
  simp only [petersson,tsum_fintype,value]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro q _
  let f (z:ℍ) := (u:ℂ)*pair F (rep q • z)
  let g (z:ℍ) := (v:ℂ)*pair G (rep q • z)
  let h (z:ℍ) := (w:ℂ)*pair H (rep q • z)
  have fi : IntegrableOn f fdo := (hf.2.2 q).const_mul (u:ℂ)
  have gi : IntegrableOn g fdo := (hg.2.2 q).const_mul (v:ℂ)
  have hi : IntegrableOn h fdo := (hh.2.2 q).const_mul (w:ℂ)
  change (∫ z in fdo,(f-g) z-h z)=_
  rw [integral_sub (fi.sub gi) hi]
  change (∫ z in fdo,f z-g z)-(∫ z in fdo,h z)=_
  rw [integral_sub fi gi]
  dsimp only [f,g,h]
  simp only [MeasureTheory.integral_const_mul]
end
end TunnellHalfPairing
end


/- TunnellPeterssonMask -/
section
namespace TunnellPeterssonMask
open Complex Matrix MatrixGroups ModularGroup CongruenceSubgroup MeasureTheory Set
open TunnellRankinIntegral TunnellRankinDomain
open UpperHalfPlane hiding I
open scoped ENNReal Pointwise
noncomputable section
local instance : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2→Fin 2→ℤ))
local instance : Countable (SL(2,ℤ)) := Function.Injective.countable (f:=fun g : SL(2,ℤ) => g.val) Subtype.val_injective
local instance (L : ℕ) : Countable (Cosets L) := Function.Injective.countable (f:=fun q : Cosets L => q.out) Quotient.out_injective
def mask (L : ℕ) (z : ℍ) := ∑' q : Cosets L, mark ((rep q)⁻¹ • z)
def quotientMeasure (L : ℕ) : Measure ℍ := volume.withDensity (mask L)
lemma mask_meas (L : ℕ) : Measurable (mask L) := by
  apply Measurable.ennreal_tsum
  intro q
  exact mark_meas.comp (measurePreserving_smul (((rep q)⁻¹:SL(2,ℤ)):GL (Fin 2) ℝ) volume).measurable
lemma twice (L : ℕ) : ∀ᵐ z : ℍ, ∑' g : Gamma0 L, mask L (g.val⁻¹ • z)=2 := by
  filter_upwards [ae_mark] with z hz
  unfold mask
  rw [ENNReal.tsum_comm]
  let e := Equiv.ofBijective _ (cosetProd_bijective L)
  have h := e.tsum_eq (fun g : SL(2,ℤ) => mark (g⁻¹ • z))
  rw [←hz,←h,ENNReal.tsum_prod']
  apply tsum_congr; intro q; apply tsum_congr; intro g
  change _=mark ((g.val*rep q)⁻¹ • z)
  rw [_root_.mul_inv_rev,mul_smul]
lemma quotient_lintegral (L : ℕ) {f : ℍ→ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂quotientMeasure L=∑' q : Cosets L,∫⁻ z in fdo,f (rep q • z) := by
  rw [quotientMeasure,lintegral_withDensity_eq_lintegral_mul _ (mask_meas L) hf]
  simp_rw [pull_eq _ hf]
  rw [←lintegral_tsum (fun q : Cosets L => (pull_meas (rep q) hf).aemeasurable)]
  apply lintegral_congr; intro z
  exact (ENNReal.tsum_mul_right).symm
lemma replace_mask (L : ℕ) {a b f : ℍ→ℝ≥0∞} (ha : Measurable a) (hb : Measurable b) (hf : Measurable f)
    (A : ∀ᵐ z:ℍ, ∑' g : Gamma0 L, a (g.val⁻¹ • z)=2)
    (B : ∀ᵐ z:ℍ, ∑' g : Gamma0 L, b (g.val⁻¹ • z)=2)
    (inv : ∀ (g : Gamma0 L) z, f (g.val • z)=f z) :
    ∫⁻ z,a z*f z=∫⁻ z,b z*f z := by
  have mp (g : Gamma0 L) : MeasurePreserving (fun z : ℍ => g.val • z) :=
    measurePreserving_smul (g.val:GL (Fin 2) ℝ) volume
  have expand (a b : ℍ→ℝ≥0∞) (ha : Measurable a) (hb : Measurable b)
      (H : ∀ᵐ z:ℍ,∑' g : Gamma0 L,b (g.val⁻¹ • z)=2) :
      2*(∫⁻ z,a z*f z)=∑' g : Gamma0 L,∫⁻ z,b (g.val⁻¹ • z)*(a z*f z) := by
    rw [←lintegral_const_mul 2 (show Measurable (fun z => a z*f z) from ha.mul hf),←lintegral_tsum (fun (g : Gamma0 L) =>
      (show Measurable (fun z : ℍ => b (g.val⁻¹ • z)*(a z*f z)) from (hb.comp (mp g⁻¹).measurable).mul (ha.mul hf)).aemeasurable)]
    apply lintegral_congr_ae
    filter_upwards [H] with z hz
    rw [ENNReal.tsum_mul_right,hz]
  apply (ENNReal.mul_right_inj (by norm_num : (2:ℝ≥0∞)≠0) (by norm_num : (2:ℝ≥0∞)≠⊤)).mp
  rw [expand a b ha hb B,expand b a hb ha A,←(Equiv.inv (Gamma0 L)).tsum_eq (fun g : Gamma0 L => ∫⁻ z,a (g.val⁻¹ • z)*(b z*f z))]
  apply tsum_congr
  intro g
  rw [←(mp g).lintegral_comp (show Measurable (fun z : ℍ => b (g.val⁻¹ • z)*(a z*f z)) from (hb.comp (mp g⁻¹).measurable).mul (ha.mul hf))]
  apply lintegral_congr
  intro z
  simp [-ModularGroup.sl_moeb,inv,mul_left_comm]
end
end TunnellPeterssonMask
end


/- TunnellPeterssonNormalizer -/
section
namespace TunnellPeterssonMask
open Matrix MatrixGroups ModularGroup CongruenceSubgroup MeasureTheory TunnellRankinIntegral
open UpperHalfPlane Set
open scoped ENNReal
noncomputable section
variable (L : ℕ) [NeZero L]
def tileMeasure (q : Cosets L) := Measure.map (fun z : ℍ => rep q • z) (volume.restrict fdo)
lemma quotient_tiles : quotientMeasure L = Measure.sum (tileMeasure L) := by
  letI := Fintype.ofFinite (Cosets L)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [quotient_lintegral L hf,lintegral_sum_measure]
  apply tsum_congr; intro q
  symm; exact lintegral_map hf (measurePreserving_smul ((rep q):GL (Fin 2) ℝ) volume).measurable
lemma integrable_quotient {f : ℍ→ℂ} (hf : Measurable f)
    (hi : ∀ q : Cosets L, IntegrableOn (fun z => f (rep q • z)) fdo) :
    Integrable f (quotientMeasure L) := by
  letI := Fintype.ofFinite (Cosets L)
  rw [quotient_tiles]
  apply integrable_sum_measure _ ((hasSum_fintype _).summable)
  intro q
  exact (integrable_map_measure hf.aestronglyMeasurable (measurePreserving_smul ((rep q):GL (Fin 2) ℝ) volume).measurable.aemeasurable).mpr (hi q)
lemma quotient_integral {f : ℍ→ℂ} (hf : Measurable f) (hi : Integrable f (quotientMeasure L)) :
    TunnellRankinIntegral.petersson L f = ∫ z,f z ∂quotientMeasure L := by
  letI := Fintype.ofFinite (Cosets L)
  rw [quotient_tiles] at hi ⊢
  rw [integral_sum_measure hi,TunnellRankinIntegral.petersson]
  apply tsum_congr; intro q
  symm; exact integral_map (measurePreserving_smul ((rep q):GL (Fin 2) ℝ) volume).measurable.aemeasurable hf.aestronglyMeasurable
variable (U : ℍ ≃ᵐ ℍ) (hU : MeasurePreserving U) (e : Gamma0 L ≃ Gamma0 L)
    (he : ∀ (g : Gamma0 L) z,U (g.val • z)=(e g).val • U z)
include hU he in
lemma normalizer_lintegral {f : ℍ→ℝ≥0∞} (hf : Measurable f)
    (H : ∀ (g : Gamma0 L) z,f (g.val • z)=f z) :
    ∫⁻ z, f (U z) ∂quotientMeasure L=∫⁻ z,f z ∂quotientMeasure L := by
  let b (z : ℍ) := mask L (U.symm z)
  have hb : Measurable b := (mask_meas L).comp U.symm.measurable
  have inv_sum (a : ℍ→ℝ≥0∞) (z : ℍ) : (∑' g : Gamma0 L, a (g.val⁻¹ • z))=∑' g : Gamma0 L,a (g.val • z) :=
    (Equiv.inv (Gamma0 L)).tsum_eq (fun g : Gamma0 L => a (g.val • z))
  have h2 : ∀ᵐ z : ℍ, ∑' g : Gamma0 L,b (g.val⁻¹ • z)=2 := by
    have ae := (hU.symm U).quasiMeasurePreserving.ae (twice L)
    filter_upwards [ae] with z hz
    rw [inv_sum,←e.tsum_eq (fun g => b (g.val • z)),←hz,inv_sum]
    apply tsum_congr; intro g
    have h := he g (U.symm z)
    simp only [U.apply_symm_apply] at h
    simp [b,←h]
  rw [quotientMeasure,lintegral_withDensity_eq_lintegral_mul _ (mask_meas L) (show Measurable (fun z => f (U z)) from hf.comp U.measurable),
    lintegral_withDensity_eq_lintegral_mul _ (mask_meas L) hf]
  calc
    _ = ∫⁻ z,b z*f z := by
      rw [←hU.lintegral_comp (show Measurable (fun z => b z*f z) from hb.mul hf)]
      simp [b]
    _ = _ := replace_mask L hb (mask_meas L) hf h2 (twice L) H
include hU he in
lemma normalizer_map {f : ℍ→ℂ} (hf : Measurable f)
    (H : ∀ (g : Gamma0 L) z,f (g.val • z)=f z) :
    Measure.map (f ∘ U) (quotientMeasure L)=Measure.map f (quotientMeasure L) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (hf.comp U.measurable),lintegral_map hg hf]
  exact normalizer_lintegral L U hU e he (hg.comp hf) (fun g₀ z => congrArg g (H g₀ z))
include hU he in
theorem normalizer {f : ℍ→ℂ} (hf : Measurable f) (hi : Integrable f (quotientMeasure L))
    (H : ∀ (g : Gamma0 L) z,f (g.val • z)=f z) :
    TunnellRankinIntegral.petersson L (f ∘ U) = TunnellRankinIntegral.petersson L f := by
  let μ := quotientMeasure L
  have eq := normalizer_map L U hU e he hf H
  have hfi : Integrable id (Measure.map f μ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hf.aemeasurable).mpr hi
  rw [←eq] at hfi
  have hFU := hf.comp U.measurable
  have hfi' : Integrable (f ∘ U) μ :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hFU.aemeasurable).mp hfi
  rw [quotient_integral L hFU hfi',quotient_integral L hf hi]
  calc
    _ = ∫ x : ℂ,x ∂Measure.map (f ∘ U) μ := (integral_map hFU.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ x : ℂ,x ∂Measure.map f μ := by rw [eq]
    _ = _ := integral_map hf.aemeasurable measurable_id.aestronglyMeasurable
end
end TunnellPeterssonMask
end


/- TunnellSignedTraceSquare -/
section
namespace TunnellWindingTrace
open TunnellShell TunnellHalfFourier TunnellHalfPairing TunnellHalfNormalizer TunnellRankinIntegral
open TunnellFiniteSymbols TunnellFricke TunnellRankinCalibration TunnellGaussCalibration TunnellToric
open scoped UpperHalfPlane
noncomputable section
lemma vanish {F : ℍ→ℂ} (hr : regular F) (he : ∀ z, F (U z)=F z) : petersson 32 (pair F)=0 := by
  have h := TunnellPeterssonMask.normalizer 32 U preserving conjugate intertwine hr.1
    (TunnellPeterssonMask.integrable_quotient 32 hr.1 hr.2.2) hr.2.1
  rw [anti he] at h
  simp only [petersson,MeasureTheory.integral_neg,tsum_neg] at h ⊢
  linear_combination -h/2
end
end TunnellWindingTrace
end


/- TunnellPublicHalfMoment -/
section
namespace TunnellPublicHalfMoment
open TunnellHalfPairing TunnellHalfFourier TunnellRankinIntegral TunnellWindingTrace TunnellHalfNormalizer
open scoped UpperHalfPlane
noncomputable section
theorem result : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H3 := by
  intro F Y Z a b c u v x y w t rF rY rZ eF eY eZ ha hb hc
  let A := 4*(w:ℝ)^2
  let B := (w:ℝ)^2*(t:ℝ)^2
  let C := 4*(x:ℝ)^2-(t:ℝ)^2*(y:ℝ)^2
  let H := remainder A B C F Y Z
  have hinv (z:ℍ) : H (U z)=H z := by
    apply even_fixed (a:=fun m => (A:ℂ)*a m-(B:ℂ)*b m-(C:ℂ)*c m)
    · intro τ
      apply (((eF τ).mul_left (A:ℂ)).sub ((eY τ).mul_left (B:ℂ)) |>.sub ((eZ τ).mul_left (C:ℂ))).congr_fun
      intro m; ring
    · intro m hm
      rw [ha m hm,hb m hm,hc m hm]
      dsimp only [A,B,C]; push_cast; ring
  have H0 := vanish (regular_sub A B C rF rY rZ) hinv
  rw [linear _ _ _ rF rY rZ] at H0
  change (w:ℂ)^2*(4*petersson 32 (pair F)-(t:ℂ)^2*petersson 32 (pair Y))=
    (4*(x:ℂ)^2-(t:ℂ)^2*(y:ℂ)^2)*petersson 32 (pair Z)
  dsimp only [A,B,C] at H0; push_cast at H0
  linear_combination H0
end
end TunnellPublicHalfMoment
end


theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H3 := TunnellPublicHalfMoment.result
