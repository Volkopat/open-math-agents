import FormalConjectures.GreensOpenProblems.«1»
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.Bertrand
import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Tactic.FieldSimp

-- Reduction of Ben Green's Open Problem 1. Credit: @sturdy4days.
-- Following B. Bedert, Large sum-free subsets of sets of integers via L1-estimates,
-- arXiv:2502.08624, §§2, 4–8. The two remaining estimates concern finite
-- trigonometric polynomials. Their coefficients are given by the divisor sums
-- of the nonprincipal character modulo three.

section
open Finset
open scoped BigOperators

namespace BedertModel

/-- A nonzero dilation modulo a prime identifies all signed relations of length
four when both integer lifts fit strictly inside the no-wrap range. -/
theorem rectify {ι : Type*} {p M : ℕ} [Fact p.Prime] (small : 4*M<p)
    (a b : ι → ℤ) (ha : ∀ i, |a i| ≤ M) (hb : ∀ i, |b i| ≤ M)
    (u : ZMod p) (hu : u≠0) (lift : ∀ i, (b i : ZMod p) = u*(a i : ZMod p)) :
    (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0)) := by
  intro x c hc
  have test (f : ι → ℤ) (bound : ∀ i, |f i| ≤ M) :
      (∑ i, c i*f (x i))=0 ↔ (∑ i, (c i : ZMod p)*(f (x i):ZMod p))=0 := by
    have lim : |∑ i, c i*f (x i)| ≤ (4:ℤ)*M := calc
      _ ≤ ∑ i, |c i*f (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 4, (M : ℤ) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact (mul_le_mul (hc i) (bound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
      _ = _ := by simp [mul_comm]
    have lim' : (∑ i, c i*f (x i)).natAbs < p := by
      rw [Int.abs_eq_natAbs] at lim
      exact_mod_cast (show ((∑ i, c i*f (x i)).natAbs : ℤ) < p by
        exact lim.trans_lt (by exact_mod_cast small))
    simp only [← Int.cast_mul, ← Int.cast_sum, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · intro h; simp [h]
    · intro h; exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h (by simpa using lim')
  rw [test a ha,test b hb]
  have eqn : (∑ i, (c i : ZMod p)*(b (x i) : ZMod p)) =
      u*(∑ i, (c i : ZMod p)*(a (x i) : ZMod p)) := by
    simp only [lift,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [eqn,mul_eq_zero,or_iff_right hu]

/-- Simultaneous rectification in dimension k, with an integral bin width.
The multiplier is a difference of two residues whose coordinate boxes agree. -/
theorem box_dilate {D : Type*} [Fintype D] {p B : ℕ} [Fact p.Prime]
    (hB : 0<B) (many : B^(Fintype.card D)<p) (a : D → ℤ) :
    ∃ u : ZMod p, u≠0 ∧ ∃ r : D → ℤ, (∀ i, |r i| ≤ p/B) ∧
      ∀ i, (r i : ZMod p)=u*(a i : ZMod p) := by
  classical
  let w := p/B+1
  have hw : 0<w := by simp [w]
  have hp : p<B*w := Nat.lt_mul_div_succ p hB
  let box (v : ZMod p) (i : D) : Fin B :=
    ⟨(v*a i).val/w,(Nat.div_lt_iff_lt_mul hw).2 ((ZMod.val_lt _).trans hp)⟩
  obtain ⟨x,y,hxy,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt box (by simpa using many)
  refine ⟨x-y,sub_ne_zero.mpr hxy,fun i => ((x*a i).val : ℤ)-(y*a i).val,?_,?_⟩
  · intro i
    let X := (x*a i).val
    let Y := (y*a i).val
    have he : X/w=Y/w := congrArg Fin.val (congrFun heq i)
    have ex := Nat.mod_add_div X w
    have ey := Nat.mod_add_div Y w
    rw [he] at ex
    have xm := Nat.mod_lt X hw
    have ym := Nat.mod_lt Y hw
    change |(X:ℤ)-Y| ≤ (p/B : ℕ)
    have hw' : w=p/B+1 := rfl
    rw [abs_le]
    constructor <;> omega
  · intro i
    simp [sub_mul]

/-- A single signed representation of the input suffices: throughout the minimization only the integer values assigned to its fixed generators vary. -/
theorem dense_fixed {ι : Type*} [Fintype ι] (a : ι → ℤ) (k : ℕ)
    (span : (∃ D : Finset ℤ, D.card ≤ k ∧ ∀ i, ∃ c : D → ℤ, (∀ d, |c d| ≤ 1) ∧ a i=∑ d, c d*(d:ℤ))) :
    ∃ b : ι → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0)) ∧ ∀ i, |b i| ≤ ((16*(k+1))^k : ℕ) := by
  classical
  obtain ⟨D,hD,rep⟩ := span
  choose ε hε initial using rep
  let labels (r : D → ℤ) (i : ι) := ∑ d, ε i d*r d
  let P (M : ℕ) := ∃ r : D → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*(labels r) (x i))=0)) ∧ ∀ i, |labels r i| ≤ M
  have hP : ∃ M, P M := by
    use ∑ i, (a i).natAbs
    have eqn : labels (fun d => (d:ℤ)) = a := funext fun i => (initial i).symm
    refine ⟨(fun d => (d:ℤ)),?_⟩
    rw [eqn]
    refine ⟨fun _ _ _ => Iff.rfl,fun i => ?_⟩
    rw [Int.abs_eq_natAbs]
    exact_mod_cast Finset.single_le_sum (f:=fun i => (a i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let M := Nat.find hP
  obtain ⟨d0,rel,bnd⟩ := Nat.find_spec hP
  let b := labels d0
  change ∀ i, |b i| ≤ M at bnd
  let B := 16*(k+1)
  have pos : 0<B := by simp [B]
  by_cases done : M ≤ B^k
  · exact ⟨b,rel,fun i => (bnd i).trans (by exact_mod_cast done)⟩
  have Mpos : 0<M := by omega
  obtain ⟨p,hprime,plow,phigh⟩ := Nat.exists_prime_lt_and_le_two_mul (4*M) (by omega)
  let : Fact p.Prime := ⟨hprime⟩
  have boxes : B^(Fintype.card D)<p := by
    rw [Fintype.card_coe]
    exact (Nat.pow_le_pow_right pos hD).trans_lt (by omega)
  obtain ⟨u,hu,r,hr,lift⟩ := box_dilate pos boxes d0
  let g (i : ι) := ∑ d : D, ε i d*r d
  have width : k*(p/B)<M := by
    have := Nat.div_mul_le_self p B
    dsimp [B] at this ⊢
    nlinarith
  have gb (i : ι) : |g i| ≤ ((k*(p/B):ℕ):ℤ) := calc
    _ ≤ ∑ d : D, |ε i d*r d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : D, ((p/B:ℕ):ℤ) := Finset.sum_le_sum fun d _ => by
      rw [abs_mul]
      exact (mul_le_mul (hε i d) (hr d) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = ((D.card*(p/B):ℕ):ℤ) := by simp
    _ ≤ _ := by exact_mod_cast Nat.mul_le_mul_right (p/B) hD
  have transfer (i : ι) : (g i : ZMod p)=u*(b i : ZMod p) := by
    change ((∑ d, ε i d*r d : ℤ) : ZMod p)=u*((∑ d, ε i d*d0 d : ℤ):ZMod p)
    simp only [Int.cast_sum,Int.cast_mul,lift,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have eqv := rectify plow b g bnd (fun i => (gb i).trans (by exact_mod_cast width.le)) u hu transfer
  have smaller : P (k*(p/B)) := ⟨r, fun x c hc => (rel x c hc).trans (eqv x c hc),gb⟩
  exact False.elim ((Nat.not_le_of_lt width) (Nat.find_min' hP smaller))

/-- An inclusion-maximal dissociated subset of a finite set of integers
represents every member by a signed sum (Bedert, Lemma 6.4). -/
theorem smallSpan_of_dissociated {ι : Type*} [Fintype ι] (a : ι → ℤ) (k : ℕ)
    (dimension : ∀ D : Finset ℤ, D ⊆ univ.image a → AddDissociated (D : Set ℤ) → D.card ≤ k) :
    (∃ D : Finset ℤ, D.card ≤ k ∧ ∀ i, ∃ c : D → ℤ, (∀ d, |c d| ≤ 1) ∧ a i=∑ d, c d*(d:ℤ)) := by
  classical
  let S := univ.image a
  obtain ⟨D,hD⟩ := (S.powerset.filter fun T : Finset ℤ => AddDissociated (T:Set ℤ)).exists_maximal
    ⟨∅,mem_filter.2 ⟨empty_mem_powerset _, by simp⟩⟩
  simp only [mem_filter,mem_powerset] at hD
  have signed {u v : Finset ℤ} (hu : u⊆D) (hv : v⊆D) :
      ∃ c : D → ℤ, (∀ d, |c d| ≤ 1) ∧
        (∑ d ∈ u,d)-(∑ d ∈ v,d)=∑ d, c d*(d:ℤ) := by
    let χ (T : Finset ℤ) (x : ℤ) := if x∈T then (1:ℤ) else 0
    have eval (T : Finset ℤ) (hT : T⊆D) : (∑ d:D, χ T d*d) = ∑ d∈T,d := by
      rw [sum_coe_sort D (fun x => χ T x*x)]
      simp only [χ,ite_mul,one_mul,zero_mul,sum_ite_mem,inter_eq_right.mpr hT]
    refine ⟨fun d => χ u d-χ v d,fun d => ?_,?_⟩
    · by_cases h:(d:ℤ)∈u <;> by_cases h':(d:ℤ)∈v <;> simp [χ,h,h']
    · simp only [sub_mul,sum_sub_distrib,eval u hu,eval v hv]
  refine ⟨D,dimension D hD.1.1 hD.1.2,fun i => ?_⟩
  let x := a i
  have hxS : x∈S := mem_image_of_mem a (mem_univ i)
  by_cases hx : x∈D
  · simpa [x] using signed (singleton_subset_iff.mpr hx) (empty_subset D)
  obtain ⟨t,u,ht,hu,htu,ne,eqn⟩ := not_addDissociated_iff_exists_disjoint.1 fun h =>
    hD.not_gt ⟨insert_subset_iff.2 ⟨hxS,hD.1.1⟩,h⟩ (ssubset_insert hx)
  by_cases xt : x∈t
  · have xu : x∉u := disjoint_left.1 htu xt
    have rep := signed ((subset_insert_iff_of_notMem xu).1 hu) (subset_insert_iff.1 ht)
    have e : ((∑ z∈u,z)-(∑ z∈t.erase x,z))=x := by rw [sum_erase_eq_sub xt,eqn]; abel
    rwa [e] at rep
  rw [coe_subset,subset_insert_iff_of_notMem xt] at ht
  by_cases xu : x∈u
  · have rep := signed ht (subset_insert_iff.1 hu)
    have e : ((∑ z∈t,z)-(∑ z∈u.erase x,z))=x := by rw [sum_erase_eq_sub xu,eqn]; abel
    rwa [e] at rep
  rw [coe_subset,subset_insert_iff_of_notMem xu] at hu
  exact False.elim ((not_addDissociated_iff_exists_disjoint.2 ⟨t,u,ht,hu,htu,ne,eqn⟩) hD.1.2)

theorem dense_original {ι : Type*} [Fintype ι] (a : ι → ℤ) (k : ℕ)
    (dimension : ∀ D : Finset ℤ, D ⊆ Finset.univ.image a →
      AddDissociated (D : Set ℤ) → D.card ≤ k) :
    ∃ b : ι → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0)) ∧ ∀ i, |b i| ≤ ((16*(k+1))^k : ℕ) :=
  dense_fixed a k (smallSpan_of_dissociated a k dimension)

theorem dense_of_dissociated {ι : Type*} [Fintype ι] (a : ι → ℤ) (k : ℕ)
    (dimension : ∀ b : ι → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0)) → ∀ D : Finset ℤ, D ⊆ univ.image b →
      AddDissociated (D : Set ℤ) → D.card ≤ k) :
    ∃ b : ι → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0)) ∧ ∀ i, |b i| ≤ ((16*(k+1))^k : ℕ) :=
  dense_original a k (dimension a (fun _ _ _ => Iff.rfl))

/-- An F₄ isomorphism preserves zero, equality, and all sum triples in both directions. -/
theorem relations {ι : Type*} {a b : ι → ℤ} (h : (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*a (x i))=0 ↔ (∑ i, c i*b (x i))=0))) :
    (∀ i, a i=0 ↔ b i=0) ∧ (∀ i j, a i=a j ↔ b i=b j) ∧
    (∀ i j l, a i+a j=a l ↔ b i+b j=b l) := by
  constructor
  · intro i
    have t := h (fun _ => i) ![1,0,0,0] (by decide)
    simpa [Fin.sum_univ_four] using t
  constructor
  · intro i j
    have t := h ![i,j,i,i] ![1,-1,0,0] (by decide)
    simpa [Fin.sum_univ_four,←sub_eq_add_neg,sub_eq_zero] using t
  · intro i j l
    have t := h ![i,j,l,i] ![1,1,-1,0] (by decide)
    simpa [Fin.sum_univ_four,←sub_eq_add_neg,sub_eq_zero,←add_assoc] using t

/-- On a finite positive input one obtains an injective, zero-free integer
model of the same size and with the same additive triples. -/
theorem reindex (A : Finset ℕ) (pos : ∀ x ∈ A, 0<x) (k : ℕ)
    (dimension : ∀ b : A → ℤ, (∀ (x : Fin 4 → _) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) → ((∑ i, c i*(fun x : A => (x.val : ℤ)) (x i))=0 ↔ (∑ i, c i*b (x i))=0)) →
      ∀ D : Finset ℤ, D ⊆ univ.image b → AddDissociated (D : Set ℤ) → D.card ≤ k) :
    ∃ b : A → ℤ, Function.Injective b ∧
      (∀ x, b x ≠ 0) ∧ (∀ x y z : A, x.val+y.val=z.val ↔ b x+b y=b z) ∧
      (univ.image b).card=A.card ∧ ∀ x, |b x| ≤ ((16*(k+1))^k : ℕ) := by
  obtain ⟨b,iso,small⟩ := dense_of_dissociated (fun x : A => (x.val : ℤ)) k dimension
  obtain ⟨hz,he,ht⟩ := relations (a:=fun x : A => (x.val : ℤ)) (b:=b) iso
  have inj : Function.Injective b := fun x y h => Subtype.ext (by exact_mod_cast (he x y).mpr h)
  refine ⟨b,inj,fun x hx => ?_,fun x y z => ?_,by simp [card_image_of_injective _ inj],small⟩
  · have hh := (hz x).mpr hx
    have hp := pos x.val x.property
    omega
  · exact_mod_cast ht x y z

end BedertModel
end

section
namespace Green1Circle

open Set MeasureTheory

/-- The middle open third of the unit circle is sum-free, including when
the two summands coincide. -/
theorem middle_sumFree :
    IsSumFree (((↑) : ℝ → UnitAddCircle) '' Ioo (1/3 : ℝ) (2/3)) := by
  rw [isSumFree_iff]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ⟨z, hz, eq⟩
  obtain ⟨hx₁,hx₂⟩ := hx
  obtain ⟨hy₁,hy₂⟩ := hy
  obtain ⟨hz₁,hz₂⟩ := hz
  have congruence : ((x+y-z : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, AddCircle.coe_add, ← eq, sub_self]
  obtain ⟨n,hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp congruence
  simp only [zsmul_eq_mul, mul_one] at hn
  have hpos : (0:ℝ) < (n:ℝ) := by linarith
  have hlt : (n:ℝ) < 1 := by linarith
  have : (0:ℤ) < n := by exact_mod_cast hpos
  have : n < (1:ℤ) := by exact_mod_cast hlt
  omega

/-- The circle arc is measurable and has normalized Haar mass one third. -/
theorem middle_measure :
    let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3 : ℝ) (2/3)
    MeasurableSet I ∧ volume.real I = 1/3 := by
  intro I
  have meas : MeasurableSet I := (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet
  refine ⟨meas, ?_⟩
  have pre : QuotientAddGroup.mk ⁻¹' I ∩ Ioc (0 : ℝ) (0+1) = Ioo (1/3 : ℝ) (2/3) := by
    ext x
    constructor
    · rintro ⟨⟨y,hy,e⟩,hx⟩
      have h0 : y ∈ Ioc (0:ℝ) (0+1) := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have h := (AddCircle.coe_eq_coe_iff_of_mem_Ioc h0 hx).mp e
      simpa [← h] using hy
    · intro hx
      exact ⟨⟨x,hx,rfl⟩,by linarith [hx.1],by linarith [hx.2]⟩
  rw [Measure.real, AddCircle.add_projection_respects_measure 1 0 meas, pre, Real.volume_Ioo]
  norm_num

/-- Every nonzero integer dilation preserves the normalized Haar measure. -/
theorem dilation_preserves (b : ℤ) (hb : b ≠ 0) :
    MeasurePreserving (fun x : UnitAddCircle => b • x) volume volume :=
  Measure.measurePreserving_zsmul volume hb

end Green1Circle
end

section
open MeasureTheory
open scoped ENNReal

namespace GreenBedert

/-- For a bounded integer-valued statistic, its maximum exceeds its expectation
by at least half its mean absolute deviation. -/
theorem mean_surplus {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ℕ) (N : ℕ) (bound : ∀ x, f x ≤ N) (hf : Integrable (fun x => (f x : ℝ)) μ)
    (m : ℝ) (mean : ∫ x, (f x : ℝ) ∂μ = m) :
    ∃ x, m + (∫ y, |(f y : ℝ)-m| ∂μ)/2 ≤ f x := by
  classical
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure μ
  let M := Nat.findGreatest (fun k => ∃ x, f x=k) N
  obtain ⟨x,hx⟩ : ∃ x, f x=M := Nat.findGreatest_spec (P:=fun k => ∃ x, f x=k) (bound x₀) ⟨x₀,rfl⟩
  have upper (y : X) : (f y : ℝ) ≤ M := by
    exact_mod_cast Nat.le_findGreatest (P:=fun k => ∃ x, f x=k) (bound y) ⟨y,rfl⟩
  have m_le : m ≤ M := by
    simpa [mean] using integral_mono hf (integrable_const (M:ℝ)) upper
  let d (y : X) := (f y:ℝ)-m
  have hd : Integrable d μ := hf.sub (integrable_const m)
  have hd0 : ∫ y, d y ∂μ = 0 := by simp [d, integral_sub hf (integrable_const m), mean]
  have hle (y : X) : |d y|+d y ≤ 2*((M:ℝ)-m) := by
    rcases le_total 0 (d y) with h | h
    · rw [abs_of_nonneg h]
      dsimp [d]
      linarith [upper y]
    · rw [abs_of_nonpos h]
      linarith
  have h := integral_mono (hd.abs.add hd) (integrable_const (2*((M:ℝ)-m))) hle
  change (∫ y, |d y|+d y ∂μ) ≤ (∫ _, 2*((M:ℝ)-m) ∂μ) at h
  rw [integral_add hd.abs hd, hd0, integral_const] at h
  simp [Measure.real] at h
  refine ⟨x,?_⟩
  rw [hx]
  change m+(∫ y, |d y| ∂μ)/2 ≤ _
  linarith

/-- Dilation pullbacks of a set of mass one third have centered mean zero.
Their centered L¹ integral gives an explicit surplus at one common dilation. -/
theorem arc_surplus {X I : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (J : Set X) [DecidablePred (· ∈ J)] (hJ : MeasurableSet J) (mass : μ.real J=1/3)
    (B : Finset I) (T : I → X → X) (pres : ∀ b∈B, MeasurePreserving (T b) μ μ) :
    ∃ x, (B.card:ℝ)/3 +
      (∫ y, |(∑ b∈B, if T b y ∈ J then (1:ℝ) else 0)-(B.card:ℝ)/3| ∂μ)/2 ≤
        ∑ b∈B, if T b x ∈ J then (1:ℝ) else 0 := by
  classical
  let count (x : X) := (B.filter (fun b => T b x ∈ J)).card
  let funs (b : I) (x : X) : ℝ := if T b x ∈ J then 1 else 0
  have eqCount (x : X) : (count x:ℝ) = ∑ b∈B, funs b x := by
    dsimp only [count]
    rw [Finset.card_filter, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : T b x ∈ J <;> simp [h, funs]
  have term (b : I) (hb : b∈B) :
      Integrable (funs b) μ ∧ ∫ x, funs b x ∂μ = (1:ℝ)/3 := by
    let E := T b ⁻¹' J
    have hE : MeasurableSet E := hJ.preimage (pres b hb).measurable
    have eq : funs b = E.indicator (fun _ => (1:ℝ)) := by
      funext x
      simp [funs,Set.indicator,E]
    rw [eq]
    refine ⟨(integrable_const _).indicator hE,?_⟩
    rw [integral_indicator_const _ hE,smul_eq_mul,mul_one]
    change (μ (T b ⁻¹' J)).toReal = _
    rw [(pres b hb).measure_preimage hJ.nullMeasurableSet]
    exact mass
  have int := integrable_finsetSum B (fun b hb => (term b hb).1)
  have mean : (∫x, (count x:ℝ) ∂μ) = (B.card:ℝ)/3 := by
    simp_rw [eqCount]
    rw [integral_finsetSum _ (fun b hb => (term b hb).1)]
    rw [Finset.sum_congr rfl (fun b hb => (term b hb).2)]
    simp; ring
  obtain ⟨x,hx⟩ := mean_surplus μ count B.card (fun _ => Finset.card_filter_le ..)
    (by simpa only [eqCount] using int) _ mean
  refine ⟨x,?_⟩
  simpa only [eqCount,funs] using hx
end GreenBedert
end

section
open MeasureTheory
open scoped Classical
namespace GreenBedert

/-- One circle dilation realizes a surplus at least half the L¹ norm of the
sum of centered middle-third indicators (Bedert, Proposition 4.1(i)). -/
theorem middle_surplus (B : Finset ℤ) (hB : ∀ b∈B, b≠0) :
    let I := ((↑) : ℝ → UnitAddCircle) '' Set.Ioo (1/3 : ℝ) (2/3)
    ∃ x : UnitAddCircle, (B.card:ℝ)/3 +
      (∫ y : UnitAddCircle, |∑ b∈B, ((if b•y∈I then (1:ℝ) else 0) - 1/3)|)/2 ≤
        ∑ b∈B, if b•x∈I then (1:ℝ) else 0 := by
  intro I
  let _ : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  obtain ⟨hm,hvol⟩ := Green1Circle.middle_measure
  obtain ⟨x,hx⟩ := arc_surplus volume I hm hvol B (fun b y => b • y) (fun b hb => Green1Circle.dilation_preserves b (hB b hb))
  refine ⟨x,?_⟩
  simpa only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one_div] using hx

end GreenBedert
end

section
open MeasureTheory
namespace GreenBedert

/-- A bounded trigonometric polynomial certifies an L¹ lower bound using only
the selected Fourier coefficients (normalized Haar measure on the unit circle). -/
theorem fourier_duality (D : UnitAddCircle → ℂ) (hD : Integrable D)
    (K : Finset ℤ) (c : ℤ → ℂ)
    (bound : ∀ x : UnitAddCircle, ‖∑ k∈K, c k * fourier (-k) x‖ ≤ 1) :
    ‖∑ k∈K, c k * fourierCoeff D k‖ ≤ ∫ x, ‖D x‖ := by
  have m : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  let t (k : ℤ) (x : UnitAddCircle) := c k*(fourier (-k) x*D x)
  have int (k : ℤ) : Integrable (t k) := by
    have h : Integrable D AddCircle.haarAddCircle := m ▸ hD
    have h' := h.fourier_smul (-k)
    rw [m] at h'
    exact h'.const_mul (c k)
  have pair (k : ℤ) : c k * fourierCoeff D k = ∫ x, t k x := by
    rw [fourierCoeff,m,←integral_const_mul]
    rfl
  simp_rw [pair]
  rw [←integral_finsetSum K (fun k _ => int k)]
  refine (norm_integral_le_integral_norm _).trans (integral_mono (integrable_finsetSum K (fun k _ => int k)).norm hD.norm ?_)
  intro x
  have eq : ∑ k∈K, t k x = (∑ k∈K, c k * fourier (-k) x)*D x := by
    simp [t,Finset.sum_mul,mul_assoc]
  change ‖∑ k∈K, t k x‖ ≤ ‖D x‖
  rw [eq,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (bound x)

/-- The same coefficient certificate for a real centered counting function. -/
theorem real_fourier_duality (D : UnitAddCircle → ℝ) (hD : Integrable D)
    (K : Finset ℤ) (c : ℤ → ℂ) (bound : ∀ x : UnitAddCircle, ‖∑ k∈K, c k * fourier (-k) x‖ ≤ 1) :
    ‖∑ k∈K, c k * fourierCoeff (fun x => (D x : ℂ)) k‖ ≤ ∫ x, |D x| := by
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    fourier_duality (fun x => (D x : ℂ)) hD.ofReal K c bound

end GreenBedert
end

section
open MeasureTheory Set
namespace GreenBedert

/-- Uniform approximation of continuous functions on the unit circle in the
negative-frequency convention used by the Fourier-coefficient pairing. -/
theorem continuous_approximation (h : C(UnitAddCircle,ℂ)) {δ : ℝ} (small : 0<δ) :
    ∃ (K : Finset ℤ) (c : ℤ → ℂ), ∀ x, ‖(∑ k∈K,c k*fourier (-k) x)-h x‖ < δ := by
  classical
  let v (k : ℤ) : C(UnitAddCircle,ℂ) := fourier (-k)
  have ran : range v = range (@fourier (1:ℝ)) := by
    ext g
    constructor
    · rintro ⟨k,rfl⟩; exact ⟨-k,rfl⟩
    · rintro ⟨k,rfl⟩; exact ⟨-k, by simp [v]⟩
  have inClosure : h ∈ (Submodule.span ℂ (range v)).topologicalClosure := by
    rw [ran,span_fourier_closure_eq_top]; trivial
  obtain ⟨p,hp,dist⟩ := Metric.mem_closure_iff.mp inClosure δ small
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hp
  refine ⟨c.support,c,?_⟩
  intro x
  have hx := (ContinuousMap.norm_coe_le_norm ((c.sum fun i a => a • v i)-h) x).trans_lt
    (show ‖(c.sum fun i a => a • v i)-h‖<δ by rwa [←dist_eq_norm,dist_comm])
  simpa [Finsupp.sum,v,ContinuousMap.sum_apply] using hx

end GreenBedert
end

section
open MeasureTheory
namespace GreenBedert

/-- Every integrable real circle function admits a continuous, unit-bounded
real test function whose correlation is arbitrarily close to its L¹ norm. -/
theorem continuous_norming (D : UnitAddCircle → ℝ) (int : Integrable D) {ε : ℝ} (pos : 0<ε) :
    ∃ h : C(UnitAddCircle,ℝ), (∀ x, |h x|≤1) ∧ (∫ x, |D x|) ≤ ε + ∫x, h x*D x := by
  let _ : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  let δ := ε/3
  have sp : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,_,close,cg,ig⟩ := int.exists_hasCompactSupport_integral_sub_le sp
  let h : C(UnitAddCircle,ℝ) := ⟨fun x => g x/(|g x|+δ),cg.div (cg.abs.add continuous_const)
    (fun x => ne_of_gt (add_pos_of_nonneg_of_pos (abs_nonneg _) sp))⟩
  have bound (x) : |h x| ≤ 1 := by
    change |g x / (|g x|+δ)| ≤ 1
    have den := add_pos_of_nonneg_of_pos (abs_nonneg (g x)) sp
    rw [abs_div,abs_of_pos den,div_le_one den]
    linarith
  have gh (x) : |g x| ≤ δ + h x*g x := by
    have den := add_pos_of_nonneg_of_pos (abs_nonneg (g x)) sp
    change |g x| ≤ δ + g x/(|g x|+δ)*g x
    rw [div_mul_eq_mul_div, ←sub_le_iff_le_add',le_div_iff₀ den]
    nlinarith [sq_abs (g x),sq_nonneg δ]
  have pt (x) : |D x| ≤ δ + 2*|D x-g x| + h x*D x := by
    have first := abs_add_le (D x-g x) (g x)
    have second := (abs_le.mp (show |h x*(g x-D x)| ≤ |g x-D x| by
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (bound x))).2
    rw [abs_sub_comm (g x) (D x)] at second
    simp only [sub_add_cancel] at first
    rw [mul_sub] at second
    linarith [gh x]
  have ihD : Integrable (fun x => h x*D x) := int.bdd_mul h.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall bound)
  have ie : Integrable (fun x => 2*|D x-g x|) := (int.sub ig).abs.const_mul 2
  have ij : Integrable (fun x => δ+2*|D x-g x|) := (integrable_const δ).add ie
  have step := integral_mono int.abs (((integrable_const δ).add ie).add ihD) pt
  change (∫ x, |D x|) ≤ ∫ x, δ+2*|D x-g x|+h x*D x at step
  rw [integral_add ij ihD, integral_add (integrable_const δ) ie,
    integral_const_mul, integral_const] at step
  simp only [Real.norm_eq_abs] at close
  simp [Measure.real] at step
  exact ⟨h,bound, by dsimp [δ] at close step; linarith⟩

end GreenBedert
end

section
open MeasureTheory
namespace GreenBedert

theorem pairing_identity (D : UnitAddCircle → ℂ) (hD : Integrable D)
    (K : Finset ℤ) (c : ℤ → ℂ) :
    ∑ k∈K, c k * fourierCoeff D k = ∫ x : UnitAddCircle, (∑ k∈K, c k*fourier (-k) x)*D x := by
  have m : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  let t (k : ℤ) (x : UnitAddCircle) := c k*(fourier (-k) x*D x)
  have int (k : ℤ) : Integrable (t k) := by
    have h : Integrable D AddCircle.haarAddCircle := m ▸ hD
    have h' := h.fourier_smul (-k)
    rw [m] at h'
    exact h'.const_mul (c k)
  have pair (k : ℤ) : c k * fourierCoeff D k = ∫ x, t k x := by
    rw [fourierCoeff,m,←integral_const_mul]; rfl
  simp_rw [pair]
  rw [←integral_finsetSum K (fun k _ => int k)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp [t,Finset.sum_mul,mul_assoc]))

/-- Continuous duality and uniform trigonometric approximation show that every
strict L¹ lower bound for a real circle function already has a finite test. -/
theorem finite_certificate (D : UnitAddCircle → ℝ) (hD : Integrable D) (q : ℝ)
    (strict : q < ∫ x, |D x|) :
    ∃ (K : Finset ℤ) (c : ℤ → ℂ), (∀ x : UnitAddCircle, ‖∑ k∈K, c k*fourier (-k) x‖≤1) ∧
      q ≤ ‖∑ k∈K, c k*fourierCoeff (fun x => (D x:ℂ)) k‖ := by
  classical
  by_cases qneg : q≤0
  · exact ⟨∅,fun _ => 0,by simp,by simpa⟩
  let M := ∫ x, |D x|
  change q<M at strict
  let ε := (M-q)/4
  let δ := ε/(M+q)
  have ep : 0<ε := by dsimp [ε]; linarith
  have mp : 0<M := by linarith
  have denom : 0<M+q := by linarith
  have dp : 0<δ := div_pos ep denom
  have bal : δ*(M+q)=ε := div_mul_cancel₀ _ denom.ne'
  obtain ⟨h,hb,ht⟩ := continuous_norming D hD ep
  let H : C(UnitAddCircle,ℂ) := ⟨fun x => (h x:ℂ),Complex.continuous_ofReal.comp h.continuous⟩
  obtain ⟨K,c,close⟩ := continuous_approximation H dp
  let P (x : UnitAddCircle) := ∑ k∈K, c k*fourier (-k) x
  let f (x : UnitAddCircle) : ℂ := D x
  have cP : Continuous P := continuous_finsetSum _ fun k _ => continuous_const.mul (fourier (-k)).continuous
  have hb' (x) : ‖H x‖ ≤ 1 := by simpa [H] using hb x
  have bp (x) : ‖P x‖ ≤ 1+δ := by
    have h := norm_add_le (P x-H x) (H x)
    rw [sub_add_cancel] at h
    linarith [close x,hb' x]
  have hf : Integrable f := hD.ofReal
  have hH : Integrable (fun x => H x * f x) := hf.bdd_mul H.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hb')
  have hP : Integrable (fun x => P x * f x) := hf.bdd_mul cP.aestronglyMeasurable (Filter.Eventually.of_forall bp)
  have err : ‖(∫ x, H x*f x)-(∫x, P x*f x)‖ ≤ δ*M := by
    rw [←integral_sub hH hP]
    apply (norm_integral_le_integral_norm _).trans
    rw [show δ*M = ∫ x, δ*|D x| by rw [integral_const_mul]]
    apply integral_mono (hH.sub hP).norm (hD.abs.const_mul δ)
    intro x
    change ‖H x*f x - P x*f x‖ ≤ δ*|D x|
    rw [←sub_mul,norm_mul, norm_sub_rev]
    simpa only [f,Complex.norm_real,Real.norm_eq_abs] using mul_le_mul_of_nonneg_right (close x).le (abs_nonneg (D x))
  have old : (∫ x, H x*f x) = Complex.ofReal (∫ x, h x*D x) := by
    rw [←integral_complex_ofReal]; simp [H,f]
  have approx : q*(1+δ) ≤ ‖∫x, P x*f x‖ := by
    have a := norm_add_le ((∫x, H x*f x) - (∫x,P x*f x)) (∫x,P x*f x)
    rw [sub_add_cancel] at a
    have hh : ‖∫x, H x*f x‖ = |∫ x, h x*D x| := by rw [old,Complex.norm_real,Real.norm_eq_abs]
    rw [hh] at a
    change M ≤ ε+_ at ht
    dsimp only [ε] at bal ht
    linarith [le_abs_self (∫x,h x*D x), show δ*M+q*δ= (M-q)/4 by linarith only [bal]]
  let z : ℂ := ((1+δ:ℝ):ℂ)⁻¹
  have nz : ‖z‖ = (1+δ)⁻¹ := by simp only [z,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0<1+δ)]
  refine ⟨K,fun k => z*c k,?_,?_⟩
  · intro x
    rw [show (∑k∈K, z*c k*fourier (-k) x)=z*P x by simp [P,Finset.mul_sum,mul_assoc], norm_mul,nz]
    calc (1+δ)⁻¹*‖P x‖ ≤ (1+δ)⁻¹*(1+δ) := by gcongr; exact bp x
         _ = _ := inv_mul_cancel₀ (by linarith)
  · rw [show (∑k∈K, z*c k*fourierCoeff f k)=z*(∑k∈K,c k*fourierCoeff f k) by simp [Finset.mul_sum,mul_assoc],
        pairing_identity f hf, norm_mul,nz]
    change q ≤ (1+δ)⁻¹*‖∫x,P x*f x‖
    rw [←div_eq_inv_mul]
    exact (le_div_iff₀ (by linarith)).2 approx
end GreenBedert
end

section
open MeasureTheory
open scoped Classical
namespace GreenBedert

/-- Every bounded Fourier certificate for the centered arc indicator sum
gives a concrete integer dilation count with half that surplus. -/
theorem middle_certificate (B : Finset ℤ) (hB : ∀ b∈B, b≠0)
    (K : Finset ℤ) (c : ℤ → ℂ) (bound : ∀ x : UnitAddCircle, ‖∑ k∈K, c k*fourier (-k) x‖ ≤ 1) :
    let I := ((↑) : ℝ → UnitAddCircle) '' Set.Ioo (1/3 : ℝ) (2/3)
    let D := fun y : UnitAddCircle => ∑ b∈B, ((if b•y∈I then (1:ℝ) else 0) - 1/3)
    ∃ x : UnitAddCircle, (B.card:ℝ)/3 + ‖∑ k∈K, c k*fourierCoeff (fun y => (D y:ℂ)) k‖/2 ≤
      ∑ b∈B, if b•x∈I then (1:ℝ) else 0 := by
  intro I D
  have int : Integrable D := by
    apply integrable_finsetSum B
    intro b hb
    have s := Green1Circle.middle_measure.1.preimage (Green1Circle.dilation_preserves b (hB b hb)).measurable
    exact ((integrable_const (1:ℝ)).indicator s).sub (integrable_const _)
  obtain ⟨x,hi⟩ := middle_surplus B hB
  exact ⟨x, (add_le_add_right (div_le_div_of_nonneg_right (real_fourier_duality D int K c bound) (by norm_num : (0:ℝ) ≤ 2)) _).trans hi⟩

end GreenBedert
end

section
namespace Green1Circle
open AddCircle MeasureTheory

/-- A Fourier coefficient of a dilation survives exactly on frequencies divisible
by the dilation factor. This statement includes negative dilations and index zero. -/
theorem fourierCoeff_dilate (h : UnitAddCircle → ℂ) (hh : Integrable h haarAddCircle)
    (b k : ℤ) (hb : b ≠ 0) :
    fourierCoeff (fun x : UnitAddCircle => h (b • x)) k =
      if b ∣ k then fourierCoeff h (k/b) else 0 := by
  let μ : Measure UnitAddCircle := haarAddCircle
  by_cases d : b ∣ k
  · rw [if_pos d, fourierCoeff, fourierCoeff]
    let g : UnitAddCircle → ℂ := fun y => fourier (-(k/b)) y • h y
    have meas : AEStronglyMeasurable g μ := (hh.fourier_smul _).aestronglyMeasurable
    have keep : MeasurePreserving (fun x : UnitAddCircle => b • x) μ μ :=
      Measure.measurePreserving_zsmul μ hb
    have eq (x : UnitAddCircle) : fourier (-k) x = fourier (-(k/b)) (b • x) := by
      simp only [fourier_apply, smul_smul, neg_mul, Int.ediv_mul_cancel d]
    calc _ = ∫ x, g (b • x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x => by rw [eq])
         _ = ∫ y, g y ∂Measure.map (fun x : UnitAddCircle => b • x) μ :=
           (integral_map keep.measurable.aemeasurable (keep.map_eq.symm ▸ meas)).symm
         _ = _ := by rw [keep.map_eq]
  · rw [if_neg d]
    let a : UnitAddCircle := ((1/(b:ℝ) : ℝ) : UnitAddCircle)
    have br : (b:ℝ) ≠ 0 := by exact_mod_cast hb
    have ba : b • a = 0 := by
      change b • ((1/(b:ℝ) : ℝ) : UnitAddCircle) = 0
      rw [← AddCircle.coe_zsmul, zsmul_eq_mul, mul_one_div_cancel br, AddCircle.coe_period]
    have nontriv : fourier (-k) a ≠ 1 := by
      intro equal
      have eh : AddCircle.toCircle ((-k) • a) = AddCircle.toCircle (0 : UnitAddCircle) := by
        apply Subtype.ext
        simpa only [fourier_apply, AddCircle.toCircle_zero, Circle.coe_one] using equal
      have ze := AddCircle.injective_toCircle (T := (1:ℝ)) one_ne_zero eh
      change (-k) • ((1/(b:ℝ) : ℝ) : UnitAddCircle) = 0 at ze
      rw [← AddCircle.coe_zsmul] at ze
      obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp ze
      simp only [zsmul_eq_mul, mul_one, Int.cast_neg, mul_one_div] at hn
      have hmult := (eq_div_iff br).mp hn
      exact d ⟨-n, by exact_mod_cast (show (k:ℝ) = (b:ℝ)*(-(n:ℝ)) by linarith [mul_comm (n:ℝ) (b:ℝ)])⟩
    let g : UnitAddCircle → ℂ := fun x => fourier (-k) x * h (b • x)
    have shift (x : UnitAddCircle) : g (a+x) = fourier (-k) a * g x := by
      simp only [g, zsmul_add, ba, zero_add, fourier_apply, AddCircle.toCircle_add,
        Circle.coe_mul, mul_assoc]
    have canc : fourier (-k) a * (∫ x, g x ∂μ) = ∫ x, g x ∂μ := calc
      _ = ∫ x, (fourier (-k) a) * g x ∂μ := (integral_const_mul ..).symm
      _ = ∫ x, g (a+x) ∂μ := integral_congr_ae (Filter.Eventually.of_forall fun x => (shift x).symm)
      _ = _ := integral_add_left_eq_self g a
    have hz := sub_eq_zero.mpr canc
    rw [← one_mul (∫ x, g x ∂μ)] at hz
    exact (mul_eq_zero.mp (show (fourier (-k) a - 1) * (∫ x, g x ∂μ) = 0 by
      rw [sub_mul]; simpa using hz)).resolve_left (sub_ne_zero.mpr nontriv)

end Green1Circle
end

section
namespace Green1Circle
open AddCircle MeasureTheory

/-- For a finite superposition of circle dilations, each coefficient is the
divisor sum of the corresponding base coefficients. -/
theorem fourierCoeff_dilates (h : UnitAddCircle → ℂ) (hh : Integrable h haarAddCircle)
    (B : Finset ℤ) (nonzero : ∀ b ∈ B, b ≠ 0) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => ∑ b ∈ B, h (b • x)) k =
      ∑ b ∈ B, if b ∣ k then fourierCoeff h (k/b) else 0 := by
  let g (b : ℤ) (x : UnitAddCircle) := h (b • x)
  have integrable (b : ℤ) (hb : b ∈ B) : Integrable (g b) haarAddCircle :=
    ((Measure.measurePreserving_zsmul haarAddCircle (nonzero b hb)).integrable_comp hh.aestronglyMeasurable).mpr hh
  have eq := congrFun (fourierCoeff.sum B g integrable) k
  simp only [Finset.sum_apply] at eq
  calc _ = ∑ b ∈ B, fourierCoeff (g b) k := by
         convert eq using 2
         ext x
         simp [g]
       _ = _ := Finset.sum_congr rfl (fun b hb => fourierCoeff_dilate h hh b k (nonzero b hb))

end Green1Circle
end

section
open Set MeasureTheory
open scoped Real BigOperators

namespace GreenArcFourier

lemma coe_mem_arc_iff {t : ℝ} (ht : t ∈ Ioo 0 1) :
    (t : UnitAddCircle) ∈ (((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)) ↔ t ∈ Ioo (1 / 3) (2 / 3) := by
  refine ⟨?_, fun h ↦ ⟨t, h, rfl⟩⟩
  rintro ⟨s, ⟨hs, hs'⟩, he⟩
  have hst : s = t := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (a := (0 : ℝ)) (p := (1 : ℝ)) ⟨by linarith, by linarith⟩
    ⟨ht.1.le, by simpa using ht.2⟩).mp he
  exact hst ▸ (show s ∈ Ioo (1 / 3) (2 / 3) from ⟨hs, hs'⟩)

lemma coeff_eq_arc_integral (n : ℤ) :
    fourierCoeff ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) n = ∫ x in (1/3 : ℝ)..(2/3 : ℝ), fourier (-n) (x : UnitAddCircle) := by
  rw [fourierCoeff_eq_intervalIntegral ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) n 0]
  simp only [zero_add, div_one, one_smul]
  let g : ℝ → ℂ := fun x ↦ fourier (-n) (x : UnitAddCircle)
  let s : Set ℝ := Ioo (1/3) (2/3)
  calc
    _ = ∫ x in (0:ℝ)..1, s.indicator g x := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro x hx
      by_cases h : x ∈ Ioo (1/3 : ℝ) (2/3)
      · simp only [indicator_of_mem ((coe_mem_arc_iff hx).mpr h), s, indicator_of_mem h, smul_eq_mul, mul_one, g]
      · simp only [indicator_of_notMem (mt (coe_mem_arc_iff hx).mp h), s, indicator_of_notMem h, smul_zero]
    _ = ∫ x in (1/3 : ℝ)..(2/3 : ℝ), g x := by
      rw [intervalIntegral.integral_of_le zero_le_one, integral_indicator measurableSet_Ioo,
        Measure.restrict_restrict measurableSet_Ioo, intervalIntegral.integral_of_le (by norm_num),
        integral_Ioc_eq_integral_Ioo]
      have hsub : s ⊆ Ioc (0 : ℝ) 1 := fun x ⟨hx, hx'⟩ ↦ ⟨by linarith, by linarith⟩
      rw [inter_eq_left.mpr hsub]

lemma coeff_arc (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) n =
      (fourier (-n) ((2/3 : ℝ) : UnitAddCircle) - fourier (-n) ((1/3 : ℝ) : UnitAddCircle)) /
        (-2 * (Real.pi : ℂ) * Complex.I * n) := by
  rw [coeff_eq_arc_integral]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (1/3 : ℝ)) (b := (2/3 : ℝ))
    (fun x _ ↦ has_antideriv_at_fourier_neg (T := (1:ℝ)) inferInstance hn x)
    (((fourier (-n) : C(UnitAddCircle,ℂ)).continuous.comp (AddCircle.continuous_mk' 1)).intervalIntegrable ..)
  convert h using 1
  push_cast
  ring

end GreenArcFourier

open Set MeasureTheory Complex
open scoped Real BigOperators

namespace GreenArcFourier

lemma sin_third (n : ℤ) :
    Real.sin (2 * Real.pi * n / 3) = (Real.sqrt 3 / 2) * (fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) n := by
  have hn : n = n % 3 + 3 * (n / 3) := by omega
  have decomp : 2 * Real.pi * n / 3 =
      2 * Real.pi * (n % 3 : ℤ) / 3 + (n / 3 : ℤ) * (2 * Real.pi) := by
    conv_lhs => rw [hn]
    push_cast
    ring
  rw [decomp, Real.sin_add_int_mul_two_pi]
  have third : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three]
  have cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases cases with h | h | h
  · simp [h]
  · simp [h, third]
  · have e : 2 * Real.pi * 2 / 3 = 2 * Real.pi - 2 * Real.pi / 3 := by ring
    norm_num [h, e, Real.sin_two_pi_sub, third]

lemma boundary_diff (n : ℤ) :
    fourier (-n) ((2 / 3 : ℝ) : UnitAddCircle) - fourier (-n) ((1 / 3 : ℝ) : UnitAddCircle) =
      (Real.sqrt 3 : ℂ) * ((fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) n : ℂ) * I := by
  let θ : ℝ := 2 * Real.pi * n / 3
  have s : Real.sin θ = Real.sqrt 3 / 2 * (fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) n := sin_third n
  rw [fourier_coe_apply, fourier_coe_apply]
  have e₁ : 2 * (Real.pi : ℂ) * I * (-n : ℤ) * ((2 / 3 : ℝ) : ℂ) / (1 : ℝ) =
      (θ : ℂ) * I + (-(n : ℂ)) * (2 * Real.pi * I) := by
    dsimp [θ]; push_cast; ring
  have e₂ : 2 * (Real.pi : ℂ) * I * (-n : ℤ) * ((1 / 3 : ℝ) : ℂ) / (1 : ℝ) =
      (-(θ : ℂ)) * I := by dsimp [θ]; push_cast; ring
  rw [e₁, e₂, Complex.exp_add]
  have ep : Complex.exp (-(n : ℂ) * (2 * Real.pi * I)) = 1 := by
    simpa only [Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [ep, mul_one, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    ← Complex.ofReal_sin, s]
  push_cast
  ring

lemma coeff_eq_chi (n : ℤ) (hn : n ≠ 0) :
    fourierCoeff ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) n = -(Real.sqrt 3 : ℂ) * ((fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) n : ℂ) / (2 * Real.pi * n) := by
  rw [coeff_arc n hn, boundary_diff]
  field_simp [Real.pi_ne_zero, hn, Complex.I_ne_zero]

end GreenArcFourier

open Set MeasureTheory
open scoped Real BigOperators Classical

namespace GreenArcFourier

lemma centered_coeff (n : ℤ) :
    fourierCoeff (fun x ↦ ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) x - (1 / 3 : ℂ)) n =
      -(Real.sqrt 3 : ℂ) * ((fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) n : ℂ) / (2 * Real.pi * n) := by
  have hm : MeasurableSet (((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)) := (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet
  have hi : Integrable ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) AddCircle.haarAddCircle := (integrable_const (1:ℂ)).indicator hm
  have hc : fourierCoeff (fun _ : UnitAddCircle ↦ -(1/3 : ℂ)) n =
      (-(1/3 : ℂ)) * (Pi.single (0:ℤ) 1 : ℤ → ℂ) n := by
    have h := fourierCoeff.const_mul (fun x : UnitAddCircle ↦ fourier 0 x) (-(1/3 : ℂ)) n
    change fourierCoeff (fun x : UnitAddCircle ↦ -(1/3 : ℂ) * fourier 0 x) n =
      -(1/3 : ℂ) * fourierCoeff (fourier 0 : C(UnitAddCircle,ℂ)) n at h
    rw [fourierCoeff_fourier] at h
    simpa only [fourier_zero, mul_one] using h
  have hadd := congrFun (fourierCoeff.add hi
    (integrable_const (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (-(1/3 : ℂ)))) n
  change fourierCoeff (fun x ↦ ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) x + -(1/3 : ℂ)) n =
    fourierCoeff ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) n + fourierCoeff (fun _ : UnitAddCircle ↦ -(1/3 : ℂ)) n at hadd
  simp_rw [sub_eq_add_neg]
  rw [hadd, hc]
  by_cases h : n = 0
  · subst n
    rw [coeff_eq_arc_integral]
    simp only [neg_zero, fourier_zero, intervalIntegral.integral_const,
      Pi.single_eq_same, mul_one, Int.cast_zero, mul_zero, div_zero]
    norm_num
  · rw [coeff_eq_chi n h, Pi.single_eq_of_ne h, mul_zero, add_zero]

lemma signal_coeff (B : Finset ℤ) (hB : ∀ b ∈ B, b ≠ 0) (n : ℤ) :
    fourierCoeff (fun x : UnitAddCircle ↦ ((∑ b ∈ B,
      ((if b • x ∈ (((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)) then (1:ℝ) else 0) - 1/3) : ℝ) : ℂ)) n =
       ∑ b ∈ B, if b ∣ n then
         -(Real.sqrt 3 : ℂ) * ((fun m : ℤ ↦ (if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ)) (n/b) : ℂ) / (2 * Real.pi * ((n/b : ℤ) : ℂ))
       else 0 := by
  have hm : MeasurableSet (((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)) := (QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo).measurableSet
  have hi : Integrable ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) AddCircle.haarAddCircle := (integrable_const (1:ℂ)).indicator hm
  have h := Green1Circle.fourierCoeff_dilates (fun y ↦ ((((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3)).indicator (fun _ ↦ (1 : ℂ))) y - (1/3 : ℂ))
    (hi.sub (integrable_const _)) B hB n
  simp_rw [centered_coeff] at h
  rw [← h]
  congr 1
  funext y
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b • y ∈ (((↑) : ℝ → UnitAddCircle) '' Ioo (1 / 3 : ℝ) (2 / 3))
  · simp only [if_pos hb, Set.indicator_of_mem hb, Complex.ofReal_one]
  · simp only [if_neg hb, Set.indicator_of_notMem hb, Complex.ofReal_zero]

end GreenArcFourier
end

section
namespace GreenOneFinal

/-- The model cut-off lies inside the radius used in Section 7 of Bedert's proof. -/
theorem model_radius_growth {n : ℕ} (large : 1 ≤ Real.log n) :
    let k := ⌈(Real.log n)^4⌉₊
    Real.log ((16*(k+1))^k : ℕ) ≤ 104 * (Real.log n)^5 := by
  intro k
  let x := Real.log n
  have positive : 0 < x := lt_of_lt_of_le zero_lt_one large
  have x4 : 1 ≤ x^4 := one_le_pow₀ large
  have ceiling : (k:ℝ) ≤ 2*x^4 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x^4 by positivity)
    change (⌈x^4⌉₊:ℝ) ≤ _
    linarith
  have mulbound : 16*((k:ℝ)+1) ≤ 48*x^4 := by linarith
  have logs : Real.log (16*((k:ℝ)+1)) ≤ 52*x := by
    calc
      _ ≤ Real.log (48*x^4) := Real.log_le_log (by positivity) mulbound
      _ = Real.log 48+4*Real.log x := by rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow];norm_num
      _ ≤ 52*x := by
        have f := Real.log_le_sub_one_of_pos (by norm_num : 0<(48:ℝ))
        have g := Real.log_le_sub_one_of_pos positive
        linarith [show 1≤x from large]
  push_cast
  rw [Real.log_pow]
  calc
    _ ≤ (2*x^4)*(52*x) := mul_le_mul ceiling logs (Real.log_nonneg (by nlinarith [Nat.cast_nonneg (α := ℝ) k])) (by positivity)
    _ = 104*x^5 := by ring

end GreenOneFinal
end

section
namespace GreenOneFinal
open Filter Finset

/-- Turn an eventual guarantee of every fixed integral surplus into one
divergent real surplus valid at every size, including the empty input. -/
theorem of_eventual_gain
    (gain : ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ A : Finset ℕ,
      (∀ a ∈ A, 0 < a) → A.card = n →
      ∃ S ⊆ A, IsSumFree (S : Set ℕ) ∧ (n : ℝ)/3+j ≤ S.card) :
    type_of% @Green1.green_1 := by
  classical
  let P (j n : ℕ) := ∀ A : Finset ℕ, (∀ a ∈ A, 0 < a) → A.card = n →
      ∃ S ⊆ A, IsSumFree (S : Set ℕ) ∧ (n : ℝ)/3+j ≤ S.card
  let levels (n : ℕ) := (range (n+1)).filter (fun j => P j n)
  let Ω (n : ℕ) : ℝ := if h : (levels n).Nonempty then (levels n).max' h else -((n:ℝ)/3)
  refine ⟨Ω,?_,?_⟩
  · apply tendsto_atTop.2
    intro x
    obtain ⟨j,hj⟩ := exists_nat_ge x
    filter_upwards [eventually_ge_atTop j,gain j] with n hn ok
    have mem : j ∈ levels n := mem_filter.mpr ⟨mem_range.mpr (by omega),ok⟩
    have h : (levels n).Nonempty := ⟨j,mem⟩
    have le : j ≤ (levels n).max' h := le_max' _ _ mem
    exact hj.trans (by simpa only [Ω,dif_pos h] using (show (j:ℝ) ≤ ((levels n).max' h : ℝ) by exact_mod_cast le))
  · intro n A pos size
    by_cases h : (levels n).Nonempty
    · have ok := (mem_filter.mp ((levels n).max'_mem h)).2
      simpa only [Ω,dif_pos h] using ok A pos size
    · exact ⟨∅,empty_subset _,by rw [isSumFree_iff]; simp,by simp [Ω,h]⟩

end GreenOneFinal

namespace GreenOneFinal
open Filter Finset

/-- Pull a sum-free set through an injection preserving the additive triples
of its finite domain. -/
theorem pull_selection (A : Finset ℕ) (b : A → ℤ) (injective : Function.Injective b)
    (triples : ∀ x y z : A, x.val+y.val=z.val → b x+b y=b z)
    (U : Finset ℤ) (sub : U ⊆ univ.image b) (free : IsSumFree (U : Set ℤ)) :
    ∃ S ⊆ A, IsSumFree (S : Set ℕ) ∧ S.card=U.card := by
  classical
  let V := (univ : Finset A).filter (fun x => b x ∈ U)
  have mapped : V.image b = U := by
    ext y
    constructor
    · rintro hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact (mem_filter.mp hi).2
    · intro hy
      obtain ⟨i,_,rfl⟩ := mem_image.mp (sub hy)
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hy⟩,rfl⟩
  refine ⟨V.image Subtype.val,?_,isSumFree_iff.mpr ?_,?_⟩
  · intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact i.property
  · intro x hx y hy hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    obtain ⟨k,hk,hs⟩ := mem_image.mp hz
    have excluded := isSumFree_iff.mp free (b i) (mem_filter.mp hi).2 (b j) (mem_filter.mp hj).2
    rw [triples i j k hs.symm] at excluded
    exact excluded (mem_filter.mp hk).2
  · rw [card_image_of_injective _ Subtype.val_injective,← mapped,card_image_of_injective _ injective]

/-- A Freiman model of dimension above the cut-off or a dense model of small
dimension suffices to obtain the exact natural-number statement. -/
theorem split_models (k : ℕ → ℕ) (Cert : ℕ → Finset ℤ → Prop)
    (high : ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℤ, 0 ∉ B → B.card=n →
      (∀ b ∈ B, -b ∉ B) →
      (∃ D ⊆ B, AddDissociated (D : Set ℤ) ∧ k n < D.card) → Cert j B)
    (low : ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℤ, 0 ∉ B → B.card=n →
      (∀ b ∈ B, -b ∉ B) →
      (∀ D ⊆ B, AddDissociated (D : Set ℤ) → D.card ≤ k n) →
      (∀ b ∈ B, |b| ≤ ((16*(k n+1))^(k n) : ℕ)) → Cert j B)
    (gain : ∀ j B, 0 ∉ B → Cert j B →
      ∃ S ⊆ B, IsSumFree (S : Set ℤ) ∧ (B.card : ℝ)/3+j ≤ S.card) :
    type_of% @Green1.green_1 := by
  classical
  apply of_eventual_gain
  intro j
  filter_upwards [high j,low j] with n hi lo
  intro A positive card
  let a (x : A) : ℤ := x.val
  let Four (b : A → ℤ) : Prop :=
    ∀ (x : Fin 4 → A) (c : Fin 4 → ℤ), (∀ i, |c i| ≤ 1) →
      ((∑ i, c i * a (x i))=0 ↔ (∑ i, c i * b (x i))=0)
  have choose_model : ∃ b : A → ℤ, Four b ∧
      ((∃ D ⊆ univ.image b, AddDissociated (D : Set ℤ) ∧ k n < D.card) ∨
        (∀ D ⊆ univ.image b, AddDissociated (D : Set ℤ) → D.card ≤ k n) ∧
        (∀ x, |b x| ≤ ((16*(k n+1))^(k n) : ℕ))) := by
    by_cases big : ∃ b : A → ℤ, Four b ∧
        ∃ D ⊆ univ.image b, AddDissociated (D : Set ℤ) ∧ k n < D.card
    · obtain ⟨b,iso,witness⟩ := big
      exact ⟨b,iso,Or.inl witness⟩
    · have dim (b : A → ℤ) (hb : Four b) (D : Finset ℤ)
          (sub : D ⊆ univ.image b) (diss : AddDissociated (D : Set ℤ)) : D.card ≤ k n := by
        by_contra! large
        exact big ⟨b,hb,D,sub,diss,large⟩
      obtain ⟨b,iso,bound⟩ := BedertModel.dense_of_dissociated a (k n) dim
      exact ⟨b,iso,Or.inr ⟨dim b iso,bound⟩⟩
  obtain ⟨b,iso,reason⟩ := choose_model
  obtain ⟨zero,eqs,tr⟩ := BedertModel.relations (a := a) (b := b) iso
  dsimp only [a] at zero eqs tr
  have inj : Function.Injective b := fun x y h => Subtype.ext (by exact_mod_cast (eqs x y).mpr h)
  have nz : 0 ∉ univ.image b := by
    intro h
    obtain ⟨x,_,hx⟩ := mem_image.mp h
    have xv : x.val = 0 := by exact_mod_cast (zero x).mpr hx
    exact (positive x.val x.property).ne' xv
  have size : (univ.image b).card = n := by simp [card_image_of_injective _ inj,card]
  have sign : ∀ v ∈ univ.image b, -v ∉ univ.image b := by
    intro v hv opposite
    obtain ⟨x,_,rfl⟩ := mem_image.mp hv
    obtain ⟨y,_,hy⟩ := mem_image.mp opposite
    have h := iso ![x,y,x,x] ![1,1,0,0] (by decide)
    simp [Fin.sum_univ_four] at h
    have e : a x+a y=0 := h.mpr (by rw [hy]; simp)
    have positiveX := positive x.val x.property
    have positiveY := positive y.val y.property
    dsimp only [a] at e
    omega
  have cert : Cert j (univ.image b) := by
    rcases reason with big | ⟨dim,radius⟩
    · exact hi _ nz size sign big
    · apply lo _ nz size sign dim
      intro v hv
      obtain ⟨x,_,rfl⟩ := mem_image.mp hv
      exact radius x
  obtain ⟨U,sub,free,large⟩ := gain j _ nz cert
  obtain ⟨S,subset,ind,same⟩ := pull_selection A b inj (fun x y z h =>
    (tr x y z).mp (by exact_mod_cast h)) U sub free
  rw [size] at large
  exact ⟨S,subset,ind,by simpa only [same] using large⟩

end GreenOneFinal
end

namespace OMA.R_Green1_green_1_R1

open Filter MeasureTheory Set
open scoped Real BigOperators Classical

/-- The high-dimensional estimate, corresponding to §§4–5 of Bedert. -/
def H1 : Prop :=
  let w := fun m : ℤ ↦ -(Real.sqrt 3 : ℂ) *
      ((if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ) : ℂ) /
        (2 * Real.pi * (m : ℂ))
  ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℤ, 0 ∉ B → B.card = n →
    (∀ b ∈ B, -b ∉ B) →
    let k := ⌈(Real.log (n : ℝ)) ^ 4⌉₊
    (∃ D ⊆ B, AddDissociated (D : Set ℤ) ∧ k < D.card) →
    ∃ K : Finset ℤ, ∃ c : ℤ → ℂ,
      (∀ x : UnitAddCircle, ‖∑ m ∈ K, c m * fourier (-m) x‖ ≤ 1) ∧
      (2 * (j : ℝ)) ≤ ‖∑ m ∈ K, c m * ∑ b ∈ B, if b ∣ m then w (m / b) else 0‖

/-- The bounded low-dimensional estimate, corresponding to §§6–8 of Bedert. -/
def H2 : Prop :=
  let w := fun m : ℤ ↦ -(Real.sqrt 3 : ℂ) *
      ((if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ) : ℂ) /
        (2 * Real.pi * (m : ℂ))
  ∀ j : ℕ, ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℤ, 0 ∉ B → B.card = n →
    (∀ b ∈ B, -b ∉ B) →
    let k := ⌈(Real.log (n : ℝ)) ^ 4⌉₊
    (∀ D ⊆ B, AddDissociated (D : Set ℤ) → D.card ≤ k) →
    (∀ b ∈ B, |b| ≤ ((16 * (k + 1)) ^ k : ℕ)) →
    ∃ K : Finset ℤ, ∃ c : ℤ → ℂ,
      (∀ x : UnitAddCircle, ‖∑ m ∈ K, c m * fourier (-m) x‖ ≤ 1) ∧
      (2 * (j : ℝ)) ≤ ‖∑ m ∈ K, c m * ∑ b ∈ B, if b ∣ m then w (m / b) else 0‖

theorem main : H1 → H2 → type_of% @Green1.green_1 := by
  intro high low
  let w := fun m : ℤ ↦ -(Real.sqrt 3 : ℂ) *
      ((if m % 3 = 0 then 0 else if m % 3 = 1 then 1 else -1 : ℝ) : ℂ) /
        (2 * Real.pi * (m : ℂ))
  let Cert (j : ℕ) (B : Finset ℤ) := ∃ K : Finset ℤ, ∃ c : ℤ → ℂ,
      (∀ x : UnitAddCircle, ‖∑ m ∈ K, c m * fourier (-m) x‖ ≤ 1) ∧
      (2 * (j : ℝ)) ≤ ‖∑ m ∈ K, c m * ∑ b ∈ B, if b ∣ m then w (m / b) else 0‖
  apply GreenOneFinal.split_models (fun n ↦ ⌈(Real.log (n : ℝ)) ^ 4⌉₊) Cert high low
  intro j B hB certificate
  obtain ⟨K, c, bound, size⟩ := certificate
  have nz : ∀ b ∈ B, b ≠ 0 := fun b hb eq ↦ hB (eq ▸ hb)
  let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3 : ℝ) (2/3)
  obtain ⟨x, hx⟩ := GreenBedert.middle_certificate B nz K c bound
  simp_rw [GreenArcFourier.signal_coeff B nz] at hx
  change (B.card : ℝ)/3 + ‖∑ m ∈ K, c m * ∑ b ∈ B, if b ∣ m then w (m/b) else 0‖/2 ≤
      ∑ b ∈ B, if b • x ∈ I then (1:ℝ) else 0 at hx
  refine ⟨B.filter (fun b ↦ b • x ∈ I), Finset.filter_subset _ _, ?_, ?_⟩
  · rw [isSumFree_iff]
    intro u hu v hv huv
    obtain ⟨_, h₁⟩ := Finset.mem_filter.mp hu
    obtain ⟨_, h₂⟩ := Finset.mem_filter.mp hv
    obtain ⟨_, h₃⟩ := Finset.mem_filter.mp huv
    rw [add_smul] at h₃
    exact isSumFree_iff.mp Green1Circle.middle_sumFree _ h₁ _ h₂ h₃
  · have h := (add_le_add_right ((le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
        ((mul_comm _ _).le.trans size)) ((B.card:ℝ)/3)).trans hx
    simpa only [Finset.sum_boole] using h

end OMA.R_Green1_green_1_R1
