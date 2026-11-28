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
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Fin.Basic
import Mathlib.Order.WellFounded
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial

/-! Every finite set of positive integers has a sum-free subset of size
n/3 plus a quantity tending to infinity. Based on Benjamin Bedert, Large
sum-free subsets of sets of integers via L¹-estimates, arXiv:2502.08624.
Credit: @sturdy4days. The high-dimensional argument uses a dissociated Riesz
product, and the low-dimensional argument uses the residue classes from §§7–8.
-/

section

-- Following B. Bedert, Large sum-free subsets of sets of integers via L1-estimates,
-- arXiv:2502.08624, §§2, 4–8. The two estimates concern finite
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
  have Mpos : 0< M := by omega
  obtain ⟨p,hprime,plow,phigh⟩ := Nat.exists_prime_lt_and_le_two_mul (4*M) (by omega)
  let : Fact p.Prime := ⟨hprime⟩
  have boxes : B^(Fintype.card D)<p := by
    rw [Fintype.card_coe]
    exact (Nat.pow_le_pow_right pos hD).trans_lt (by omega)
  obtain ⟨u,hu,r,hr,lift⟩ := box_dilate pos boxes d0
  let g (i : ι) := ∑ d : D, ε i d*r d
  have width : k*(p/B)< M := by
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
  change q< M at strict
  let ε := (M-q)/4
  let δ := ε/(M+q)
  have ep : 0<ε := by dsimp [ε]; linarith
  have mp : 0< M := by linarith
  have denom : 0< M+q := by linarith
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
end

section
/-! Bedert’s high-dimensional estimate for Green’s sum-free set problem.
We combine the Riesz-product estimate for dissociated characters with the finite Möbius sieve and the square-summable Fourier tail. Their logarithmic loss is overcome by the fourth-power threshold on additive dimension (Bedert, arXiv:2502.08624, Sections 4–5). The prime reciprocal estimate is credited separately below. -/

section

/-! Mertens' prime reciprocal estimate. This portion was proved by @senamakel in
Open Math Agents PR 2394 and included in the accepted proof of the positive-density
variant of Erdős 955 (public main c7ffad9b7e5d5341b55813cfb3b6d16b163fcf41). -/
open scoped Classical

namespace OMALib.Mertens

open Real Finset

theorem log_factorial_eq_sum (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ p ∈ Nat.primesLE N, ((N.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    exact ⟨(Nat.Prime.dvd_factorial hp.1).1 hp.2.1, hp.1⟩
  · intro p _
    simp

theorem div_le_factorization_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    N / p ≤ N.factorial.factorization p := by
  rcases lt_or_ge N p with h | h
  · simp [Nat.div_eq_of_lt h]
  rw [Nat.factorization_factorial hp (Nat.lt_add_one (Nat.log p N))]
  have h1 : 1 ∈ Ico 1 (Nat.log p N + 1) := by
    simp only [mem_Ico, le_refl, true_and]
    have := Nat.log_pos hp.one_lt h
    omega
  have := Finset.single_le_sum (f := fun i => N / p ^ i) (fun i _ => Nat.zero_le _) h1
  simpa using this

theorem real_div_sub_one_le_nat_div (N p : ℕ) (hp : 0 < p) :
    (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := by
  have h := Nat.lt_div_mul_add (a := N) hp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 : (N : ℝ) < ((N / p : ℕ) : ℝ) * p + p := by exact_mod_cast h
  rw [div_sub_one hp'.ne', div_le_iff₀ hp']
  linarith

theorem log_factorial_le (N : ℕ) : Real.log (N.factorial : ℝ) ≤ N * Real.log N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rw [← Real.log_pow]
  apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos N)
  exact_mod_cast Nat.factorial_le_pow N

theorem log_factorial_ge (N : ℕ) : N * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h := Real.pow_div_factorial_le_exp (N : ℝ) (Nat.cast_nonneg N) N
  have hf : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hNp : (0 : ℝ) < (N : ℝ) ^ N := by positivity
  have h2 := Real.log_le_log (by positivity) h
  rw [Real.log_exp, Real.log_div hNp.ne' hf.ne', Real.log_pow] at h2
  linarith

theorem summable_log_div_mul_sub_one :
    Summable (fun n : ℕ => Real.log n / ((n : ℝ) * ((n : ℝ) - 1))) := by
  have hs : Summable (fun n : ℕ => 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      apply div_nonneg (Real.log_nonneg (by linarith))
      nlinarith
  · rcases Nat.lt_or_ge n 2 with h | h
    · interval_cases n <;> simp
    · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
      have hn : (0 : ℝ) < n := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
        Real.log_le_rpow_div hn.le (by norm_num)
      have hsq : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) = n * n := by
        rw [← Real.rpow_add hn]; norm_num; ring
      have hpos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn _
      have hden : (n : ℝ) * n / 2 ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      have hden0 : 0 < (n : ℝ) * n / 2 := by positivity
      calc Real.log n / ((n : ℝ) * ((n : ℝ) - 1))
          ≤ Real.log n / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) hden0 hden
        _ ≤ ((n : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((n : ℝ) * n / 2) :=
            div_le_div_of_nonneg_right hlog hden0.le
        _ = 4 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
            rw [← hsq]; field_simp; ring

/-- Mertens' first theorem, upper half, over the naturals. -/
theorem sum_log_div_le_nat (N : ℕ) :
    ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ Real.log N + Real.log 4 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp only [Nat.primesLE_zero, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    exact Real.log_nonneg (by norm_num)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) ≤ Real.log (N.factorial : ℝ) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ hl
    calc (N : ℝ) / p - 1 ≤ ((N / p : ℕ) : ℝ) := real_div_sub_one_le_nat_div N p hpp.pos
      _ ≤ _ := by exact_mod_cast div_le_factorization_factorial hpp N
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p - 1) =
      N * ∑ p ∈ Nat.primesLE N, Real.log p / p - Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hth := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  have hf := log_factorial_le N
  rw [hsplit] at key
  have : (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

/-- The convergent sum over primes of `log p / (p (p - 1))`, which bounds the contribution of
higher prime powers in Legendre's formula. -/
noncomputable def primePowerConst : ℝ := ∑' n : ℕ, Real.log n / ((n : ℝ) * ((n : ℝ) - 1))

theorem sum_log_div_mul_sub_one_le (s : Finset ℕ) :
    ∑ p ∈ s, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ primePowerConst := by
  apply summable_log_div_mul_sub_one.sum_le_tsum s
  intro n _
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    apply div_nonneg (Real.log_nonneg (by linarith))
    nlinarith

/-- Mertens' first theorem, lower half, over the naturals. -/
theorem sum_log_div_ge_nat (N : ℕ) :
    Real.log N - 1 - primePowerConst ≤ ∑ p ∈ Nat.primesLE N, Real.log p / p := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have := sum_log_div_mul_sub_one_le ∅
    simp at this ⊢
    linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have key : Real.log (N.factorial : ℝ) ≤
      ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [log_factorial_eq_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hpp := (Nat.mem_primesLE.mp hp).2
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hl
    have h1 : ((N.factorial.factorization p : ℕ) : ℝ) ≤ ((N / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorization_factorial_le_div_pred hpp N
    have h2 : ((N / (p - 1) : ℕ) : ℝ) ≤ (N : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le
    have h3 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub hpp.one_lt.le]; simp
    rw [h3] at h2
    have h4 : (N : ℝ) / ((p : ℝ) - 1) = (N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      have : (p : ℝ) ≠ 0 := by linarith
      field_simp
      ring
    linarith
  have hsplit : ∑ p ∈ Nat.primesLE N, Real.log p * ((N : ℝ) / p + N / ((p : ℝ) * ((p : ℝ) - 1))) =
      N * (∑ p ∈ Nat.primesLE N, Real.log p / p +
        ∑ p ∈ Nat.primesLE N, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hsplit] at key
  have hK := sum_log_div_mul_sub_one_le (Nat.primesLE N)
  have hf := log_factorial_ge N
  have : (N : ℝ) * (Real.log N - 1 - primePowerConst) ≤ N * ∑ p ∈ Nat.primesLE N, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hNr

theorem primePowerConst_nonneg : 0 ≤ primePowerConst := by
  have := sum_log_div_mul_sub_one_le ∅
  simpa using this

/-- The constant in Mertens' first theorem proved here. -/
noncomputable def mertens1Const : ℝ := Real.log 4 + 1 + primePowerConst

theorem abs_sum_log_div_sub_log_le_nat (N : ℕ) :
    |∑ p ∈ Nat.primesLE N, Real.log p / p - Real.log N| ≤ mertens1Const := by
  have h1 := sum_log_div_le_nat N
  have h2 := sum_log_div_ge_nat N
  have h3 := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [abs_le]; unfold mertens1Const; constructor <;> linarith

theorem log_le_log_floor_add (x : ℝ) (hx : 1 ≤ x) :
    Real.log ⌊x⌋₊ ≤ Real.log x ∧ Real.log x ≤ Real.log ⌊x⌋₊ + Real.log 2 := by
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.mpr hx
  have hN : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hlt : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  constructor
  · exact Real.log_le_log (by linarith) hle
  · rw [← Real.log_mul (by linarith) (by norm_num)]
    apply Real.log_le_log (by linarith)
    linarith

/-- **Mertens' first theorem.** For real `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ log 4 + log 2 + 1 + primePowerConst`. -/
theorem abs_sum_log_div_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ mertens1Const + Real.log 2 := by
  have h := abs_sum_log_div_sub_log_le_nat ⌊x⌋₊
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x hx
  have h3 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' first theorem**, existential form. -/
theorem mertens1 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log p / p - Real.log x| ≤ C :=
  ⟨mertens1Const + Real.log 2, fun x hx => abs_sum_log_div_sub_log_le x (by linarith)⟩

theorem sum_succ_eq (N : ℕ) (f : ℕ → ℝ) :
    ∑ p ∈ Nat.primesLE (N + 1), f p =
      (∑ p ∈ Nat.primesLE N, f p) + if (N + 1).Prime then f (N + 1) else 0 := by
  rw [Nat.primesLE_succ]
  split_ifs with h
  · rw [Finset.sum_insert, add_comm]
    intro hm
    have := (Nat.mem_primesLE.mp hm).1
    omega
  · simp

theorem recip_step (N : ℕ) :
    (∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p) - ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p =
      ((∑ p ∈ Nat.primesLE (N + 1), Real.log p / p) - ∑ p ∈ Nat.primesLE N, Real.log p / p) /
        Real.log ((N + 1 : ℕ) : ℝ) := by
  rw [sum_succ_eq, sum_succ_eq]
  split_ifs with h
  · have hl : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast h.one_lt)
    field_simp
    ring
  · simp

/-- Elementary comparison of `log b - log a` with `(b - a) / b`, for `0 < a ≤ b ≤ a + 1`. -/
theorem abs_log_sub_log_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ a + 1) :
    |(b - a) / b - (Real.log b - Real.log a)| ≤ 1 / a - 1 / b := by
  have hb : 0 < b := by linarith
  have hq : 0 < b / a := div_pos hb ha
  have hlog : Real.log b - Real.log a = Real.log (b / a) := (Real.log_div hb.ne' ha.ne').symm
  have hup := Real.log_le_sub_one_of_pos hq
  have hlo := Real.one_sub_inv_le_log_of_pos hq
  rw [inv_div] at hlo
  rw [hlog]
  have e1 : (b - a) / b = 1 - a / b := by field_simp
  have e2 : 1 / a - 1 / b = (b - a) / (a * b) := by field_simp
  have e3 : b / a - 1 - (1 - a / b) = (b - a) * ((b - a) / (a * b)) := by field_simp
  have hnn : 0 ≤ (b - a) / (a * b) := div_nonneg (by linarith) (by positivity)
  have e4 : (b - a) * ((b - a) / (a * b)) ≤ (b - a) / (a * b) := by
    have : b - a ≤ 1 := by linarith
    nlinarith
  rw [abs_le, e2, e1]
  constructor <;> nlinarith

/-- Partial sums used in the proof of Mertens' second theorem. -/
noncomputable def mertensG (N : ℕ) : ℝ :=
  (∑ p ∈ Nat.primesLE N, (1 : ℝ) / p) - Real.log (Real.log N) -
    ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N

theorem mertensG_step (N : ℕ) (hN : 2 ≤ N) :
    |mertensG (N + 1) - mertensG N| ≤
      (mertens1Const + 1) * (1 / Real.log N - 1 / Real.log ((N + 1 : ℕ) : ℝ)) := by
  set a := Real.log N with ha_def
  set b := Real.log ((N + 1 : ℕ) : ℝ) with hb_def
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have ha : 0 < a := Real.log_pos (by linarith)
  have hab : a ≤ b := Real.log_le_log (by linarith) (by push_cast; linarith)
  have hb : 0 < b := by linarith
  have hb1 : b ≤ a + 1 := by
    have h1 : b - a = Real.log (((N + 1 : ℕ) : ℝ) / N) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have h2 := Real.log_le_sub_one_of_pos (x := ((N + 1 : ℕ) : ℝ) / N) (by positivity)
    have h3 : ((N + 1 : ℕ) : ℝ) / N - 1 ≤ 1 := by
      push_cast
      rw [div_sub_one (by linarith), div_le_iff₀ (by linarith)]
      linarith
    linarith
  set S0 := ∑ p ∈ Nat.primesLE N, Real.log p / p
  set S1 := ∑ p ∈ Nat.primesLE (N + 1), Real.log p / p
  set F0 := ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p
  set F1 := ∑ p ∈ Nat.primesLE (N + 1), (1 : ℝ) / p
  have hstep : F1 - F0 = (S1 - S0) / b := recip_step N
  have hR : |S0 - a| ≤ mertens1Const := abs_sum_log_div_sub_log_le_nat N
  have hdiff : mertensG (N + 1) - mertensG N =
      (S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a)) := by
    have e : mertensG (N + 1) - mertensG N =
        (F1 - F0) - (Real.log b - Real.log a) - (S1 - b) / b + (S0 - a) / a := by
      simp only [mertensG]
      ring
    rw [e, hstep]
    field_simp
    ring
  have hE := abs_log_sub_log_sub_le ha hab hb1
  have hpos : 0 ≤ 1 / a - 1 / b := by
    rw [sub_nonneg]; exact one_div_le_one_div_of_le ha hab
  rw [hdiff]
  calc |(S0 - a) * (1 / a - 1 / b) + ((b - a) / b - (Real.log b - Real.log a))|
      ≤ |(S0 - a) * (1 / a - 1 / b)| + |(b - a) / b - (Real.log b - Real.log a)| := abs_add_le _ _
    _ ≤ mertens1Const * (1 / a - 1 / b) + (1 / a - 1 / b) := by
      rw [abs_mul, abs_of_nonneg hpos]
      gcongr
    _ = (mertens1Const + 1) * (1 / a - 1 / b) := by ring

theorem abs_mertensG_sub_le (N : ℕ) (hN : 2 ≤ N) :
    |mertensG N - mertensG 2| ≤ (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hs := mertensG_step n hn
    calc |mertensG (n + 1) - mertensG 2|
        = |(mertensG (n + 1) - mertensG n) + (mertensG n - mertensG 2)| := by ring_nf
      _ ≤ |mertensG (n + 1) - mertensG n| + |mertensG n - mertensG 2| := abs_add_le _ _
      _ ≤ _ := add_le_add hs ih
      _ = _ := by push_cast; ring

/-- The constant in Mertens' second theorem over the naturals. -/
noncomputable def mertens2NatConst : ℝ :=
  |mertensG 2| + (2 * mertens1Const + 1) / Real.log 2

theorem mertens1Const_nonneg : 0 ≤ mertens1Const := by
  have := primePowerConst_nonneg
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold mertens1Const; linarith

/-- **Mertens' second theorem** over the naturals: for `N ≥ 2`,
`|∑_{p ≤ N} 1 / p - log log N| ≤ mertens2NatConst`. -/
theorem abs_sum_inv_sub_log_log_le_nat (N : ℕ) (hN : 2 ≤ N) :
    |∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N)| ≤ mertens2NatConst := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
  have hlN0 : 0 < Real.log N := by linarith
  have hG := abs_mertensG_sub_le N hN
  have hR := abs_sum_log_div_sub_log_le_nat N
  have hC := mertens1Const_nonneg
  have e : ∑ p ∈ Nat.primesLE N, (1 : ℝ) / p - Real.log (Real.log N) =
      mertensG 2 + (mertensG N - mertensG 2) +
        ((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N := by
    rw [show mertensG 2 + (mertensG N - mertensG 2) = mertensG N by ring]
    unfold mertensG; ring
  rw [e]
  have h1 : |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| ≤
      mertens1Const / Real.log 2 := by
    rw [abs_div, abs_of_pos hlN0]
    calc _ ≤ mertens1Const / Real.log N := div_le_div_of_nonneg_right hR hlN0.le
      _ ≤ mertens1Const / Real.log 2 := div_le_div_of_nonneg_left hC hl2 hlN
  have h2 : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
      (mertens1Const + 1) / Real.log 2 := by
    have : 0 ≤ 1 / Real.log N := by positivity
    have : (mertens1Const + 1) * (1 / Real.log 2 - 1 / Real.log N) ≤
        (mertens1Const + 1) * (1 / Real.log 2) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    rw [div_eq_mul_one_div (mertens1Const + 1)]
    exact this
  have h3 : mertens2NatConst =
      |mertensG 2| + (mertens1Const + 1) / Real.log 2 + mertens1Const / Real.log 2 := by
    unfold mertens2NatConst; ring
  rw [h3]
  calc _ ≤ |mertensG 2 + (mertensG N - mertensG 2)| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := abs_add_le _ _
    _ ≤ |mertensG 2| + |mertensG N - mertensG 2| +
        |((∑ p ∈ Nat.primesLE N, Real.log p / p) - Real.log N) / Real.log N| := by
      gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

theorem log_log_floor_le (x : ℝ) (hx : 2 ≤ x) :
    Real.log (Real.log ⌊x⌋₊) ≤ Real.log (Real.log x) ∧
      Real.log (Real.log x) ≤ Real.log (Real.log ⌊x⌋₊) + 1 := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hN2r : (2 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN2
  have hlN : Real.log 2 ≤ Real.log ⌊x⌋₊ := Real.log_le_log (by norm_num) hN2r
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlN0 : 0 < Real.log ⌊x⌋₊ := by linarith
  obtain ⟨h1, h2⟩ := log_le_log_floor_add x (by linarith)
  have hlx : 0 < Real.log x := by linarith
  constructor
  · exact Real.log_le_log hlN0 h1
  · have hq := Real.log_le_sub_one_of_pos (div_pos hlx hlN0)
    rw [Real.log_div hlx.ne' hlN0.ne'] at hq
    have : Real.log x / Real.log ⌊x⌋₊ - 1 ≤ 1 := by
      rw [div_sub_one hlN0.ne', div_le_iff₀ hlN0]; linarith
    linarith

/-- The constant in Mertens' second theorem over the reals. -/
noncomputable def mertens2Const : ℝ := mertens2NatConst + 1

/-- **Mertens' second theorem.** For real `x ≥ 2`,
`|∑_{p ≤ x} 1 / p - log log x| ≤ mertens2Const`. -/
theorem abs_sum_inv_sub_log_log_le (x : ℝ) (hx : 2 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ mertens2Const := by
  have hN2 : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have h := abs_sum_inv_sub_log_log_le_nat ⌊x⌋₊ hN2
  obtain ⟨h1, h2⟩ := log_log_floor_le x hx
  unfold mertens2Const
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- **Mertens' second theorem**, existential form. -/
theorem mertens2 : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p - Real.log (Real.log x)| ≤ C :=
  ⟨mertens2Const, abs_sum_inv_sub_log_log_le⟩

end OMALib.Mertens

namespace BedertSieve
open Finset

/-- The reciprocal weights in the divisor sifting operator form a finite Euler product. -/
theorem primorial_divisor_sum (Q : ℕ) :
    ∑ d ∈ (primorial Q).divisors, (1:ℝ)/d =
    ∏ p ∈ Nat.primesLE Q, (1 + (1:ℝ)/p) := by
  classical
  let S := Nat.primesLE Q
  let D := (primorial Q).divisors
  have primes (T : Finset ℕ) (h : T ⊆ S) :
      (∏ p ∈ T, p).primeFactors = T :=
    Nat.primeFactors_prod (fun q hq => (Nat.mem_primesLE.mp (h hq)).2)
  have code (d : ℕ) (h : d ∈ D) : ∏ p ∈ d.primeFactors, p = d :=
    Nat.prod_primeFactors_of_squarefree
      (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp h).1 (squarefree_primorial Q))
  rw [Finset.prod_one_add]
  refine Finset.sum_bij' (fun d _ => d.primeFactors) (fun T _ => ∏ p ∈ T, p) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    apply Finset.mem_powerset.mpr
    rw [← primeFactors_primorial]
    exact Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 (primorial_ne_zero _)
  · intro T hT
    apply Nat.mem_divisors.mpr
    refine ⟨?_,primorial_ne_zero _⟩
    rw [primorial_eq_prod_primesLE]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp hT)
  · exact code
  · intro T hT
    exact primes T (Finset.mem_powerset.mp hT)
  · intro d hd
    simp only [one_div,Finset.prod_inv_distrib]
    rw [← Nat.cast_prod,code d hd]

/-- The loss of sifting all primes at most Q is logarithmic. -/
theorem primorial_divisor_bound : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q →
    ∑ d ∈ (primorial Q).divisors, (1:ℝ)/d ≤ C*Real.log Q := by
  obtain ⟨b,mer⟩ := OMALib.Mertens.mertens2
  refine ⟨Real.exp b,Real.exp_pos _,?_⟩
  intro Q hQ
  have hq : (2:ℝ) ≤ Q := by exact_mod_cast hQ
  have logpos : 0 < Real.log Q := Real.log_pos (by linarith)
  have h := (abs_le.mp (mer Q hq)).2
  rw [Nat.floor_natCast] at h
  rw [primorial_divisor_sum]
  calc
    _ ≤ ∏ p ∈ Nat.primesLE Q, Real.exp ((1:ℝ)/p) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _
      simpa only [add_comm] using Real.add_one_le_exp ((1:ℝ)/p)
    _ = Real.exp (∑ p ∈ Nat.primesLE Q, (1:ℝ)/p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (b+Real.log (Real.log Q)) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_add,Real.exp_log logpos]

end BedertSieve

end

section

namespace GreenOneTail
open Finset AddCircle MeasureTheory

/-- One-sided tail estimate for a nonnegative sequence bounded by the reciprocal square. -/
theorem natural_tail (Q : ℕ) (pos : 0 < Q) (a : ℕ → ℝ) (nonneg : ∀ i, 0 ≤ a i)
    (low : ∀ i ≤ Q, a i = 0) (cap : ∀ i, Q < i → a i ≤ ((i:ℝ)^2)⁻¹) :
    ∑' i, a i ≤ (Q:ℝ)⁻¹ := by
  classical
  apply Real.tsum_le_of_sum_le nonneg
  intro S
  let N := max Q (S.sup id)
  have sub : S.filter (fun i => Q < i) ⊆ Ioc Q N := by
    intro i hi
    obtain ⟨si,qi⟩ := mem_filter.mp hi
    exact mem_Ioc.mpr ⟨qi,(show i ≤ S.sup id from le_sup (f := id) si).trans (le_max_right _ _)⟩
  calc
    _ = ∑ i ∈ S.filter (fun i => Q < i), a i := by
      symm
      apply sum_subset (filter_subset _ S)
      intro i si ni
      exact low _ (le_of_not_gt (fun qi => ni (mem_filter.mpr ⟨si,qi⟩)))
    _ ≤ ∑ i ∈ S.filter (fun i => Q < i), ((i:ℝ)^2)⁻¹ :=
      sum_le_sum (fun i hi => cap _ (mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ Ioc Q N, ((i:ℝ)^2)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
    _ ≤ (Q:ℝ)⁻¹ - (N:ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub (Nat.ne_of_gt pos) (le_max_left _ _)
    _ ≤ _ := sub_le_self _ (by positivity)

/-- Two-sided Parseval tail on the standard circle with probability Haar measure. -/
theorem fourier_tail (Q : ℕ) (positive : 0 < Q) (h : UnitAddCircle → ℂ)
    (lp : MemLp h 2 haarAddCircle)
    (low : ∀ t : ℤ, t.natAbs ≤ Q → fourierCoeff h t = 0)
    (cap : ∀ t : ℤ, Q < t.natAbs → ‖fourierCoeff h t‖ ≤ 1/(t.natAbs:ℝ)) :
    (∫ x, ‖h x‖ ∂haarAddCircle) ≤ Real.sqrt (2/(Q:ℝ)) := by
  let μ : Measure UnitAddCircle := haarAddCircle
  let a (t : ℤ) := ‖fourierCoeff h t‖^2
  have small (t : ℤ) (ht : t.natAbs ≤ Q) : a t = 0 := by simp [a,low t ht]
  have bounded (t : ℤ) (ht : Q < t.natAbs) : a t ≤ ((t.natAbs:ℝ)^2)⁻¹ := by
    simpa only [a,one_div,inv_pow] using pow_le_pow_left₀ (norm_nonneg _) (cap t ht) 2
  have P := hasSum_sq_fourierCoeff (lp.toLp h)
  have co (t : ℤ) : fourierCoeff (lp.toLp h) t = fourierCoeff h t :=
    congrFun (fourierCoeff_congr_ae lp.coeFn_toLp) t
  have same : (∫ x, ‖lp.toLp h x‖^2 ∂μ) = ∫ x, ‖h x‖^2 ∂μ :=
    integral_congr_ae (lp.coeFn_toLp.mono fun x hx => congrArg (fun z : ℂ => ‖z‖^2) hx)
  have parseval : HasSum a (∫ x, ‖h x‖^2 ∂μ) := by
    rw [← same]
    simpa only [a,co] using P
  obtain ⟨plus,minus⟩ := summable_int_iff_summable_nat_and_neg.mp parseval.summable
  have pp := natural_tail Q positive (fun k : ℕ => a k) (fun _ => sq_nonneg _)
      (fun i hh => small _ (by simpa using hh)) (fun i hh => by simpa using bounded (i:ℤ) (by simpa using hh))
  have mm := natural_tail Q positive (fun k : ℕ => a (-k)) (fun _ => sq_nonneg _)
      (fun i hh => small _ (by simpa using hh)) (fun i hh => by simpa using bounded (-(i:ℤ)) (by simpa using hh))
  have v := tsum_nat_add_neg parseval.summable
  rw [small 0 (by simp),add_zero,parseval.tsum_eq,plus.tsum_add minus] at v
  have sq_bound : (∫ x, ‖h x‖^2 ∂μ) ≤ 2/(Q:ℝ) := by rw [←v,div_eq_mul_inv];linarith
  let M := ∫ x, ‖h x‖ ∂μ
  have normI : Integrable (fun x => ‖h x‖) μ := (lp.integrable (by norm_num)).norm
  have normSq : Integrable (fun x => ‖h x‖^2) μ := (memLp_two_iff_integrable_sq_norm lp.aestronglyMeasurable).mp lp
  have variance : 0 ≤ ∫ x, (‖h x‖-M)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  simp only [sub_sq] at variance
  have linear : Integrable (fun x : UnitAddCircle => 2*‖h x‖*M) μ := (normI.const_mul 2).mul_const M
  have diff : Integrable (fun x : UnitAddCircle => ‖h x‖^2 - 2*‖h x‖*M) μ := normSq.sub linear
  rw [integral_add diff (integrable_const (M^2)),
    integral_sub normSq linear, integral_mul_const, integral_const_mul,
    integral_const] at variance
  have simplified : 0 ≤ (∫ x, ‖h x‖^2 ∂μ) - 2*M*M + M^2 := by
    simpa only [μ,MeasureTheory.probReal_univ,one_smul,M] using variance
  have m_sq : M^2 ≤ ∫ x, ‖h x‖^2 ∂μ := by nlinarith
  exact Real.le_sqrt_of_sq_le (m_sq.trans sq_bound)

end GreenOneTail

end

section

namespace Green1Circle
open AddCircle MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Möbius inclusion-exclusion for the common divisors of two nonzero integers. -/
theorem moebius_common_divisors {M n : ℕ} (hM : M ≠ 0) :
    (∑ d ∈ M.divisors, if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0) =
      if M.Coprime n then 1 else 0 := by
  have gne : M.gcd n ≠ 0 := Nat.ne_of_gt (Nat.gcd_pos_of_pos_left n (Nat.pos_of_ne_zero hM))
  have eq : (M.divisors.filter fun d => d ∣ n) = (M.gcd n).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, hM, gne, ne_eq,
      not_false_eq_true, and_true, Nat.dvd_gcd_iff]
  rw [← Finset.sum_filter, eq]
  have inv := DFunLike.congr_fun ArithmeticFunction.moebius_mul_coe_zeta (M.gcd n)
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at inv
  change _ = if M.gcd n = 1 then 1 else 0
  split_ifs with heq
  · rw [if_pos heq] at inv
    exact_mod_cast inv
  · rw [if_neg heq] at inv
    exact_mod_cast inv

/-- The finite Möbius combination of dilates sifts a completely multiplicative
positive-frequency sequence down to indices coprime to M. -/
theorem fourierCoeff_moebius_sieve (h : UnitAddCircle → ℂ) (hh : Integrable h haarAddCircle)
    (w : ℕ →* ℂ) (C : ℂ) (coeff : ∀ n : ℕ, 0 < n → fourierCoeff h (n:ℤ) = C*w n)
    {M n : ℕ} (hM : M ≠ 0) (hn : 0 < n) :
    fourierCoeff (fun x : UnitAddCircle => ∑ d ∈ M.divisors,
        ((ArithmeticFunction.moebius d : ℂ) * w d) * h ((d:ℤ) • x)) (n:ℤ) =
      if M.Coprime n then C*w n else 0 := by
  let a (d : ℕ) := (ArithmeticFunction.moebius d : ℂ) * w d
  let g (d : ℕ) (x : UnitAddCircle) := h ((d:ℤ) • x)
  have nz (d : ℕ) (hd : d ∈ M.divisors) : (d:ℤ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have integ (d : ℕ) (hd : d ∈ M.divisors) : Integrable (g d) haarAddCircle :=
    ((Measure.measurePreserving_zsmul haarAddCircle (nz d hd)).integrable_comp hh.aestronglyMeasurable).mpr hh
  have eq := congrFun (fourierCoeff.sum M.divisors (fun d => a d • g d)
      (fun d hd => (integ d hd).smul (a d))) (n:ℤ)
  simp only [Finset.sum_apply, fourierCoeff.const_smul, smul_eq_mul] at eq
  calc
    _ = ∑ d ∈ M.divisors, a d * fourierCoeff (g d) (n:ℤ) := by
      convert eq using 2
      ext x
      simp [g,a]
    _ = ∑ d ∈ M.divisors, (if d ∣ n then (ArithmeticFunction.moebius d : ℂ) else 0)*(C*w n) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [show fourierCoeff (g d) (n:ℤ) = _ from fourierCoeff_dilate h hh (d:ℤ) (n:ℤ) (nz d hd)]
      simp only [Int.natCast_dvd_natCast]
      by_cases div : d ∣ n
      · have pos := Nat.div_pos (Nat.le_of_dvd hn div) (Nat.pos_of_mem_divisors hd)
        rw [if_pos div, if_pos div, ← Int.natCast_ediv, coeff _ pos]
        have wmul : w d * w (n/d) = w n := by rw [← map_mul, Nat.mul_div_cancel' div]
        dsimp [a]
        rw [← wmul]
        ring
      · simp [div]
    _ = _ := by
      rw [← Finset.sum_mul, moebius_common_divisors hM]
      split_ifs <;> simp

end Green1Circle

end

section

namespace Green1Circle
open AddCircle MeasureTheory ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The same sieve simultaneously at all positive, negative and zero indices.
The even Fourier sequence is recorded using the absolute frequency. -/
theorem fourierCoeff_sieve_signed (h : UnitAddCircle → ℂ) (hh : Integrable h haarAddCircle)
    (w : ℕ →* ℂ) (coeff : ∀ k : ℤ, fourierCoeff h k = w k.natAbs)
    {M : ℕ} (hM : M ≠ 0) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => ∑ d ∈ M.divisors,
        ((ArithmeticFunction.moebius d : ℂ) * w d) * h ((d:ℤ) • x)) k =
      if M.Coprime k.natAbs then w k.natAbs else 0 := by
  let a (d : ℕ) := (ArithmeticFunction.moebius d : ℂ) * w d
  let g (d : ℕ) (x : UnitAddCircle) := h ((d:ℤ) • x)
  have nz (d : ℕ) (hd : d ∈ M.divisors) : (d:ℤ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have integ (d : ℕ) (hd : d ∈ M.divisors) : Integrable (g d) haarAddCircle :=
    ((Measure.measurePreserving_zsmul haarAddCircle (nz d hd)).integrable_comp hh.aestronglyMeasurable).mpr hh
  have eq := congrFun (fourierCoeff.sum M.divisors (fun d => a d • g d)
      (fun d hd => (integ d hd).smul (a d))) k
  simp only [Finset.sum_apply, fourierCoeff.const_smul, smul_eq_mul] at eq
  calc
    _ = ∑ d ∈ M.divisors, a d * fourierCoeff (g d) k := by
      convert eq using 2
      ext x
      simp [g,a]
    _ = ∑ d ∈ M.divisors, (if d ∣ k.natAbs then (ArithmeticFunction.moebius d : ℂ) else 0)*(w k.natAbs) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [show fourierCoeff (g d) k = _ from fourierCoeff_dilate h hh (d:ℤ) k (nz d hd)]
      have equiv : ((d:ℤ) ∣ k) ↔ d ∣ k.natAbs := by
        rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      by_cases div : (d:ℤ) ∣ k
      · rw [if_pos div, if_pos (equiv.mp div), coeff, Int.natAbs_ediv_of_dvd div, Int.natAbs_natCast]
        dsimp [a]
        rw [mul_assoc, ← map_mul, Nat.mul_div_cancel' (equiv.mp div)]
      · simp [div, not_congr equiv |>.mp div]
    _ = _ := by
      rw [← Finset.sum_mul, moebius_common_divisors hM]
      split_ifs <;> simp

end Green1Circle

end

section

namespace GreenBourgain
open AddCircle MeasureTheory Set
open scoped Classical

def chi (k : ℤ) : ℝ := if k % 3 = 0 then 0 else if k % 3 = 1 then 1 else -1

lemma chi_mul (a b : ℤ) : chi (a*b) = chi a * chi b := by
  have ar : a%3 = 0 ∨ a%3 = 1 ∨ a%3 = 2 := by omega
  have br : b%3 = 0 ∨ b%3 = 1 ∨ b%3 = 2 := by omega
  rw [show chi (a*b) = (if (a%3*(b%3))%3=0 then 0 else if (a%3*(b%3))%3=1 then 1 else -1 : ℝ)
    from by simp only [chi, ← Int.mul_emod]]
  rcases ar with h|h|h <;> rcases br with j|j|j <;> norm_num [chi,h,j]

lemma chi_neg (k : ℤ) : chi (-k) = -chi k := by
  simpa only [neg_one_mul, show chi (-1) = -1 from by norm_num [chi]] using chi_mul (-1) k

/-- Normalized Bedert coefficient at a nonnegative index (zero at the origin). -/
noncomputable def weight : ℕ →* ℂ where
  toFun n := (chi (n:ℤ) : ℂ)/(n:ℂ)
  map_one' := by norm_num [chi]
  map_mul' a b := by
    push_cast
    rw [chi_mul, Complex.ofReal_mul, div_mul_div_comm]

def arc : Set UnitAddCircle := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3 : ℝ) (2/3)

noncomputable def base (x : UnitAddCircle) : ℂ :=
  (-(2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) *
    (arc.indicator (fun _ => (1 : ℂ)) x - 1/3)

lemma weight_bound (n : ℕ) : ‖weight n‖ ≤ 1/(n:ℝ) := by
  change ‖(chi (n:ℤ) : ℂ)/(n:ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold chi
  split_ifs <;> norm_num

lemma base_coeff (k : ℤ) : fourierCoeff base k = weight k.natAbs := by
  change fourierCoeff (fun x : UnitAddCircle =>
    (-(2 * Real.pi / Real.sqrt 3 : ℝ) : ℂ) *
    ((fun y : UnitAddCircle => arc.indicator (fun _ => (1:ℂ)) y - 1/3) x)) k = _
  rw [fourierCoeff.const_mul]
  have coeff := GreenArcFourier.centered_coeff k
  change fourierCoeff (fun x => arc.indicator (fun _ => (1:ℂ)) x - 1/3) k =
    -(Real.sqrt 3 : ℂ) * (chi k : ℂ) / (2*Real.pi*k) at coeff
  rw [coeff]
  change _ = (chi (k.natAbs:ℤ):ℂ) / (k.natAbs:ℂ)
  have cases := Int.natAbs_eq k
  generalize k.natAbs = m at cases ⊢
  obtain h|h := cases
  · subst k
    push_cast
    field_simp [Real.pi_ne_zero, show (Real.sqrt 3 : ℝ) ≠ 0 by positivity]
  · subst k
    rw [chi_neg]
    push_cast
    field_simp [Real.pi_ne_zero, show (Real.sqrt 3 : ℝ) ≠ 0 by positivity]

lemma base_memLp : MemLp base 2 haarAddCircle := by
  have meas : MeasurableSet arc := Green1Circle.middle_measure.1
  exact (((memLp_const (1:ℂ)).indicator meas).sub (memLp_const (1/3:ℂ))).const_mul _

end GreenBourgain

end

section

namespace GreenBourgain
open AddCircle MeasureTheory

noncomputable def sieve (Q : ℕ) (x : UnitAddCircle) : ℂ :=
  ∑ d ∈ (primorial Q).divisors, ((ArithmeticFunction.moebius d : ℂ) * weight d) * base ((d:ℤ) • x)

noncomputable def head (x : UnitAddCircle) : ℂ := fourier 1 x + fourier (-1) x
noncomputable def tail (Q : ℕ) (x : UnitAddCircle) : ℂ := sieve Q x - head x

lemma sieve_coeff (Q : ℕ) (k : ℤ) :
    fourierCoeff (sieve Q) k = if (primorial Q).Coprime k.natAbs then weight k.natAbs else 0 :=
  Green1Circle.fourierCoeff_sieve_signed base (base_memLp.integrable (by norm_num)) weight base_coeff
    (primorial_pos Q).ne' k

lemma sieve_memLp (Q : ℕ) : MemLp (sieve Q) 2 haarAddCircle := by
  apply memLp_finsetSum
  intro d hd
  have nz : (d:ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  exact (base_memLp.comp_measurePreserving (Measure.measurePreserving_zsmul haarAddCircle nz)).const_mul _

lemma mode_memLp (k : ℤ) : MemLp (fourier k : C(UnitAddCircle,ℂ)) 2 haarAddCircle :=
  (fourier k).memLp haarAddCircle (𝕜' := ℂ)

lemma head_memLp : MemLp head 2 haarAddCircle := (mode_memLp 1).add (mode_memLp (-1))

lemma tail_memLp (Q : ℕ) : MemLp (tail Q) 2 haarAddCircle := (sieve_memLp Q).sub head_memLp

lemma tail_coeff (Q : ℕ) (k : ℤ) :
    fourierCoeff (tail Q) k =
      (if (primorial Q).Coprime k.natAbs then weight k.natAbs else 0)
        - ((Pi.single (1:ℤ) 1 : ℤ → ℂ) k + (Pi.single (-1:ℤ) 1 : ℤ → ℂ) k) := by
  have add := congrFun (fourierCoeff.add ((mode_memLp 1).integrable (by norm_num))
    ((mode_memLp (-1)).integrable (by norm_num))) k
  change fourierCoeff head k = fourierCoeff (fourier 1 : C(UnitAddCircle,ℂ)) k +
    fourierCoeff (fourier (-1) : C(UnitAddCircle,ℂ)) k at add
  rw [fourierCoeff_fourier, fourierCoeff_fourier] at add
  have neg : fourierCoeff (-head) k = -fourierCoeff head k := by
    change fourierCoeff (fun x => -(head x)) k = _
    simpa using fourierCoeff.const_mul head (-1) k
  have sub := congrFun (fourierCoeff.add ((sieve_memLp Q).integrable (by norm_num))
    (head_memLp.neg.integrable (by norm_num))) k
  change fourierCoeff (fun x => sieve Q x + -(head x)) k = fourierCoeff (sieve Q) k +
    fourierCoeff (-head) k at sub
  change fourierCoeff (fun x => sieve Q x - head x) k = _
  simpa only [sub_eq_add_neg, sieve_coeff, neg, add] using sub

lemma rough_none {Q n : ℕ} (lo : 2 ≤ n) (hi : n ≤ Q) : ¬ (primorial Q).Coprime n := by
  intro cop
  have hp := Nat.minFac_prime (show n ≠ 1 by omega)
  have dv : n.minFac ∣ primorial Q := hp.dvd_primorial_iff.mpr ((Nat.minFac_le (show 0 < n by omega)).trans hi)
  exact hp.ne_one (Nat.dvd_one.mp (cop ▸ Nat.dvd_gcd dv (Nat.minFac_dvd n)))

lemma tail_low (Q : ℕ) (k : ℤ) (low : k.natAbs ≤ Q) : fourierCoeff (tail Q) k = 0 := by
  rw [tail_coeff]
  by_cases k0 : k = 0
  · subst k
    simp [weight,chi]
  by_cases k1 : k = 1
  · subst k
    simp
  by_cases km1 : k = -1
  · subst k
    simp
  have lo : 2 ≤ k.natAbs := by omega
  rw [if_neg (rough_none lo low)]
  simp [Pi.single_eq_of_ne k1, Pi.single_eq_of_ne km1]

lemma tail_high {Q : ℕ} (pos : 0 < Q) (k : ℤ) (high : Q < k.natAbs) :
    ‖fourierCoeff (tail Q) k‖ ≤ 1/(k.natAbs:ℝ) := by
  rw [tail_coeff, Pi.single_eq_of_ne (by omega : k ≠ 1), Pi.single_eq_of_ne (by omega : k ≠ -1),
    add_zero, sub_zero]
  split_ifs
  · exact weight_bound _
  · simp

end GreenBourgain

end

section

namespace GreenBourgain
open AddCircle MeasureTheory

noncomputable def mass (h : UnitAddCircle → ℂ) : ℝ := ∫ x, ‖h x‖ ∂haarAddCircle

lemma mass_nonnegative (h : UnitAddCircle → ℂ) : 0 ≤ mass h := integral_nonneg (fun _ => norm_nonneg _)

lemma mass_sum {ι : Type*} (B : Finset ι) (f : ι → UnitAddCircle → ℂ)
    (hi : ∀ b ∈ B, Integrable (f b) haarAddCircle) :
    mass (fun x => ∑ b ∈ B, f b x) ≤ ∑ b ∈ B, mass (f b) := by
  unfold mass
  rw [← integral_finsetSum B (fun b hb => (hi b hb).norm)]
  exact integral_mono (integrable_finsetSum B hi).norm
    (integrable_finsetSum B (fun b hb => (hi b hb).norm))
    (fun x => norm_sum_le _ _)

lemma mass_dilate (f : UnitAddCircle → ℂ) (hf : Integrable f haarAddCircle)
    (b : ℤ) (hb : b ≠ 0) : mass (fun x => f (b • x)) = mass f := by
  let μ : Measure UnitAddCircle := haarAddCircle
  have mp : MeasurePreserving (fun x : UnitAddCircle => b • x) μ μ :=
    Measure.measurePreserving_zsmul μ hb
  have meas : AEStronglyMeasurable (fun x => ‖f x‖) μ := hf.norm.aestronglyMeasurable
  exact (integral_map mp.measurable.aemeasurable (mp.map_eq.symm ▸ meas)).symm.trans
    (by rw [mp.map_eq])

lemma mass_const (f : UnitAddCircle → ℂ) (c : ℂ) : mass (fun x => c * f x) = ‖c‖ * mass f := by
  simp only [mass, norm_mul, integral_const_mul]

lemma weight_moebius_bound (d : ℕ) :
    ‖(ArithmeticFunction.moebius d : ℂ) * weight d‖ ≤ 1/(d:ℝ) := by
  rw [norm_mul, Complex.norm_intCast]
  have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
  exact (mul_le_mul_of_nonneg_right hmu (norm_nonneg _)).trans (by simpa using weight_bound d)

noncomputable def signal (B : Finset ℤ) (f : UnitAddCircle → ℂ) (x : UnitAddCircle) : ℂ :=
  ∑ b ∈ B, f (b • x)

lemma signal_int (B : Finset ℤ) (nonzero : ∀ b ∈ B, b ≠ 0)
    (f : UnitAddCircle → ℂ) (hi : Integrable f haarAddCircle) : Integrable (signal B f) haarAddCircle :=
  integrable_finsetSum B (fun b hb => ((Measure.measurePreserving_zsmul haarAddCircle
    (nonzero b hb)).integrable_comp hi.aestronglyMeasurable).mpr hi)

lemma mass_signal (B : Finset ℤ) (nonzero : ∀ b ∈ B, b ≠ 0) (f : UnitAddCircle → ℂ)
    (hi : Integrable f haarAddCircle) : mass (signal B f) ≤ B.card * mass f := by
  calc _ ≤ ∑ b ∈ B, mass (fun x => f (b • x)) :=
          mass_sum B _ (fun b hb => ((Measure.measurePreserving_zsmul haarAddCircle
            (nonzero b hb)).integrable_comp hi.aestronglyMeasurable).mpr hi)
       _ = ∑ _ ∈ B, mass f := Finset.sum_congr rfl (fun b hb => mass_dilate f hi b (nonzero b hb))
       _ = _ := by simp

lemma mass_sieve_signal (B : Finset ℤ) (nonzero : ∀ b ∈ B, b ≠ 0) (Q : ℕ) :
    mass (signal B (sieve Q)) ≤
      (∑ d ∈ (primorial Q).divisors, 1/(d:ℝ)) * mass (signal B base) := by
  let ds := (primorial Q).divisors
  let a (d : ℕ) := (ArithmeticFunction.moebius d : ℂ) * weight d
  let S := signal B base
  have sint := signal_int B nonzero base (base_memLp.integrable (by norm_num))
  have nz (d : ℕ) (hd : d ∈ ds) : (d:ℤ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have di (d : ℕ) (hd : d ∈ ds) : Integrable (fun x => S ((d:ℤ) • x)) haarAddCircle :=
    ((Measure.measurePreserving_zsmul haarAddCircle (nz d hd)).integrable_comp sint.aestronglyMeasurable).mpr sint
  have swapped : signal B (sieve Q) = fun x => ∑ d ∈ ds, a d * S ((d:ℤ) • x) := by
    funext x
    simp only [signal,sieve,ds,a,S,Finset.mul_sum,smul_smul]
    rw [Finset.sum_comm]
    congr! 5
    ring
  rw [swapped, Finset.sum_mul]
  calc _ ≤ ∑ d ∈ ds, mass (fun x => a d * S ((d:ℤ) • x)) := mass_sum ds _ (fun d hd => (di d hd).const_mul _)
       _ ≤ _ := by
         apply Finset.sum_le_sum
         intro d hd
         rw [mass_const, mass_dilate S sint _ (nz d hd)]
         exact mul_le_mul_of_nonneg_right (weight_moebius_bound _) (mass_nonnegative _)

end GreenBourgain

end

section

namespace GreenBourgain
open AddCircle MeasureTheory

lemma head_signal (B : Finset ℤ) (x : UnitAddCircle) :
    signal B head x = ∑ b ∈ B, (fourier b x + fourier (-b) x) := by
  simp only [signal,head,fourier_apply,smul_smul,one_mul,neg_one_mul]

lemma head_mass_ge_one (B : Finset ℤ) (hb : B.Nonempty) :
    1 ≤ mass (signal B head) := by
  obtain ⟨b, bin⟩ := hb
  let f (j : ℤ) (x : UnitAddCircle) := fourier j x + fourier (-j) x
  have hi (j : ℤ) : Integrable (f j) haarAddCircle :=
    ((mode_memLp j).add (mode_memLp (-j))).integrable (by norm_num)
  have cf (j : ℤ) : fourierCoeff (f j) b =
      (Pi.single j 1 : ℤ → ℂ) b + (Pi.single (-j) 1 : ℤ → ℂ) b := by
    have eq := congrFun (fourierCoeff.add ((mode_memLp j).integrable (by norm_num))
      ((mode_memLp (-j)).integrable (by norm_num))) b
    change fourierCoeff ((fourier j : C(UnitAddCircle,ℂ)) + (fourier (-j) : C(UnitAddCircle,ℂ)) : UnitAddCircle → ℂ) b = _
    simpa only [fourierCoeff_fourier, Pi.add_apply] using eq
  have cfB : fourierCoeff (signal B head) b =
      ∑ j ∈ B, ((if b=j then (1:ℝ) else 0)+(if b= -j then (1:ℝ) else 0) : ℝ) := by
    have eq := congrFun (fourierCoeff.sum B f (fun j _ => hi j)) b
    calc _ = fourierCoeff (∑ j ∈ B, f j) b := by
            congr 1
            funext x
            simp only [head_signal,Finset.sum_apply,f]
         _ = _ := by
            rw [eq]
            simp only [Finset.sum_apply,cf,Pi.single_apply,Complex.ofReal_sum,Complex.ofReal_add,
              apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero]
  have lower : (1:ℝ) ≤ ∑ j ∈ B, ((if b=j then (1:ℝ) else 0)+(if b= -j then (1:ℝ) else 0)) :=
    calc 1 ≤ (if b=b then (1:ℝ) else 0)+(if b= -b then (1:ℝ) else 0) := by simp only [if_true]; split_ifs <;> norm_num
         _ ≤ _ := Finset.single_le_sum (f := fun j => (if b=j then (1:ℝ) else 0)+(if b= -j then (1:ℝ) else 0))
           (fun j _ => by split_ifs <;> norm_num) bin
  have exactnorm : (1:ℝ) ≤ ‖fourierCoeff (signal B head) b‖ := by
    rw [cfB, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact lower
  apply exactnorm.trans
  unfold fourierCoeff mass
  simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using
    (norm_integral_le_integral_norm (μ := (haarAddCircle : Measure UnitAddCircle))
      (fun x => fourier (-b) x • signal B head x))

lemma head_mass_le (B : Finset ℤ) (nz : ∀ b ∈ B, b ≠ 0) (Q : ℕ) :
    mass (signal B head) ≤ mass (signal B (sieve Q)) + B.card * mass (tail Q) := by
  have si := signal_int B nz (sieve Q) ((sieve_memLp Q).integrable (by norm_num))
  have ti := signal_int B nz (tail Q) ((tail_memLp Q).integrable (by norm_num))
  have identity (x : UnitAddCircle) : signal B head x = signal B (sieve Q) x - signal B (tail Q) x := by
    simp only [signal,tail,Finset.sum_sub_distrib,sub_sub_cancel]
  calc
    _ ≤ ∫ x, (‖signal B (sieve Q) x‖ + ‖signal B (tail Q) x‖) ∂haarAddCircle :=
      integral_mono (signal_int B nz head (head_memLp.integrable (by norm_num))).norm (si.norm.add ti.norm)
        (fun x => by rw [identity]; exact norm_sub_le ..)
    _ = mass (signal B (sieve Q)) + mass (signal B (tail Q)) := integral_add si.norm ti.norm
    _ ≤ _ := add_le_add_right (mass_signal B nz _ ((tail_memLp Q).integrable (by norm_num))) _

end GreenBourgain

end

section

namespace GreenBourgain
open AddCircle MeasureTheory
open scoped Classical

/-- L¹ comparison between the first harmonics and the full middle-third signal
with a single logarithmic loss. The cutoff 8N² makes the rough tail at most 1/2. -/
theorem lift_normalized :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Finset ℤ, 2 ≤ B.card → (∀ b ∈ B, b ≠ 0) →
      mass (signal B head) ≤ C * Real.log B.card * mass (signal B base) := by
  obtain ⟨C,cp,loss⟩ := BedertSieve.primorial_divisor_bound
  refine ⟨10*C, by positivity, ?_⟩
  intro B big nz
  let N : ℕ := B.card
  let Q : ℕ := 8*N^2
  have hn : 2 ≤ N := big
  have hnR : (2:ℝ) ≤ N := by exact_mod_cast hn
  have npos : (0:ℝ) < N := by linarith
  have hQ : 2 ≤ Q := by dsimp [Q]; nlinarith
  have split := head_mass_le B nz Q
  have sieve := mass_sieve_signal B nz Q
  have tailbd := GreenOneTail.fourier_tail Q (by omega) (tail Q) (tail_memLp Q)
    (tail_low Q) (tail_high (by omega))
  change mass (tail Q) ≤ _ at tailbd
  have sqrtQ : Real.sqrt (2/(Q:ℝ)) = 1/(2*N) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    dsimp [Q]
    push_cast
    field_simp
    ring
  have half : (N:ℝ)*mass (tail Q) ≤ 1/2 := by
    rw [sqrtQ] at tailbd
    calc _ ≤ (N:ℝ)*(1/(2*N)) := mul_le_mul_of_nonneg_left tailbd npos.le
         _ = _ := by field_simp
  have lg : Real.log (Q:ℝ) ≤ 5*Real.log N := by
    change Real.log ((8 * N^2 : ℕ):ℝ) ≤ _
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
       (show (8:ℝ) = 2^3 by norm_num), Real.log_pow]
    have := Real.log_le_log (by norm_num : (0:ℝ)<2) hnR
    norm_num
    linarith
  have bound := (loss Q hQ).trans (mul_le_mul_of_nonneg_left lg cp.le)
  have hnorm := (sieve.trans (mul_le_mul_of_nonneg_right bound (mass_nonnegative _)))
  have nonempty : B.Nonempty := Finset.card_pos.mp (by omega)
  have floor := head_mass_ge_one B nonempty
  change mass (signal B head) ≤ mass (signal B (GreenBourgain.sieve Q)) + (N:ℝ)*mass (tail Q) at split
  change mass (signal B head) ≤ _ * Real.log (N:ℝ) * _ 
  linarith

/-- Normalization of the first harmonic. -/
theorem head_cosine (B : Finset ℤ) :
    mass (signal B head) = 2 * ∫ x : UnitAddCircle, |∑ b ∈ B, (fourier b x).re| ∂haarAddCircle := by
  have eq (x : UnitAddCircle) : signal B head x = ((2 * ∑ b ∈ B, (fourier b x).re : ℝ):ℂ) := by
    rw [head_signal, Finset.mul_sum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [fourier_neg, Complex.add_conj]
  unfold mass
  simp_rw [eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  rw [integral_const_mul]

/-- Comparison with the unscaled real centered middle-third indicator. -/
theorem base_discrepancy (B : Finset ℤ) :
    mass (signal B base) = (2 * Real.pi / Real.sqrt 3) *
      ∫ x : UnitAddCircle, |∑ b ∈ B, ((if b • x ∈ arc then (1:ℝ) else 0)-1/3)| := by
  classical
  let c : ℝ := -(2 * Real.pi / Real.sqrt 3)
  have eq (x : UnitAddCircle) : signal B base x =
      ((c * ∑ b ∈ B, ((if b • x ∈ arc then (1:ℝ) else 0)-1/3) : ℝ):ℂ) := by
    simp only [signal, base, Complex.ofReal_mul, Complex.ofReal_sum, ← Finset.mul_sum]
    dsimp only [c]
    rw [Complex.ofReal_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    by_cases hx : b • x ∈ arc <;> simp [Set.indicator, hx]
  have svol : (volume : Measure UnitAddCircle) = haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
  rw [svol]
  unfold mass
  simp_rw [eq, Complex.norm_real, Real.norm_eq_abs, abs_mul, integral_const_mul]
  rw [show |c|=2*Real.pi/Real.sqrt 3 from by dsimp [c]; rw [abs_neg, abs_of_nonneg (by positivity)]]

/-- Bourgain's logarithmic lifting inequality, Bedert Proposition 4.2. -/
theorem bourgain_lift :
    ∃ C : ℝ, 0 < C ∧ ∀ B : Finset ℤ, 2 ≤ B.card → (∀ b ∈ B, b ≠ 0) →
      (∫ x : UnitAddCircle, |∑ b ∈ B, (fourier b x).re| ∂haarAddCircle) ≤
      C * Real.log B.card * (∫ x : UnitAddCircle, |∑ b ∈ B,
        ((if b • x ∈ ((↑) : ℝ → UnitAddCircle) '' Set.Ioo (1/3 : ℝ) (2/3) then (1:ℝ) else 0)-1/3)|) := by
  obtain ⟨C,cp,cmp⟩ := lift_normalized
  refine ⟨C*(Real.pi/Real.sqrt 3), by positivity, ?_⟩
  intro B big nz
  have h := cmp B big nz
  rw [head_cosine,base_discrepancy] at h
  change _ ≤ C * (Real.pi / Real.sqrt 3) * Real.log ↑B.card *
    (∫ x : UnitAddCircle, |∑ b ∈ B, ((if b • x ∈ arc then (1:ℝ) else 0)-1/3)|)
  apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<2)).mp
  convert h using 1 <;> first | rfl | ring

end GreenBourgain

end

section

section

open MeasureTheory Finset
open scoped ComplexConjugate

namespace GreenRudin

/-- The product of circle exponentials is the exponential at the sum of frequencies. -/
theorem prod_fourier (s : Finset ℤ) (f : ℤ → ℤ) (x : UnitAddCircle) :
    (∏ i∈s, fourier (f i) x) = fourier (∑ i∈s, f i) x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [prod_insert hi,sum_insert hi,ih,fourier_add]

/-- Every nonempty signed product supported on dissociated frequencies has zero
mean. Complex amplitudes allow arbitrary phases in the Riesz product. -/
theorem mixed_mean (D : Finset ℤ) (diss : AddDissociated (D : Set ℤ)) (ne : D.Nonempty)
    (u v : ℤ → ℂ) :
    (∫ x : UnitAddCircle, ∏ d∈D, (u d*fourier d x + v d*fourier (-d) x)
      ∂AddCircle.haarAddCircle) = 0 := by
  classical
  let f (s : Finset ℤ) := (∑ d∈s,d) - ∑ d∈D\s,d
  let c (s : Finset ℤ) := (∏ d∈s,u d)*(∏ d∈D\s,v d)
  have rep (x : UnitAddCircle) :
      (∏ d∈D, (u d*fourier d x + v d*fourier (-d) x)) =
      ∑ s∈D.powerset, c s * fourier (f s) x := by
    rw [Finset.prod_add]
    refine sum_congr rfl fun s _ => ?_
    simp only [prod_mul_distrib,prod_fourier,Finset.sum_neg_distrib (fun d : ℤ => d),c,f,sub_eq_add_neg,fourier_add]
    ring
  simp_rw [rep]
  rw [integral_finsetSum]
  · refine sum_eq_zero fun s hs => ?_
    have hin := mem_powerset.mp hs
    have nf : f s ≠ 0 := by
      intro h
      have eql : s=D\s := diss (coe_subset.mpr hin) (coe_subset.mpr sdiff_subset)
        (sub_eq_zero.mp h)
      obtain ⟨d,hd⟩ := ne
      by_cases hds : d∈s
      · exact (mem_sdiff.mp (eql ▸ hds)).2 hds
      · exact hds (eql.symm ▸ mem_sdiff.mpr ⟨hd,hds⟩)
    rw [integral_const_mul,integral_eq_zero_of_add_right_eq_neg
      (fourier_add_half_inv_index nf (by norm_num : 0 < (1:ℝ))),mul_zero]
  · intro s _
    exact (continuous_const.mul (fourier (f s)).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Distinct dissociated frequencies give exactly the constant coefficient
after averaging a product of real parts of circle characters. -/
theorem riesz_mean (D : Finset ℤ) (diss : AddDissociated (D : Set ℤ)) (a : ℤ → ℝ) (z : ℤ → ℂ) :
    (∫ x : UnitAddCircle, ∏ d∈D, ((z d * fourier d x).re + a d)
      ∂AddCircle.haarAddCircle) = ∏ d∈D,a d := by
  classical
  have van (s : Finset ℤ) (hs : s⊆D) (ne : s.Nonempty) :
      (∫ x : UnitAddCircle, ∏ d∈s, (z d * fourier d x).re ∂AddCircle.haarAddCircle)=0 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal,Complex.ofReal_zero]
    simp only [Complex.ofReal_prod,Complex.re_eq_add_conj,map_mul,←fourier_neg]
    convert mixed_mean s (diss.subset (coe_subset.mpr hs)) ne (fun d => z d/2)
      (fun d => conj (z d)/2) using 1
    apply integral_congr_ae
    filter_upwards with x
    exact prod_congr rfl fun d _ => by ring
  simp_rw [Finset.prod_add]
  rw [integral_finsetSum]
  · rw [Finset.sum_eq_single ∅]
    · simp
    · intro s hs hn
      rw [integral_mul_const,van s (mem_powerset.mp hs) (nonempty_iff_ne_empty.mpr hn),zero_mul]
    · simp
  · intro s _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact (continuous_finsetProd _ fun d _ =>
      Complex.continuous_re.comp (continuous_const.mul (fourier d).continuous)).mul continuous_const

end GreenRudin

end

section

open MeasureTheory Finset

namespace GreenRudin

/-- The chord of the exponential between −r and r majorizes it on their interval. -/
theorem exp_chord (r y : ℝ) (hy : |y| ≤ 1) :
    Real.exp (r*y) ≤ Real.sinh r*y+Real.cosh r := by
  obtain ⟨lo,hi⟩ := abs_le.mp hy
  have h := convexOn_exp.2 (Set.mem_univ r) (Set.mem_univ (-r))
    (show 0≤(1+y)/2 by linarith) (show 0≤(1-y)/2 by linarith)
    (show (1+y)/2+(1-y)/2=1 by ring)
  simp only [smul_eq_mul] at h
  rwa [show (1+y)/2*r+(1-y)/2*(-r)=r*y by ring,
    show (1+y)/2*Real.exp r+(1-y)/2*Real.exp (-r)=Real.sinh r*y+Real.cosh r by
      rw [Real.cosh_eq,Real.sinh_eq]; ring] at h

/-- A dissociated exponential sum is subgaussian in every real projection,
with variance proxy equal to the sum of the squares of its weights. -/
theorem mgf_weighted (D : Finset ℤ) (hD : AddDissociated (D : Set ℤ))
    (w : ℤ → ℝ) (z : ℤ → ℂ) (phase : ∀ d∈D, ‖z d‖ ≤ 1) (r : ℝ) :
    (∫ x : UnitAddCircle, Real.exp (r*∑ d∈D,w d*(z d*fourier d x).re)
      ∂AddCircle.haarAddCircle) ≤ Real.exp ((∑ d∈D,(w d)^2)*r^2/2) := by
  classical
  let c (d : ℤ) := Real.cosh (r*w d)
  let v (d : ℤ) := (Real.sinh (r*w d):ℂ)*z d
  have yn (d : ℤ) (hd : d∈D) (x : UnitAddCircle) : |(z d*fourier d x).re|≤1 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul,show ‖fourier d x‖=1 from Circle.norm_coe _,mul_one]
    exact phase d hd
  have point (x : UnitAddCircle) : Real.exp (r*∑ d∈D,w d*(z d*fourier d x).re) ≤
      ∏ d∈D,((v d*fourier d x).re+c d) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod (fun d _ => (Real.exp_pos _).le)
    intro d hd
    simpa only [← mul_assoc r, v, c, mul_assoc (Real.sinh (r*w d):ℂ),Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using
      exp_chord (r*w d) (z d*fourier d x).re (yn d hd x)
  calc
    _ ≤ (∫ x : UnitAddCircle, ∏ d∈D,((v d*fourier d x).re+c d) ∂AddCircle.haarAddCircle) := by
      apply integral_mono _ _ point
      · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        exact Real.continuous_exp.comp (continuous_const.mul (continuous_finsetSum _ fun d _ =>
          continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul (fourier d).continuous))))
      · apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
        exact continuous_finsetProd _ fun d _ =>
          (Complex.continuous_re.comp (continuous_const.mul (fourier d).continuous)).add continuous_const
    _ = ∏ d∈D, c d := riesz_mean D hD c v
    _ ≤ ∏ d∈D, Real.exp ((r*w d)^2/2) := by
      exact Finset.prod_le_prod (fun d _ => (Real.cosh_pos _).le) (fun d _ => Real.cosh_le_exp_half_sq _)
    _ = _ := by
      rw [←Real.exp_sum]
      congr 1
      rw [←Finset.sum_div,Finset.sum_mul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring

theorem mgf (D : Finset ℤ) (hD : AddDissociated (D : Set ℤ)) (r : ℝ) :
    (∫ x : UnitAddCircle, Real.exp (r*(∑ d∈D,(fourier d x).re)) ∂AddCircle.haarAddCircle) ≤
    Real.exp ((D.card:ℝ)*r^2/2) := by
  simpa [Finset.sum_const] using mgf_weighted D hD (fun _ => 1) (fun _ => 1) (by simp) r

end GreenRudin

end

section

open MeasureTheory
namespace GreenBedert

theorem young_entropy {u B : ℝ} (hu : 0 ≤ u) (bound : u ≤ B) (y : ℝ) :
    u*y ≤ u*Real.log B-u+Real.exp y := by
  rcases eq_or_lt_of_le hu with e | hp
  · simp [←e,(Real.exp_pos _).le]
  have h := Real.add_one_le_exp (y-Real.log u)
  rw [Real.exp_sub,Real.exp_log hp,le_div_iff₀ hp] at h
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log hp bound) hu
  linarith

/-- The entropy bound in a compact probability space follows from scalar
Young duality without any differentiability of the density. -/
theorem entropy_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (w y : X → ℝ) (B M : ℝ) (iw : Integrable w μ) (iwy : Integrable (fun x => w x*y x) μ)
    (ie : Integrable (fun x => Real.exp (y x)) μ)
    (density : (∫ x, w x ∂μ)=1) (bounds : ∀ x, 0 ≤ w x ∧ w x ≤ B)
    (mgf : (∫x, Real.exp (y x) ∂μ)≤ Real.exp M) :
    (∫x, w x*y x ∂μ) ≤ Real.log B + M := by
  have each (x) : w x*y x ≤ (Real.log B+M-1)*w x + Real.exp (-M)*Real.exp (y x) := by
    have h := young_entropy (bounds x).1 (bounds x).2 (y x-M)
    rw [sub_eq_add_neg,Real.exp_add] at h
    linarith
  have main := integral_mono iwy ((iw.const_mul _).add (ie.const_mul _)) each
  change _ ≤ (∫ x, (Real.log B+M-1)*w x + Real.exp (-M)*Real.exp (y x) ∂μ) at main
  rw [integral_add (iw.const_mul _) (ie.const_mul _),integral_const_mul,integral_const_mul,density,mul_one] at main
  have hx := mul_le_mul_of_nonneg_left mgf (Real.exp_pos (-M)).le
  rw [←Real.exp_add,neg_add_cancel,Real.exp_zero] at hx
  linarith

/-- A subgaussian dissociated sum with large correlation forces an L¹ norm
lower bound. Here d is the variance proxy and also the correlation lower bound. -/
theorem entropy_correlation (F T : UnitAddCircle → ℝ) (cF : Continuous F) (cT : Continuous T)
    (N d : ℝ) (bnd : ∀ x, |F x| ≤ N)
    (cor : d ≤ ∫ x, F x*T x ∂AddCircle.haarAddCircle)
    (mgf : ∀ r : ℝ, (∫ x, Real.exp (r*T x) ∂AddCircle.haarAddCircle) ≤ Real.exp (d*r^2/2))
    (positive : 0 < ∫ x, |F x| ∂AddCircle.haarAddCircle) :
    let L := ∫ x, |F x| ∂AddCircle.haarAddCircle
    d ≤ 2*L^2*Real.log (2*N/L) := by
  intro L
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let r := L⁻¹
  have lp : 0 < L := positive
  have rp : 0 < r := inv_pos.mpr lp
  have NL : L ≤ N := by
    have hh := integral_mono (μ:=μ) (cF.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (integrable_const N) bnd
    simpa [Measure.real,μ] using hh
  have np : 0 < N := lp.trans_le NL
  let w (x : UnitAddCircle) := r*|F x|
  let y (x : UnitAddCircle) := r*|T x|
  have cw : Continuous w := continuous_const.mul cF.abs
  have cy : Continuous y := continuous_const.mul cT.abs
  have int (g : UnitAddCircle → ℝ) (hg : Continuous g) : Integrable g μ := hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have mass : (∫x,w x ∂μ)=1 := by
    change (∫x,r*|F x| ∂μ)=1
    rw [integral_const_mul]; exact inv_mul_cancel₀ lp.ne'
  have bounds (x) : 0 ≤ w x ∧ w x ≤ r*N :=
    ⟨mul_nonneg rp.le (abs_nonneg _),mul_le_mul_of_nonneg_left (bnd x) rp.le⟩
  let t := d*r^2/2
  have both : (∫x, Real.exp (y x) ∂μ) ≤ Real.exp (Real.log 2+t) := by
    have neg (x) : Real.exp (y x) ≤ Real.exp (r*T x)+Real.exp ((-r)*T x) := by
      by_cases h : 0 ≤ T x
      · simp [y, abs_of_nonneg h, (Real.exp_pos _).le]
      · rw [show y x=(-r)*T x by simp [y,abs_of_nonpos (le_of_not_ge h)]]
        linarith [Real.exp_pos (r*T x)]
    have h1 : Integrable (fun x => Real.exp (r*T x)) μ := int _ ((continuous_const.mul cT).rexp : Continuous (fun x => Real.exp (r*T x)))
    have h2 : Integrable (fun x => Real.exp ((-r)*T x)) μ := int _ ((continuous_const.mul cT).rexp : Continuous (fun x => Real.exp ((-r)*T x)))
    have hi := integral_mono (int _ cy.rexp) (h1.add h2) neg
    change _ ≤ (∫x,Real.exp (r*T x)+Real.exp ((-r)*T x) ∂μ) at hi
    rw [integral_add h1 h2] at hi
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2)]
    have negmgf := mgf (-r)
    rw [neg_sq] at negmgf
    dsimp only [μ] at hi
    dsimp only [t,μ]; linarith [mgf r]
  have ent := entropy_bound μ w y (r*N) (Real.log 2+t) (int _ cw) (int _ (cw.mul cy)) (int _ cy.rexp) mass bounds both
  have abs_c : d ≤ ∫x, |F x| * |T x| ∂μ := cor.trans (integral_mono (int _ (cF.mul cT)) (int _ (cF.abs.mul cT.abs))
    (fun x => by simpa [abs_mul] using le_abs_self (F x*T x)))
  have eq : (∫ x, w x*y x ∂μ) = r^2*(∫x, |F x| * |T x| ∂μ) := by
    rw [←integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by dsimp [w,y]; ring))
  rw [eq] at ent
  have hlog : Real.log (2*N/L) = Real.log 2+Real.log (r*N) := by
    rw [← Real.log_mul (by norm_num) (mul_pos rp np).ne']; congr 1; dsimp [r]; ring
  rw [hlog]
  have r2 : L^2*r^2=1 := by dsimp [r]; field_simp
  have h := (mul_le_mul_of_nonneg_left abs_c (sq_nonneg r)).trans ent
  dsimp only [t] at h
  have last := mul_le_mul_of_nonneg_left h (sq_nonneg L)
  have hhalf : d ≤ L^2*(Real.log 2+Real.log (r*N))+d/2 := by
    calc d = L^2*(r^2*d) := by rw [←mul_assoc,r2,one_mul]
         _ ≤ _ := last
         _ = _ := by linear_combination d/2*r2
  linarith

end GreenBedert

end

section

open MeasureTheory
open scoped ComplexConjugate
namespace GreenBedert

theorem character_real_mean (k : ℤ) :
    (∫x : UnitAddCircle, (fourier k x).re ∂AddCircle.haarAddCircle) = if k=0 then 1 else 0 := by
  split_ifs with h
  · simp [h]
  · have hi : Integrable (fourier k : UnitAddCircle → ℂ) AddCircle.haarAddCircle :=
      (fourier k).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [show (∫x : UnitAddCircle, (fourier k x).re ∂AddCircle.haarAddCircle) =
        (∫x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle).re from integral_re hi]
    rw [integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index h (by norm_num : 0 < (1:ℝ)))]
    rfl

theorem cos_pair (a d : ℤ) :
    (∫ x : UnitAddCircle, (2*(fourier a x).re)*(fourier d x).re ∂AddCircle.haarAddCircle) =
      (if a=d then (1:ℝ) else 0)+(if a = -d then 1 else 0) := by
  have int (n : ℤ) : Integrable (fun x : UnitAddCircle => (fourier n x).re) AddCircle.haarAddCircle :=
    (Complex.continuous_re.comp (fourier n).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have formula (x : UnitAddCircle) : 2*(fourier a x).re*(fourier d x).re =
      (fourier (a-d) x).re+(fourier (a+d) x).re := by
    rw [sub_eq_add_neg,fourier_add,fourier_add,fourier_neg]
    simp [Complex.mul_re]; ring
  simp_rw [formula]
  rw [integral_add (int _) (int _),character_real_mean,character_real_mean]
  simp only [sub_eq_zero,add_eq_zero_iff_eq_neg]

theorem dissociated_cosine_L1 (A D : Finset ℤ) (sub : D ⊆ A)
    (diss : AddDissociated (D : Set ℤ)) :
    (D.card:ℝ) ≤ 8*(∫x : UnitAddCircle, |∑ a∈A,(fourier a x).re| ∂AddCircle.haarAddCircle)^2 *
      Real.log (4*(A.card:ℝ)) := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let f (x : UnitAddCircle) := ∑ a∈A,(fourier a x).re
  let F (x : UnitAddCircle) := ∑ a∈A,2*(fourier a x).re
  let T (x : UnitAddCircle) := ∑ d∈D,(fourier d x).re
  have cont (a : ℤ) : Continuous (fun x : UnitAddCircle => (fourier a x).re) :=
    Complex.continuous_re.comp (fourier a).continuous
  have cf : Continuous F := continuous_finsetSum _ (fun a _ => continuous_const.mul (cont a))
  have ct : Continuous T := continuous_finsetSum _ (fun d _ => cont d)
  have int (g : UnitAddCircle → ℝ) (hg : Continuous g) : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have pair (a d : ℤ) : Integrable (fun x : UnitAddCircle => (2*(fourier a x).re)*(fourier d x).re) μ := int _ ((continuous_const.mul (cont a)).mul (cont d) :
    Continuous (fun x : UnitAddCircle => (2*(fourier a x).re)*(fourier d x).re))
  have cor : (D.card:ℝ) ≤ ∫x,F x*T x ∂μ := by
    have split (x) : F x*T x = ∑ d∈D, ∑ a∈A, (2*(fourier a x).re)*(fourier d x).re := by
      simp [F,T,Finset.mul_sum,Finset.sum_mul]
    simp_rw [split]
    rw [integral_finsetSum D (fun d _ => integrable_finsetSum A (fun a _ => pair a d))]
    simp_rw [integral_finsetSum A (fun a _ => pair a _)]
    change _ ≤ ∑ d∈D, ∑ a∈A, ∫x : UnitAddCircle,(2*(fourier a x).re)*(fourier d x).re ∂AddCircle.haarAddCircle
    simp_rw [cos_pair, Finset.sum_add_distrib]
    calc (D.card:ℝ) = ∑ _d∈D,(1:ℝ) := by simp
         _ ≤ _ := by
           rw [←Finset.sum_add_distrib]
           apply Finset.sum_le_sum
           intro d hd
           have hs : (∑ a∈A, if a=d then (1:ℝ) else 0) = 1 := by simp [sub hd]
           rw [hs]
           exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by positivity))
  have point (a : ℤ) (x : UnitAddCircle) : |(fourier a x).re| ≤ 1 := by
    exact (Complex.abs_re_le_norm _).trans_eq (by rw [fourier_apply,Circle.norm_coe])
  have bound (S : Finset ℤ) (x : UnitAddCircle) : |∑ a∈S, (fourier a x).re| ≤ S.card := by
    calc _ ≤ ∑ a∈S, |(fourier a x).re| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _a∈S,(1:ℝ) := Finset.sum_le_sum (fun a _ => point a x)
         _ = _ := by simp
  have double (x) : F x = 2*f x := (Finset.mul_sum ..).symm
  have bdF (x) : |F x| ≤ 2*(A.card:ℝ) := by
    rw [double,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
    exact mul_le_mul_of_nonneg_left (bound A x) (by norm_num)
  let L := ∫ x, |F x| ∂μ
  by_cases dne : D.Nonempty
  · have dpos : 0<(D.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr dne
    have hlow : (D.card:ℝ) ≤ D.card*L := by
      rw [show (D.card:ℝ)*L=∫x, (D.card:ℝ)*|F x| ∂μ by rw [integral_const_mul]]
      exact cor.trans (integral_mono (int _ (cf.mul ct)) (int _ (continuous_const.mul cf.abs)) (fun x => by
        calc F x*T x ≤ |F x*T x| := le_abs_self _
             _ = |T x| * |F x| := by rw [abs_mul,mul_comm]
             _ ≤ _ := mul_le_mul_of_nonneg_right (bound D x) (abs_nonneg _)))
    have oneL : 1 ≤ L := (le_of_mul_le_mul_left (by simpa using hlow : (D.card:ℝ)*1 ≤ D.card*L) dpos)
    have ent := entropy_correlation F T cf ct (2*A.card) D.card bdF cor (GreenRudin.mgf D diss) (zero_lt_one.trans_le oneL)
    change (D.card:ℝ) ≤ 2*L^2*Real.log _ at ent
    have apos : 0<(A.card:ℝ) := by exact_mod_cast Finset.card_pos.mpr (dne.mono sub)
    have hlog : Real.log (2*(2*(A.card:ℝ))/L) ≤ Real.log (4*(A.card:ℝ)) := by
      apply Real.log_le_log (by positivity)
      rw [div_le_iff₀ (zero_lt_one.trans_le oneL)]
      nlinarith [mul_nonneg apos.le (sub_nonneg.mpr oneL)]
    have dL : L = 2*∫x, |f x| ∂μ := by
      dsimp only [L]
      simp_rw [double,abs_mul,abs_of_pos (by norm_num : 0<(2:ℝ))]
      rw [integral_const_mul]
    calc _ ≤ 2*L^2*Real.log (4*(A.card:ℝ)) := ent.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
         _ = _ := by rw [dL]; ring
  · rw [Finset.not_nonempty_iff_eq_empty.mp dne]; simp only [Finset.card_empty,Nat.cast_zero]
    by_cases ha : A.Nonempty
    · have ap : (1:ℝ) ≤ A.card := by exact_mod_cast Finset.card_pos.mpr ha
      exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    · simp [Finset.not_nonempty_iff_eq_empty.mp ha]

end GreenBedert

end

section

open MeasureTheory Filter Set
open scoped Real BigOperators Classical

namespace GreenBedert

/-- A dimension threshold of log⁴ dominates the log³ loss in the squared
discrepancy estimate for every fixed surplus. -/
theorem eventual_high_conversion (C : ℝ) (pC : 0 < C) (j : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (d : ℕ) (L U : ℝ), 0 ≤ U →
      ⌈(Real.log (n:ℝ))^4⌉₊ < d →
      (d:ℝ) ≤ 8*U^2*Real.log (4*(n:ℝ)) →
      U ≤ C*Real.log (n:ℝ)*(1+L) → 2*(j:ℝ) < L := by
  have toInf : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [toInf.eventually_ge_atTop (16*C^2*(1+2*(j:ℝ))^2),
    toInf.eventually_ge_atTop (Real.log 4),eventually_ge_atTop (2:ℕ)] with n large logn n2
  intro d L U nonneg thresh ent upper
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  let t := Real.log (n:ℝ)
  have tp : 0 < t := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have cut : t^4 < (d:ℝ) := (Nat.le_ceil (t^4)).trans_lt (by exact_mod_cast thresh)
  by_contra! fail
  have up : U ≤ C*t*(1+2*(j:ℝ)) := upper.trans (mul_le_mul_of_nonneg_left (by linarith) (mul_pos pC tp).le)
  have ln : Real.log (4*(n:ℝ)) ≤ 2*t := by
    rw [Real.log_mul (by norm_num) np.ne']; dsimp [t]; linarith
  have contra : (d:ℝ) ≤ t^4 := calc
    _ ≤ 8*U^2*Real.log (4*(n:ℝ)) := ent
    _ ≤ 8*U^2*(2*t) := mul_le_mul_of_nonneg_left ln (by positivity)
    _ ≤ 8*(C*t*(1+2*(j:ℝ)))^2*(2*t) := by gcongr
    _ = (16*C^2*(1+2*(j:ℝ))^2)*t^3 := by ring
    _ ≤ t*t^3 := mul_le_mul_of_nonneg_right large (by positivity)
    _ = t^4 := by ring
  exact cut.not_ge contra

/-- The high-dimensional child follows from the logarithmic cost of extracting
the first cosine block of the middle-third indicator. -/
theorem high_child_of_cosine_bound
    (comparison : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ B : Finset ℤ, 0∉B → B.card=n → (∀ b∈B,-b∉B) →
      let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3:ℝ) (2/3)
      (∫ x : UnitAddCircle, |∑ b∈B, (fourier b x).re| ∂AddCircle.haarAddCircle) ≤ C*Real.log (n:ℝ) *
        (1 + ∫x : UnitAddCircle, |∑ b∈B, ((if b•x∈I then (1:ℝ) else 0)-1/3)|)) :
    OMA.R_Green1_green_1_R1.H1 := by
  obtain ⟨C,pC,bound⟩ := comparison
  intro j
  filter_upwards [bound,eventual_high_conversion C pC j] with n up grow
  intro B nz card antisign k
  rintro ⟨D,sub,diss,lower⟩
  let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3:ℝ) (2/3)
  let F := fun x : UnitAddCircle => ∑ b∈B, ((if b•x∈I then (1:ℝ) else 0)-1/3)
  let U := ∫x : UnitAddCircle, |∑ b∈B, (fourier b x).re| ∂AddCircle.haarAddCircle
  have bne : ∀ b∈B, b≠0 := fun b hb eq => nz (eq ▸ hb)
  have hi : Integrable F := by
    apply integrable_finsetSum B
    intro b hb
    have set := Green1Circle.middle_measure.1.preimage (Green1Circle.dilation_preserves b (bne b hb)).measurable
    exact ((integrable_const (1:ℝ)).indicator set).sub (integrable_const _)
  have ent := dissociated_cosine_L1 B D sub diss
  rw [card] at ent
  have large := grow D.card (∫x,|F x|) U (integral_nonneg (fun _ => abs_nonneg _)) lower ent (up B nz card antisign)
  obtain ⟨K,c,bnd,size⟩ := finite_certificate F hi (2*j) large
  refine ⟨K,c,bnd,?_⟩
  dsimp only [F,I] at size
  simp_rw [GreenArcFourier.signal_coeff B bne] at size
  exact size
end GreenBedert

end

end

/-- Bedert's high-dimensional branch. The Riesz-product entropy estimate and
Bourgain's cosine comparison force arbitrarily large arc discrepancy. -/
theorem GreenHigh.high_child : OMA.R_Green1_green_1_R1.H1 := by
  classical
  apply GreenBedert.high_child_of_cosine_bound
  obtain ⟨C,hC,h⟩ := GreenBourgain.bourgain_lift
  refine ⟨C,hC,?_⟩
  filter_upwards [Filter.eventually_ge_atTop (2:ℕ)] with n large
  intro B nz card _ I
  have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have bound := h B (by simpa only [card] using large) (fun b hb he => nz (he ▸ hb))
  rw [card] at bound
  exact bound.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (mul_nonneg hC.le hlog))
end

section
section
section

open Finset MeasureTheory
namespace BedertTest

/-- The MPS dampers can be chosen linear in the amplitude. The combined test
has norm at most one because its scalar majorant telescopes exactly. -/
theorem weights_sum_le (a : ℕ → ℝ) (ha : ∀ i, a i ≤ 1) (J : ℕ) :
    ∑ i ∈ range J, a i * ∏ j ∈ Ico (i+1) J, (1-a j) ≤ 1 := by
  have h (n : ℕ) : ∑ i ∈ range n, a i * ∏ j ∈ Ico (i+1) n, (1-a j) =
      1 - ∏ j ∈ range n, (1-a j) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, prod_range_succ]
      simp only [Ico_self,prod_empty,mul_one]
      have split (i : ℕ) (hi : i ∈ range n) : a i * ∏ j ∈ Ico (i+1) (n+1), (1-a j) =
          (a i * ∏ j ∈ Ico (i+1) n, (1-a j))*(1-a n) := by
        rw [prod_Ico_succ_top (mem_range.mp hi)]; ring
      rw [sum_congr rfl split, ←sum_mul, ih]; ring
  rw [h]
  have hpos := prod_nonneg (s := range J) (fun i _ => sub_nonneg.mpr (ha i))
  linarith

theorem lost_weight_le (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, a i ≤ 1)
    (s : Finset ℕ) : 1 - (∏ j ∈ s, (1-a j)) ≤ ∑ j ∈ s, a j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [prod_insert hi, sum_insert hi]
    have hp : ∏ j ∈ s, (1-a j) ≤ 1 :=
      prod_le_one (fun j _ => by linarith [hb j]) (fun j _ => by linarith [ha j])
    nlinarith [mul_nonneg (ha i) (sub_nonneg.mpr hp)]

/-- Integration of the MPS test. Here b_i is the real pairing of the Fourier
projection of F to the ith character class with the normalized block g_i.
The projection may be used under the remaining (invariant) dampers. -/
theorem pairing_lower {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (J : ℕ) (F : X → ℂ) (g : ℕ → X → ℂ) (b : ℕ → X → ℝ)
    (cF : Continuous F) (cg : ∀ i, Continuous (g i)) (cb : ∀ i, Continuous (b i))
    (amp : ∀ i x, ‖g i x‖ ≤ 1)
    (main : ∀ i < J, (9:ℝ)/10 ≤ ∫ x, b i x ∂μ)
    (small : ∀ i < J, ∑ j ∈ Ico (i+1) J, ∫ x, |b i x| *‖g j x‖ ∂μ ≤ 11/20)
    (proj : ∀ i < J, (∫ x, (F x * star (g i x)).re *
        (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) =
        ∫ x, b i x * (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) :
    (7/20 : ℝ)*J ≤ ∫ x, ‖F x‖ ∂μ := by
  have integ {f : X → ℝ} (h : Continuous f) : Integrable f μ :=
    (integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ))
  let P (i : ℕ) (x : X) := ∏ j ∈ Ico (i+1) J, (1-‖g j x‖)
  have cP i : Continuous (P i) := continuous_finsetProd _ (fun j _ => continuous_const.sub (cg j).norm)
  have posP i x : 0 ≤ P i x := prod_nonneg (fun j _ => sub_nonneg.mpr (amp j x))
  have leP i x : P i x ≤ 1 := prod_le_one (fun j _ => sub_nonneg.mpr (amp j x))
    (fun j _ => by linarith [norm_nonneg (g j x)])
  have loss i x : 1-P i x ≤ ∑ j ∈ Ico (i+1) J, ‖g j x‖ :=
    lost_weight_le _ (fun _ => norm_nonneg _) (fun j => amp j x) _
  have row i (hi : i < J) : (7:ℝ)/20 ≤ ∫ x, b i x * P i x ∂μ := by
    have pt (x : X) : b i x - b i x * P i x ≤ ∑ j ∈ Ico (i+1) J, |b i x| *‖g j x‖ := by
      rw [←mul_sum, ←mul_one_sub]
      exact (mul_le_mul_of_nonneg_right (le_abs_self _) (sub_nonneg.mpr (leP i x))).trans
        (mul_le_mul_of_nonneg_left (loss i x) (abs_nonneg _))
    have bound := integral_mono (μ := μ)
      (integ ((cb i).sub ((cb i).mul (cP i))))
      (by apply integ; fun_prop) pt
    change (∫ x, b i x - b i x * P i x ∂μ) ≤ _ at bound
    rw [integral_sub, integral_finsetSum] at bound
    · linarith [main i hi, small i hi]
    all_goals first | exact integ (cb i) | exact integ ((cb i).mul (cP i)) | intro j hj; exact integ ((cb i).abs.mul (cg j).norm)
  have term (i : ℕ) (x : X) : (F x * star (g i x)).re * P i x ≤ ‖F x‖ * (‖g i x‖ * P i x) := by
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (posP i x)
    simpa only [norm_mul, norm_star] using Complex.re_le_norm (F x * star (g i x))
  let W (i : ℕ) (x : X) := (F x * star (g i x)).re * P i x
  have point (x : X) : ∑ i ∈ range J, W i x ≤ ‖F x‖ := calc
    _ ≤ ∑ i ∈ range J, ‖F x‖ * (‖g i x‖ * P i x) := sum_le_sum fun i _ => term i x
    _ ≤ ‖F x‖ := by rw [←mul_sum]; exact mul_le_of_le_one_right (norm_nonneg _) (weights_sum_le _ (fun i => amp i x) J)
  have cW i : Continuous (W i) := (Complex.continuous_re.comp (cF.mul (cg i).star)).mul (cP i)
  calc
    _ = ∑ i ∈ range J, (7:ℝ)/20 := by simp [mul_comm]
    _ ≤ ∑ i ∈ range J, ∫ x, W i x ∂μ := by
      apply sum_le_sum
      intro i hi
      rw [show (∫ x, W i x ∂μ) = ∫ x, b i x*P i x ∂μ from proj i (mem_range.mp hi)]
      exact row i (mem_range.mp hi)
    _ = ∫ x, ∑ i ∈ range J, W i x ∂μ := (integral_finsetSum _ (fun i _ => (integ (cW i)))).symm
    _ ≤ _ := integral_mono (integ (continuous_finsetSum _ fun i _ => cW i))
      (integ cF.norm) point

end BedertTest

end

section

open Finset MeasureTheory
namespace BedertTest

theorem sqrt_pairing_bound {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {f g : X → ℂ} (cf : Continuous f) (cg : Continuous g) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hf : ∫ x, ‖f x‖^2 ∂μ ≤ a^2) (hg : ∫ x, ‖g x‖^2 ∂μ ≤ b^2) :
    ∫ x, ‖f x‖*‖g x‖ ∂μ ≤ a*b := by
  have integ {v : X → ℝ} (hv : Continuous v) : Integrable v μ :=
    integrableOn_univ.mp (hv.continuousOn.integrableOn_compact isCompact_univ)
  have pt (x : X) : (2*a*b)*(‖f x‖*‖g x‖) ≤ b^2*‖f x‖^2 + a^2*‖g x‖^2 := by
    nlinarith [sq_nonneg (b*‖f x‖-a*‖g x‖)]
  have h := integral_mono (μ := μ) (f := fun x => (2*a*b)*(‖f x‖*‖g x‖))
    (g := fun x => b^2*‖f x‖^2+a^2*‖g x‖^2) (integ (by fun_prop)) (integ (by fun_prop)) pt
  rw [integral_const_mul, integral_add (integ (by fun_prop)) (integ (by fun_prop)),
    integral_const_mul, integral_const_mul] at h
  have z : (2*a*b) * (∫ x, ‖f x‖*‖g x‖ ∂μ) ≤ (2*a*b)*(a*b) := by
    nlinarith [mul_le_mul_of_nonneg_left hf (sq_nonneg b),mul_le_mul_of_nonneg_left hg (sq_nonneg a)]
  exact le_of_mul_le_mul_left z (by positivity)

theorem sum_inverse_tail {w : ℕ → ℝ} {i J : ℕ} (hw : ∀ i, 0 < w i)
    (grow : ∀ i, i+1 < J → 3*w i ≤ w (i+1)) (h : i < J) : ∑ j ∈ Ico (i+1) J, (w j)⁻¹ ≤ (w i)⁻¹/2 := by
  by_cases last : i+1=J
  · rw [last, Ico_self, sum_empty]; have := hw i; positivity
  have hs (n i : ℕ) (hn : i+n ≤ J) : ∑ j ∈ Ico i (i+n), (w j)⁻¹ ≤ (3/2)*(w i)⁻¹ := by
    induction n generalizing i with
    | zero => simp; have := hw i; positivity
    | succ n ih =>
      rw [sum_eq_sum_Ico_succ_bot (by omega : i < i+(n+1))]
      by_cases none : n = 0
      · subst n; simp; have := hw i; nlinarith [inv_pos.mpr (hw i)]
      have after := ih (i+1) (by omega)
      rw [show i+(n+1)=i+1+n by omega]
      have step := grow i (by omega)
      have ratio : 3*(w (i+1))⁻¹ ≤ (w i)⁻¹ := by
        rw [←div_eq_mul_inv, inv_eq_one_div]
        exact (div_le_div_iff₀ (hw (i+1)) (hw i)).mpr (by linarith)
      linarith
  have bound := hs (J-(i+1)) (i+1) (by omega)
  rw [show i+1+(J-(i+1))=J by omega] at bound
  have goal : 3*(w (i+1))⁻¹ ≤ (w i)⁻¹ := by
    rw [←div_eq_mul_inv, inv_eq_one_div]
    exact (div_le_div_iff₀ (hw (i+1)) (hw i)).mpr (by linarith [grow i (by omega)])
  linarith

theorem norm_lower {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (J : ℕ) (F : X → ℂ) (g D : ℕ → X → ℂ) (w : ℕ → ℝ)
    (cF : Continuous F) (cg : ∀ i, Continuous (g i)) (cD : ∀ i, Continuous (D i))
    (hw : ∀ i, 0 < w i) (grow : ∀ i, i+1 < J → 3*w i ≤ w (i+1))
    (amp : ∀ i x, ‖g i x‖ ≤ 1)
    (ng : ∀ i < J, ∫ x, ‖g i x‖^2 ∂μ ≤ ((w i)⁻¹)^2)
    (nD : ∀ i < J, ∫ x, ‖D i x‖^2 ∂μ ≤ (11/10*w i)^2)
    (main : ∀ i < J, (9:ℝ)/10 ≤ ∫ x, (D i x*star (g i x)).re ∂μ)
    (proj : ∀ i < J, (∫ x, (F x*star (g i x)).re *
        (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) =
        ∫ x, (D i x*star (g i x)).re * (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) :
    (7/20 : ℝ)*J ≤ ∫ x, ‖F x‖ ∂μ := by
  let b i x := (D i x * star (g i x)).re
  have cb i : Continuous (b i) := Complex.continuous_re.comp ((cD i).mul (cg i).star)
  apply pairing_lower μ J F g b cF cg cb amp main _ proj
  intro i hi
  have integ {v : X → ℝ} (hv : Continuous v) : Integrable v μ :=
    integrableOn_univ.mp (hv.continuousOn.integrableOn_compact isCompact_univ)
  have point j (x : X) : |b i x| * ‖g j x‖ ≤ ‖D i x‖ * ‖g j x‖ := by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ‖D i x * star (g i x)‖ := Complex.abs_re_le_norm _
      _ = ‖D i x‖*‖g i x‖ := by simp
      _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) (amp i x)
  calc
    _ ≤ ∑ j ∈ Ico (i+1) J, (11/10*w i)*(w j)⁻¹ := by
      apply sum_le_sum
      intro j hj
      apply (integral_mono (integ ((cb i).abs.mul (cg j).norm))
        (integ ((cD i).norm.mul (cg j).norm)) (point j)).trans
      exact sqrt_pairing_bound μ (cD i) (cg j) (by have := hw i; positivity)
        (inv_pos.mpr (hw j)) (nD i hi) (ng j (mem_Ico.mp hj).2)
    _ = (11/10*w i)* ∑ j ∈ Ico (i+1) J, (w j)⁻¹ := (mul_sum ..).symm
    _ ≤ (11/10*w i)*((w i)⁻¹/2) := mul_le_mul_of_nonneg_left (sum_inverse_tail hw grow hi)
      (by have := hw i; positivity)
    _ = 11/20 := by field_simp [ne_of_gt (hw i)]; ring

end BedertTest

end

section

open Finset MeasureTheory
namespace BedertTest

/-- Each projected signal is a normalized frequency packet plus an error at
most one tenth of its L² norm. -/
theorem packets_lower {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (J : ℕ) (F : X → ℂ) (g E : ℕ → X → ℂ) (w : ℕ → ℝ)
    (cF : Continuous F) (cg : ∀ i, Continuous (g i)) (ce : ∀ i, Continuous (E i))
    (hw : ∀ i, 0 < w i) (grow : ∀ i, i+1 < J → 3*w i ≤ w (i+1))
    (amp : ∀ i x, ‖g i x‖ ≤ 1)
    (ng : ∀ i < J, ∫ x, ‖g i x‖^2 ∂μ = ((w i)⁻¹)^2)
    (ne : ∀ i < J, ∫ x, ‖E i x‖^2 ∂μ ≤ (w i/10)^2)
    (proj : ∀ i < J, (∫ x, (F x*star (g i x)).re *
        (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) =
        ∫ x, ((((w i)^2 : ℝ) * g i x + E i x : ℂ) * star (g i x)).re *
            (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂μ) :
    (7/20 : ℝ)*J ≤ ∫ x, ‖F x‖ ∂μ := by
  let D (i : ℕ) (x : X) : ℂ := ((w i)^2 : ℝ) * g i x + E i x
  have cD (i : ℕ) : Continuous (D i) := (continuous_const.mul (cg i)).add (ce i)
  have integ {v : X → ℝ} (hv : Continuous v) : Integrable v μ :=
    integrableOn_univ.mp (hv.continuousOn.integrableOn_compact isCompact_univ)
  have pair i (hi : i < J) : ∫ x, ‖E i x‖ * ‖g i x‖ ∂μ ≤ 1/10 := by
    apply (sqrt_pairing_bound μ (ce i) (cg i) (by have := hw i; positivity : 0 < w i/10)
      (inv_pos.mpr (hw i)) (ne i hi) (ng i hi).le).trans
    field_simp [ne_of_gt (hw i)]; norm_num
  apply norm_lower μ J F g D w cF cg cD hw grow amp (fun i hi => (ng i hi).le) _ _ _
  · intro i hi
    let u := w i
    have u0 : 0 < u := hw i
    have point (x : X) : ‖D i x‖^2 ≤ (u^2)^2 * ‖g i x‖^2 +
        (2*u^2)*(‖E i x‖*‖g i x‖) + ‖E i x‖^2 := by
      have t := norm_add_le (((u^2:ℝ):ℂ)*g i x) (E i x)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at t
      change ‖((u^2:ℝ):ℂ)*g i x + E i x‖^2 ≤ _
      have sq := pow_le_pow_left₀ (norm_nonneg _) t 2
      nlinarith only [sq]
    have step := integral_mono (μ := μ) (f := fun x => ‖D i x‖^2)
      (g := fun x => (u^2)^2 * ‖g i x‖^2 + (2*u^2)*(‖E i x‖*‖g i x‖)+‖E i x‖^2)
      (integ (by fun_prop)) (integ (by fun_prop)) point
    rw [integral_add (integ (by fun_prop)) (integ (by fun_prop)),
      integral_add (integ (by fun_prop)) (integ (by fun_prop)),integral_const_mul,integral_const_mul,ng i hi] at step
    have uu : (u^2)^2 * (w i)⁻¹^2 = u^2 := by change (u^2)^2 * u⁻¹^2 = u^2; field_simp
    rw [uu] at step
    have pe := mul_le_mul_of_nonneg_left (pair i hi) (by positivity : 0 ≤ 2*u^2)
    change (∫ x, ‖D i x‖^2 ∂μ) ≤ (11/10*u)^2
    have en : (∫ x, ‖E i x‖^2 ∂μ) ≤ (u/10)^2 := ne i hi
    nlinarith only [step,pe,en]
  · intro i hi
    have lower (x : X) : (w i)^2 * ‖g i x‖^2 - ‖E i x‖*‖g i x‖ ≤
        (D i x * star (g i x)).re := by
      have a := neg_abs_le (E i x * star (g i x)).re
      have b := Complex.abs_re_le_norm (E i x * star (g i x))
      rw [norm_mul,norm_star] at b
      simp only [D, add_mul, Complex.add_re, mul_assoc, Complex.star_def, Complex.mul_conj,
        ← Complex.ofReal_mul, Complex.ofReal_re, Complex.normSq_eq_norm_sq] at a b ⊢
      linarith
    have step := integral_mono (μ := μ)
      (f := fun x => (w i)^2 * ‖g i x‖^2 - ‖E i x‖*‖g i x‖)
      (g := fun x => (D i x*star (g i x)).re) (integ (by fun_prop)) (integ (by fun_prop)) lower
    rw [integral_sub (integ (by fun_prop)) (integ (by fun_prop)), integral_const_mul, ng i hi] at step
    have one : (w i)^2*(w i)⁻¹^2 = 1 := by field_simp [ne_of_gt (hw i)]
    rw [one] at step
    linarith [pair i hi]
  · intro i hi
    simpa [D] using proj i hi

end BedertTest

end

section

open Finset MeasureTheory AddCircle
namespace BedertTest

/-- Translation by the q-torsion point distinguishes exactly the q-residue
classes among the additive characters of the circle. -/
theorem phase_eq_iff {q : ℕ} (hq : 0 < q) (n r : ℤ) :
    fourier n (↑(1/(q:ℝ)) : AddCircle (1:ℝ)) = fourier r (↑(1/(q:ℝ)) : AddCircle (1:ℝ)) ↔
      (q:ℤ) ∣ n-r := by
  let t : AddCircle (1:ℝ) := ↑(1/(q:ℝ))
  have order : addOrderOf t = q := addOrderOf_period_div hq
  calc
    _ ↔ n • t = r • t := by
      simp only [fourier_apply]
      exact ⟨fun h => AddCircle.injective_toCircle (by norm_num : (1:ℝ) ≠ 0) (Subtype.ext h),
        fun h => congrArg (fun x : AddCircle (1:ℝ) => (x.toCircle:ℂ)) h⟩
    _ ↔ (n-r) • t = 0 := by rw [sub_zsmul, ←sub_eq_add_neg, sub_eq_zero]
    _ ↔ _ := by rw [←addOrderOf_dvd_iff_zsmul_eq_zero,order]

theorem char_translate {n : ℤ} (t x : AddCircle (1:ℝ)) :
    fourier n (t + x) = fourier n t * fourier n x := by
  simp only [fourier_apply,zsmul_add,toCircle_add,Circle.coe_mul]

theorem integral_eigen_zero (h : AddCircle (1:ℝ) → ℂ) (t : AddCircle (1:ℝ))
    (z : ℂ) (ne : z ≠ 1) (shift : ∀ x, h (t+x) = z*h x) :
    ∫ x, h x ∂AddCircle.haarAddCircle = 0 := by
  have eq := integral_add_left_eq_self (μ := AddCircle.haarAddCircle) h t
  simp_rw [shift] at eq
  rw [integral_const_mul] at eq
  have zero : (z-1)*(∫ x, h x ∂AddCircle.haarAddCircle) = 0 := by linear_combination eq
  exact (mul_eq_zero.mp zero).resolve_left (sub_ne_zero.mpr ne)

theorem restrict_pairing (s : Finset ℤ) (c : ℤ → ℂ) {q : ℕ} (hq : 0 < q) (r : ℤ)
    (H : AddCircle (1:ℝ) → ℂ) (hH : Continuous H)
    (shift : ∀ x, H ((↑(1/(q:ℝ)) : AddCircle (1:ℝ)) + x) =
      fourier r (↑(1/(q:ℝ)) : AddCircle (1:ℝ)) * H x) :
    (∫ x, (∑ n ∈ s, c n * fourier n x) * star (H x) ∂AddCircle.haarAddCircle) =
      ∫ x, (∑ n ∈ s.filter (fun n => (q:ℤ) ∣ n-r), c n * fourier n x) *
        star (H x) ∂AddCircle.haarAddCircle := by
  let t : AddCircle (1:ℝ) := ↑(1/(q:ℝ))
  let δ (n : ℤ) : ℂ := fourier n t
  have unit (n : ℤ) : δ n * star (δ n) = 1 := by
    simp only [δ, fourier_apply,Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,Circle.norm_coe]
    norm_num
  have itg (n : ℤ) : Integrable (fun x : AddCircle (1:ℝ) => c n * fourier n x * star (H x))
      AddCircle.haarAddCircle := integrableOn_univ.mp
        (((continuous_const.mul (fourier n).continuous).mul hH.star).continuousOn.integrableOn_compact isCompact_univ)
  simp_rw [sum_mul]
  rw [integral_finsetSum _ (fun n _ => itg n),integral_finsetSum _ (fun n _ => itg n)]
  symm
  apply sum_subset (filter_subset ..)
  intro n mem hn
  have sep : δ n ≠ δ r := (phase_eq_iff hq n r).not.mpr (by simpa [mem] using hn)
  apply integral_eigen_zero _ t (δ n * star (δ r)) _ _
  · intro eq
    apply sep
    have e := congrArg (· * δ r) eq
    rw [mul_assoc, mul_comm (star (δ r)), unit, mul_one, one_mul] at e
    exact e
  · intro x
    rw [char_translate, shift, star_mul]
    change c n * (δ n * fourier n x) * (star (H x) * star (δ r)) = _
    ring

end BedertTest

end

section

open Finset MeasureTheory AddCircle
namespace BedertTest

/-- Orthogonality of the unit-circle exponential system with normalized Haar measure. -/
theorem char_pair (a b : ℤ) :
    (∫ x : AddCircle (1:ℝ), fourier a x * star (fourier b x) ∂haarAddCircle) =
      if a = b then 1 else 0 := by
  have fc := congrFun (@fourierCoeff_fourier (1:ℝ) _ a) b
  simpa only [fourierCoeff, fourier_neg, Complex.star_def, smul_eq_mul,
    mul_comm, Pi.single_apply, eq_comm] using fc

/-- For a finite Fourier series its squared norm is exactly the sum of the
squared coefficient norms. This finite version needs no completeness lemma. -/
theorem trig_square (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x : AddCircle (1:ℝ), ‖∑ n ∈ s, a n*fourier n x‖^2 ∂haarAddCircle) =
      ∑ n ∈ s, ‖a n‖^2 := by
  have cc n m : Continuous (fun x : AddCircle (1:ℝ) => (a n*star (a m)) * (fourier n x * star (fourier m x))) :=
    continuous_const.mul ((fourier n).continuous.mul (fourier m).continuous.star)
  have integ {f : AddCircle (1:ℝ) → ℂ} (h : Continuous f) : Integrable f haarAddCircle :=
    (integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ))
  have pt (x : AddCircle (1:ℝ)) :
      ((‖∑ n ∈ s, a n*fourier n x‖^2:ℝ):ℂ) =
      ∑ n ∈ s, ∑ m ∈ s, (a n * star (a m))*(fourier n x * star (fourier m x)) := by
    rw [←Complex.normSq_eq_norm_sq, ←Complex.mul_conj]
    simp only [map_sum, map_mul, sum_mul, mul_sum, Complex.star_def]
    rw [sum_comm]
    apply sum_congr rfl; intro n hn
    apply sum_congr rfl; intro m hm
    ring
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal]
  simp_rw [pt]
  rw [integral_finsetSum _ (fun n _ => integ (continuous_finsetSum _ fun m _ => cc n m))]
  simp_rw [fun n => integral_finsetSum s (fun m _ => integ (cc n m)), integral_const_mul, char_pair]
  push_cast
  apply sum_congr rfl
  intro n hn
  classical
  simp only [mul_ite, mul_one, mul_zero]
  simp [hn,Complex.mul_conj,Complex.normSq_eq_norm_sq]

end BedertTest

end

section

open AddCircle Finset MeasureTheory
namespace BedertTest

theorem packet_shift (A : Finset ℤ) (c : ℤ → ℂ) (q : ℕ) (pos : 0 < q) (r : ℤ)
    (support : ∀ n ∈ A, (q:ℤ) ∣ n-r) (x : AddCircle (1:ℝ)) :
    ∑ n ∈ A, c n*fourier n ((↑(1/(q:ℝ)) : AddCircle (1:ℝ))+x) =
      fourier r (↑(1/(q:ℝ)) : AddCircle (1:ℝ)) * ∑ n ∈ A, c n*fourier n x := by
  rw [mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [char_translate, (phase_eq_iff pos n r).mpr (support n hn)]
  ring

/-- Restricting the Fourier support to a residue class preserves the real
pairing against its normalized packet and all the later, invariant dampers. -/
theorem damped_filter (s : Finset ℤ) (c : ℤ → ℂ) (g : ℕ → AddCircle (1:ℝ) → ℂ)
    (cg : ∀ j, Continuous (g j)) {i J q : ℕ} (hq : 0 < q) (r : ℕ → ℤ)
    (tr : ∀ j ∈ Ico i J, ∀ x, g j ((↑(1/(q:ℝ)) : AddCircle (1:ℝ)) + x) =
      fourier (r j) (↑(1/(q:ℝ)) : AddCircle (1:ℝ)) * g j x) (hi : i < J) :
    (∫ x, ((∑ n ∈ s, c n * fourier n x) * star (g i x)).re *
        (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂haarAddCircle) =
      ∫ x, ((∑ n ∈ s.filter (fun n => (q:ℤ) ∣ n-r i), c n * fourier n x) * star (g i x)).re *
        (∏ j ∈ Ico (i+1) J, (1-‖g j x‖)) ∂haarAddCircle := by
  let t : AddCircle (1:ℝ) := ↑(1/(q:ℝ))
  let P (x : AddCircle (1:ℝ)) := ∏ j ∈ Ico (i+1) J, (1-‖g j x‖)
  have cp : Continuous P := continuous_finsetProd _ (fun j _ => continuous_const.sub (cg j).norm)
  let H (x : AddCircle (1:ℝ)) := g i x*(P x:ℂ)
  have ch : Continuous H := (cg i).mul (Complex.continuous_ofReal.comp cp)
  have ptrans (x : AddCircle (1:ℝ)) : P (t+x) = P x := by
    apply prod_congr rfl
    intro j hj
    rw [tr j (mem_Ico.mpr ⟨by have := (mem_Ico.mp hj).1; omega, (mem_Ico.mp hj).2⟩),
      norm_mul, fourier_apply, Circle.norm_coe, one_mul]
  have ht (x : AddCircle (1:ℝ)) : H (t+x) = fourier (r i) t * H x := by
    simp only [H,ptrans,tr i (mem_Ico.mpr ⟨le_rfl,hi⟩),mul_assoc,t]
  have central (B : Finset ℤ) :
      (∫ x, ((∑ n ∈ B, c n * fourier n x) * star (g i x)).re * P x ∂haarAddCircle) =
      (∫ x, (∑ n ∈ B, c n * fourier n x) * star (H x) ∂haarAddCircle).re := by
    have ct : Continuous (fun x => (∑ n ∈ B, c n * fourier n x) * star (H x)) :=
      (continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous).mul ch.star
    have itg := integrableOn_univ.mp (ct.continuousOn.integrableOn_compact isCompact_univ (μ := haarAddCircle))
    rw [←show (∫ x, ((∑ n ∈ B, c n * fourier n x) * star (H x)).re ∂haarAddCircle) =
        (∫ x, (∑ n ∈ B, c n * fourier n x) * star (H x) ∂haarAddCircle).re from integral_re itg]
    apply integral_congr_ae
    filter_upwards with x
    simp only [H,star_mul,Complex.star_def,Complex.conj_ofReal]
    rw [mul_left_comm, ←mul_assoc, mul_comm ((P x:ℝ):ℂ)]
    simp; ring
  exact (central s).trans ((congrArg Complex.re (restrict_pairing s c hq (r i) H ch ht)).trans (central _).symm)

end BedertTest

end

section

open MeasureTheory Finset AddCircle
namespace BedertTest

/-- Bedert's non-Archimedean test-function bound (Theorem 8.2) for finite
Fourier series. The polynomial actually used in Bedert's proof is of this kind.
A coefficient perturbation in each modular packet has squared mass at most
one hundredth of its cardinality. -/
theorem nonarchimedean_mps (s : Finset ℤ) (present : ℤ → Bool) (e : ℤ → ℂ)
    (J : ℕ) (q : ℕ → ℕ) (r : ℕ → ℤ) (positive : ∀ i < J, 0 < q i)
    (chain : ∀ i j, i ≤ j → j < J → q i ∣ q j)
    (cell : ℕ → Finset ℤ) (cells : ∀ i, cell i = s.filter (fun n => (q i:ℤ) ∣ n-r i))
    (B : ℕ → Finset ℤ) (blocks : ∀ i, B i = (cell i).filter (fun n => present n))
    (nonempty : ∀ i < J, (B i).Nonempty)
    (growth : ∀ i, i+1 < J → 10*(B i).card ≤ (B (i+1)).card)
    (noise : ∀ i < J, ∑ n ∈ cell i, ‖e n‖^2 ≤ (B i).card/100) :
    (7/20 : ℝ)*J ≤ ∫ x : AddCircle (1:ℝ),
      ‖∑ n ∈ s, ((if present n then 1 else 0) + e n) * fourier n x‖ ∂haarAddCircle := by
  classical
  let u (i : ℕ) : ℝ := max ((B i).card : ℝ) 1
  let w (i : ℕ) := Real.sqrt (u i)
  have one i : 1 ≤ u i := le_max_right _ _
  have upos i : 0 < u i := by linarith [one i]
  have wp i : 0 < w i := Real.sqrt_pos.mpr (upos i)
  have sq i : w i ^ 2 = u i := Real.sq_sqrt (upos i).le
  have ucard i (hi : i < J) : u i = (B i).card := by
    apply max_eq_left
    exact_mod_cast (nonempty i hi).card_pos
  let g (i : ℕ) (x : AddCircle (1:ℝ)) : ℂ := ∑ n ∈ B i, (↑((u i)⁻¹) : ℂ)*fourier n x
  let E (i : ℕ) (x : AddCircle (1:ℝ)) : ℂ := ∑ n ∈ cell i, e n * fourier n x
  let a (n : ℤ) : ℂ := (if present n then 1 else 0) + e n
  have cg (i : ℕ) : Continuous (g i) := continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous
  have sig (i : ℕ) (x : AddCircle (1:ℝ)) :
      ((w i^2:ℝ):ℂ)*g i x + E i x = ∑ n ∈ cell i, a n * fourier n x := by
    simp only [sq,g,E,mul_sum]
    have cancel (n : ℤ) : ((u i:ℝ):ℂ)*(↑((u i)⁻¹)*fourier n x) = fourier n x := by
      rw [←mul_assoc,←Complex.ofReal_mul,mul_inv_cancel₀ (upos i).ne',Complex.ofReal_one,one_mul]
    simp only [cancel,blocks,sum_filter,a,add_mul,sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro n hn
    cases present n <;> simp
  apply packets_lower haarAddCircle J _ g E w
      (continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous) cg
      (fun i => continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous) wp
  · intro i hi
    have old := sq i
    have new := sq (i+1)
    have v : 10*(B i).card ≤ (B (i+1)).card := growth i hi
    have v' : (10:ℝ)*((B i).card:ℝ) ≤ (B (i+1)).card := by exact_mod_cast v
    rw [←ucard i (by omega),←ucard (i+1) hi] at v'
    nlinarith [wp i,wp (i+1),sq_nonneg (w i)]
  · intro i x
    apply (norm_sum_le _ _).trans
    simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (upos i)),sum_const,nsmul_eq_mul]
    calc
      _ ≤ u i * (u i)⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (upos i).le)
      _ = 1 := mul_inv_cancel₀ (upos i).ne'
  · intro i hi
    rw [show (∫ x, ‖g i x‖^2 ∂haarAddCircle) = _ from trig_square (B i) (fun _ => (↑((u i)⁻¹):ℂ))]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (upos i)),sum_const,nsmul_eq_mul,
      ←ucard i hi]
    simp only [inv_pow, sq]
    field_simp [(upos i).ne']
  · intro i hi
    have ei := trig_square (cell i) e
    change (∫ x, ‖∑ n ∈ cell i, e n * fourier n x‖^2 ∂haarAddCircle) ≤ _
    rw [ei,div_pow,sq,ucard i hi]
    norm_num at *; exact noise i hi
  · intro i hi
    have tr (j : ℕ) (hj : j ∈ Ico i J) (x : AddCircle (1:ℝ)) :
        g j ((↑(1/(q i:ℝ)):AddCircle (1:ℝ))+x) =
          fourier (r j) (↑(1/(q i:ℝ)):AddCircle (1:ℝ))*g j x := by
      apply packet_shift (B j) _ (q i) (positive i hi) (r j) _ x
      intro n hn
      have hm : n ∈ cell j := (mem_filter.mp ((blocks j) ▸ hn)).1
      rw [cells j,mem_filter] at hm
      have hd : (q j:ℤ) ∣ n-r j := hm.2
      exact (Int.natCast_dvd_natCast.mpr (chain i j (mem_Ico.mp hj).1 (mem_Ico.mp hj).2)).trans hd
    simp_rw [sig,cells i]
    exact damped_filter s a g cg (positive i hi) r tr hi

end BedertTest

end

section
open Complex
namespace BedertTest

/-- A finite power of a one-sided polynomial provides the MPS damping
without needing a pointwise-convergent Fourier series for a Hilbert transform. -/
theorem finite_damping {z : ℂ} {a ε : ℝ} {M : ℕ} (m : 0 < M)
    (ap : 0 ≤ a) (a1 : a ≤ 1) (major : a+ε ≤ z.re)
    (hM : ‖z‖^2 ≤ M*ε) :
    ‖(1-z/(M:ℂ))^M‖ ≤ 1-a/2 ∧ ‖1-(1-z/(M:ℂ))^M‖ ≤ ‖z‖ := by
  let t : ℂ := 1-z/(M:ℂ)
  have m0 : 0 < (M:ℝ) := by exact_mod_cast m
  have mon : 1 ≤ (M:ℝ) := by exact_mod_cast m
  have eps : 0 ≤ ε := by nlinarith [sq_nonneg ‖z‖]
  have scale : ‖t‖^2 = 1 + ‖z‖^2/(M:ℝ)^2 - 2*z.re/M := by
    rw [←Complex.normSq_eq_norm_sq, Complex.normSq_sub, Complex.normSq_one,
      Complex.normSq_div, Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    simp only [one_mul, Complex.conj_re, Complex.div_natCast_re, norm_natCast]
    ring
  have hp : 0 ≤ 1-a/(M:ℝ) := by
    rw [sub_nonneg, div_le_one m0]; linarith
  have tbound : ‖t‖ ≤ 1-a/(M:ℝ) := by
    have s : ‖t‖^2 ≤ (1-a/(M:ℝ))^2 := by
      rw [scale]; field_simp
      nlinarith [mul_le_mul_of_nonneg_right major m0.le,sq_nonneg a]
    exact (sq_le_sq₀ (norm_nonneg _) hp).mp s
  have t1 : ‖t‖ ≤ 1 := tbound.trans (by linarith [div_nonneg ap m0.le])
  have w : 1+a ≤ (1+a/(M:ℝ))^M := by
    have bern := one_add_mul_le_pow (by linarith [div_nonneg ap m0.le] : (-2:ℝ) ≤ a/(M:ℝ)) M
    have cancel : (M:ℝ)*(a/M) = a := by field_simp
    rw [cancel] at bern
    exact bern
  have r : ‖t‖^M * (1+a/(M:ℝ))^M ≤ 1 := by
    rw [←mul_pow]
    apply pow_le_one₀ (mul_nonneg (norm_nonneg _) (by linarith [div_nonneg ap m0.le])) 
    calc
      _ ≤ (1-a/(M:ℝ))*(1+a/(M:ℝ)) := mul_le_mul_of_nonneg_right tbound (by positivity)
      _ ≤ 1 := by nlinarith [sq_nonneg (a/(M:ℝ))]
  constructor
  · change ‖t^M‖ ≤ _
    rw [norm_pow]
    have h : ‖t‖^M * (1+a) ≤ 1 :=
      (mul_le_mul_of_nonneg_left w (pow_nonneg (norm_nonneg _) _)).trans r
    exact (mul_le_mul_iff_left₀ (by linarith : 0 < 1+a)).mp
      (show ‖t‖^M*(1+a) ≤ (1-a/2)*(1+a) by nlinarith [mul_nonneg ap (sub_nonneg.mpr a1)])
  · have triangle (k : ℕ) : ‖1-t^k‖ ≤ k*‖1-t‖ := by
      induction k with
      | zero => simp
      | succ k ih =>
        have eq : 1-t^(k+1) = (1-t^k)+t^k*(1-t) := by rw [pow_succ]; ring
        rw [eq]
        apply (norm_add_le _ _).trans
        rw [norm_mul,norm_pow, Nat.cast_succ]
        have u := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := k) (norm_nonneg _) t1) (norm_nonneg (1-t))
        linarith
    have h := triangle M
    change ‖1-t^M‖ ≤ _
    apply h.trans
    dsimp [t]
    rw [sub_sub_cancel, norm_div, Complex.norm_natCast]; field_simp; rfl

end BedertTest
end

section
open MeasureTheory Finset Polynomial AddCircle
namespace BedertTest

theorem negative_power (k : ℕ) (x : UnitAddCircle) :
    fourier (-(k:ℤ)) x = (fourier (-1) x)^k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Nat.cast_succ, neg_add, fourier_add, pow_succ, ih]

/-- Fold the positive frequencies to the negative side, keeping the real
part unchanged and losing at most a factor two in the squared L² norm. -/
theorem fold_polynomial (K : Finset ℤ) (c : ℤ → ℂ) :
    ∃ h : Polynomial ℂ,
      (∀ x : UnitAddCircle, (h.eval (fourier (-1) x)).re =
        (∑ n ∈ K, c n*fourier n x).re) ∧
      (∫ x : UnitAddCircle, ‖h.eval (fourier (-1) x)‖^2 ∂haarAddCircle) ≤
        2*∑ n ∈ K, ‖c n‖^2 := by
  classical
  let L := K.filter (fun n => n ≤ 0)
  let H := K.filter (fun n => ¬ n ≤ 0)
  let h : Polynomial ℂ := ∑ n ∈ L, monomial n.natAbs (c n) +
    ∑ n ∈ H, monomial n.natAbs (star (c n))
  let f (S : Finset ℤ) (x : UnitAddCircle) := ∑ n ∈ S, c n*fourier n x
  have split (t : ℤ → ℂ) : (∑ n ∈ L, t n) + ∑ n ∈ H, t n = ∑ n ∈ K, t n :=
    sum_filter_add_sum_filter_not _ _ _
  have low (n : ℤ) (hn : n ∈ L) : -(n.natAbs:ℤ) = n := by
    have := (mem_filter.mp hn).2
    omega
  have high (n : ℤ) (hn : n ∈ H) : (n.natAbs:ℤ) = n := by
    have := (mem_filter.mp hn).2
    omega
  have val (x : UnitAddCircle) : h.eval (fourier (-1) x) = f L x + star (f H x) := by
    simp only [h,eval_add,eval_finsetSum,eval_monomial,←negative_power,f,star_sum,star_mul]
    congr 1
    · apply sum_congr rfl; intro n hn; rw [low n hn]
    · apply sum_congr rfl; intro n hn
      rw [high n hn, fourier_neg, Complex.star_def,mul_comm]
  refine ⟨h,?_,?_⟩
  · intro x
    rw [val, ←split (fun n => c n * fourier n x)]
    simp [f]
  · have bound x : ‖h.eval (fourier (-1) x)‖^2 ≤ 2*‖f L x‖^2 + 2*‖f H x‖^2 := by
      rw [val]
      have tr := norm_add_le (f L x) (star (f H x))
      rw [norm_star] at tr
      nlinarith only [pow_le_pow_left₀ (norm_nonneg _) tr 2, sq_nonneg (‖f L x‖-‖f H x‖)]
    have cf (S : Finset ℤ) : Continuous (f S) := continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous
    have hh : Continuous (fun x : UnitAddCircle => h.eval (fourier (-1) x)) := h.continuous.comp (fourier (-1)).continuous
    have integ {v : UnitAddCircle → ℝ} (hv : Continuous v) : Integrable v haarAddCircle :=
      integrableOn_univ.mp (hv.continuousOn.integrableOn_compact isCompact_univ)
    have b := integral_mono (μ := haarAddCircle)
      (f := fun x => ‖h.eval (fourier (-1) x)‖^2)
      (g := fun x => 2*‖f L x‖^2+2*‖f H x‖^2) (integ (by fun_prop)) (integ (by fun_prop)) bound
    rw [integral_add (integ (by fun_prop)) (integ (by fun_prop)),integral_const_mul,integral_const_mul] at b
    change _ ≤ 2*(∫ x, ‖∑ n ∈ L, c n*fourier n x‖^2 ∂haarAddCircle) +
      2*(∫ x, ‖∑ n ∈ H, c n*fourier n x‖^2 ∂haarAddCircle) at b
    rw [trig_square, trig_square, ←mul_add, sum_filter_add_sum_filter_not] at b
    exact b

end BedertTest
end

section
open Finset MeasureTheory AddCircle Polynomial
namespace BedertTest

/-- A finite negative-spectrum MPS corrector. The real-part majorant is obtained by
uniform approximation and folding; a polynomial damper replaces exponentiation. -/
theorem one_sided_correction (g : UnitAddCircle → ℂ) (cg : Continuous g)
    (amp : ∀ x, ‖g x‖ ≤ 1) {v : ℝ} (vp : 0 < v)
    (size : ∫ x, ‖g x‖^2 ∂haarAddCircle ≤ v^2) :
    ∃ Q : Polynomial ℂ, (∀ x : UnitAddCircle, ‖Q.eval (fourier (-1) x)‖ ≤ 1-‖g x‖/2) ∧
      (∫ x : UnitAddCircle, ‖1-Q.eval (fourier (-1) x)‖^2 ∂haarAddCircle) ≤ (3*v)^2 := by
  classical
  let δ := v/10
  have positive : 0 < δ := by dsimp [δ]; positivity
  let h : C(UnitAddCircle,ℂ) := ⟨fun x => ↑‖g x‖,Complex.continuous_ofReal.comp cg.norm⟩
  obtain ⟨K,c,near⟩ := GreenBedert.continuous_approximation h positive
  let L : Finset ℤ := K.map (Equiv.neg ℤ).toEmbedding
  let a (n : ℤ) := c (-n)
  let p (x : UnitAddCircle) := ∑ n ∈ L, a n*fourier n x
  have close (x : UnitAddCircle) : ‖p x - (‖g x‖:ℂ)‖ ≤ δ := by
    simpa [p,L,a,h,Equiv.neg_apply] using (near x).le
  obtain ⟨z, zr, ze⟩ := fold_polynomial L a
  let zz := z + C (↑(2*δ):ℂ)
  let zval : C(UnitAddCircle,ℂ) := ⟨fun x => zz.eval (fourier (-1) x), zz.continuous.comp (fourier (-1)).continuous⟩
  have rz (x : UnitAddCircle) : ‖g x‖+δ ≤ (zval x).re := by
    have tmp := (Complex.abs_re_le_norm (p x-(‖g x‖:ℂ))).trans (close x)
    rw [Complex.sub_re,Complex.ofReal_re] at tmp
    simp only [zval, ContinuousMap.coe_mk,zz,eval_add,eval_C,Complex.add_re,Complex.ofReal_re,zr]
    change _ ≤ (p x).re + 2*δ
    linarith [(abs_le.mp tmp).1]
  have integ {f : UnitAddCircle → ℝ} (cf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  have pc : Continuous p := continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous
  have psmall : ∫ x, ‖p x‖^2 ∂haarAddCircle ≤ 2*v^2 + 2*δ^2 := by
    have bd (x : UnitAddCircle) : ‖p x‖^2 ≤ 2*(‖g x‖^2)+2*δ^2 := by
      have t := norm_le_norm_sub_add (p x) (‖g x‖:ℂ)
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)] at t
      have b : ‖p x‖ ≤ δ + ‖g x‖ := t.trans (add_le_add_left (close x) _)
      nlinarith only [pow_le_pow_left₀ (norm_nonneg _) b 2, sq_nonneg (δ-‖g x‖)]
    have b := integral_mono (μ := haarAddCircle) (f := fun x => ‖p x‖^2)
      (g := fun x => 2*(‖g x‖^2)+2*δ^2) (integ (by fun_prop)) (integ (by fun_prop)) bd
    rw [integral_add (integ (by fun_prop)) (integrable_const _), integral_const_mul] at b
    simpa using b.trans (by simpa using (mul_le_mul_of_nonneg_left size (by norm_num : (0:ℝ)≤2)))
  have Z (x : UnitAddCircle) : ‖zval x‖^2 ≤ 2*‖z.eval (fourier (-1) x)‖^2 + 2*(2*δ)^2 := by
    have t := norm_add_le (z.eval (fourier (-1) x)) (↑(2*δ):ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ 2*δ)] at t
    change ‖(z+C (↑(2*δ):ℂ)).eval _‖^2 ≤ _
    rw [eval_add,eval_C]
    nlinarith only [pow_le_pow_left₀ (norm_nonneg _) t 2,sq_nonneg (‖z.eval (fourier (-1) x)‖-2*δ)]
  have zc : Continuous (fun x : UnitAddCircle => z.eval (fourier (-1) x)) := z.continuous.comp (fourier (-1)).continuous
  have zsmall : ∫ x, ‖zval x‖^2 ∂haarAddCircle ≤ (3*v)^2 := by
    have b := integral_mono (μ := haarAddCircle) (f := fun x => ‖zval x‖^2)
      (g := fun x => 2*‖z.eval (fourier (-1) x)‖^2 + 2*(2*δ)^2) (integ (by fun_prop)) (integ (by fun_prop)) Z
    rw [integral_add (integ (by fun_prop)) (integrable_const _),integral_const_mul] at b
    simp only [integral_const,probReal_univ,one_smul] at b
    have parse : ∑ n ∈ L, ‖a n‖^2 = ∫ x, ‖p x‖^2 ∂haarAddCircle := (trig_square L a).symm
    rw [parse] at ze
    change (∫ x, ‖zval x‖^2 ∂haarAddCircle) ≤ 2*(∫ x : UnitAddCircle, ‖z.eval (fourier (-1) x)‖^2 ∂haarAddCircle) + 2*(2*δ)^2 at b
    calc
      _ ≤ _ := b
      _ ≤ 2*(2*(2*v^2+2*δ^2))+2*(2*δ)^2 := by gcongr; exact ze.trans (mul_le_mul_of_nonneg_left psmall (by norm_num))
      _ ≤ _ := by dsimp [δ]; nlinarith [sq_nonneg v]
  obtain ⟨M,m⟩ := exists_nat_gt (max (‖zval‖^2/δ) 1)
  have m0 : 0 < M := by have := (le_max_right (‖zval‖^2/δ) 1).trans_lt m; exact_mod_cast (by linarith : (0:ℝ)< M)
  let Q : Polynomial ℂ := (1-C ((M:ℂ)⁻¹)*zz)^M
  have evalQ x : Q.eval (fourier (-1) x) = (1-zval x/(M:ℂ))^M := by
    simp [Q,zval,div_eq_mul_inv,mul_comm]
  have damper (x : UnitAddCircle) := finite_damping (z := zval x) (ε := δ) m0 (norm_nonneg _) (amp x) (rz x) (by
    have H := (le_max_left (‖zval‖^2/δ) 1).trans_lt m
    exact (pow_le_pow_left₀ (norm_nonneg _) (zval.norm_coe_le_norm x) 2).trans ((div_lt_iff₀ positive).mp H).le)
  refine ⟨Q,fun x => (evalQ x) ▸ (damper x).1,?_⟩
  apply (integral_mono (integ (by fun_prop)) (integ (by fun_prop)) _).trans zsmall
  intro x
  change ‖1 - Q.eval (fourier (-1) x)‖^2 ≤ ‖zval x‖^2
  rw [evalQ]
  exact pow_le_pow_left₀ (norm_nonneg _) (damper x).2 2

end BedertTest
end

section
open Finset MeasureTheory
namespace BedertTest

theorem complex_lost_weight {ι : Type*} (s : Finset ι) (q : ι → ℂ) (hq : ∀ k ∈ s, ‖q k‖ ≤ 1) :
    ‖1-∏ k ∈ s, q k‖ ≤ ∑ k ∈ s, ‖1-q k‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s h ih =>
    rw [prod_insert h,sum_insert h]
    have id : 1-q k*(∏ j ∈ s, q j) = (1-q k)+q k*(1-∏ j ∈ s, q j) := by ring
    rw [id]
    apply (norm_add_le ..).trans
    rw [norm_mul]
    gcongr
    exact (mul_le_of_le_one_left (norm_nonneg _) (hq k (mem_insert_self ..))).trans (ih fun j hj => hq j (mem_insert_of_mem hj))

theorem ordered_test_bound (J : ℕ) (g q : ℕ → ℂ) (hg : ∀ i, ‖g i‖ ≤ 1)
    (hq : ∀ i, ‖q i‖ ≤ 1-‖g i‖/2) :
    (∑ i ∈ range J, ‖g i‖*‖∏ j ∈ Ico (i+1) J, q j‖) ≤ 2 := by
  have bd (i : ℕ) : ‖∏ j ∈ Ico (i+1) J, q j‖ ≤ ∏ j ∈ Ico (i+1) J, (1-‖g j‖/2) := by
    rw [norm_prod]
    exact prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hq j)
  calc
    _ ≤ ∑ i ∈ range J, ‖g i‖ * ∏ j ∈ Ico (i+1) J, (1-‖g j‖/2) := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (bd i) (norm_nonneg _)
    _ = 2 * ∑ i ∈ range J, (‖g i‖/2) * ∏ j ∈ Ico (i+1) J, (1-‖g j‖/2) := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ _ := by linarith [weights_sum_le (fun j => ‖g j‖/2) (fun j => by linarith [hg j]) J]

theorem ordered_inverse_tail {w : ℕ → ℝ} {i J : ℕ} (hw : ∀ i, 0 < w i)
    (grow : ∀ i, i+1<J → 64*w i ≤ w (i+1)) (hi : i < J) :
    ∑ j ∈ Ico (i+1) J, (w j)⁻¹ ≤ (w i)⁻¹/32 := by
  by_cases last : i+1=J
  · rw [last,Ico_self,sum_empty]; exact div_nonneg (inv_nonneg.mpr (hw i).le) (by norm_num)
  have ip : i+1<J := by omega
  have rough := sum_inverse_tail (i := i+1) hw (fun k hk => by linarith [grow k hk,hw k]) ip
  rw [sum_eq_sum_Ico_succ_bot ip]
  have step : 64*(w (i+1))⁻¹ ≤ (w i)⁻¹ := by
    rw [←div_eq_mul_inv,inv_eq_one_div]
    exact (div_le_div_iff₀ (hw (i+1)) (hw i)).mpr (by linarith [grow i ip])
  linarith [inv_pos.mpr (hw (i+1))]

end BedertTest
end

section
open MeasureTheory Finset Polynomial AddCircle
namespace BedertTest

theorem polynomial_char_orthogonal (h : Polynomial ℂ) {a b : ℤ} (lt : a < b) :
    ∫ x : UnitAddCircle, fourier b x * star (fourier a x * h.eval (fourier (-1) x)) ∂haarAddCircle = 0 := by
  have integ {f : UnitAddCircle → ℂ} (cf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  induction h using Polynomial.induction_on' with
  | add p q ih jh =>
    simp only [eval_add,mul_add,star_add]
    rw [integral_add,ih,jh,add_zero]
    all_goals apply integ; fun_prop (disch := intros; continuity)
  | monomial n c =>
    have point (x : UnitAddCircle) : fourier b x * star (fourier a x * (monomial n c).eval (fourier (-1) x)) =
        star c * (fourier b x * star (fourier (a + -(n:ℤ)) x)) := by
      simp only [eval_monomial,fourier_add,negative_power,star_mul]; ring
    simp only [point,integral_const_mul,char_pair,if_neg (by omega : b ≠ a + -(n:ℤ)),mul_zero]

theorem ordered_filter (s A : Finset ℤ) (c d : ℤ → ℂ) (h : Polynomial ℂ) (t : ℤ)
    (cut : ∀ a ∈ A, a ≤ t) :
    (∫ x : UnitAddCircle, (∑ b ∈ s, c b*fourier b x) *
      star ((∑ a ∈ A, d a*fourier a x)*h.eval (fourier (-1) x)) ∂haarAddCircle) =
    ∫ x : UnitAddCircle, (∑ b ∈ s.filter (· ≤ t), c b*fourier b x) *
      star ((∑ a ∈ A, d a*fourier a x)*h.eval (fourier (-1) x)) ∂haarAddCircle := by
  classical
  let I (b a : ℤ) (x : UnitAddCircle) := fourier b x * star (fourier a x*h.eval (fourier (-1) x))
  let g (b : ℤ) := ∑ a ∈ A, (c b * star (d a))*(∫ x, I b a x ∂haarAddCircle)
  have ci (b a : ℤ) : Continuous (I b a) := (fourier b).continuous.mul
    (((fourier a).continuous.mul (h.continuous.comp (fourier (-1)).continuous)).star)
  have integ {f : UnitAddCircle → ℂ} (cf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  have eqn (S : Finset ℤ) : (∫ x : UnitAddCircle, (∑ b ∈ S, c b*fourier b x) *
      star ((∑ a ∈ A, d a*fourier a x)*h.eval (fourier (-1) x)) ∂haarAddCircle) = ∑ b ∈ S, g b := by
    have pt (x : UnitAddCircle) : (∑ b ∈ S, c b*fourier b x) *
        star ((∑ a ∈ A, d a*fourier a x)*h.eval (fourier (-1) x)) =
        ∑ b ∈ S, ∑ a ∈ A, (c b*star (d a))* I b a x := by
      rw [sum_mul]
      apply sum_congr rfl; intro b hb
      simp only [sum_mul,star_sum,mul_sum]
      apply sum_congr rfl; intro a ha
      simp only [I,star_mul]; ring
    simp only [pt]
    have ic (b a : ℤ) : Integrable (fun x => (c b*star (d a))*I b a x) haarAddCircle :=
      integ (continuous_const.mul (ci b a))
    rw [integral_finsetSum S (fun b _ => integrable_finsetSum A fun a _ => ic b a)]
    apply sum_congr rfl; intro b hb
    rw [integral_finsetSum A (fun a _ => ic b a)]
    simp only [integral_const_mul,g]
  rw [eqn,eqn]
  symm
  apply sum_subset (filter_subset _ _)
  intro b hb out
  apply sum_eq_zero; intro a ha
  have lt : a < b := by have := cut a ha; simp [hb] at out; omega
  rw [show (∫ x, I b a x ∂haarAddCircle) = 0 from polynomial_char_orthogonal h lt,mul_zero]

end BedertTest
end

section
open Finset MeasureTheory AddCircle
namespace BedertTest

theorem packet_gram (s A : Finset ℤ) (sub : A ⊆ s) (c d : ℤ → ℂ) :
    (∫ x : UnitAddCircle, (∑ n ∈ s,c n*fourier n x)*star (∑ k ∈ A,d k*fourier k x) ∂haarAddCircle) =
    ∑ k ∈ A,c k*star (d k) := by
  classical
  let f k n (x : UnitAddCircle) := (c n*star (d k))*(fourier n x*star (fourier k x))
  have integ (k n : ℤ) : Integrable (f k n) haarAddCircle := by
    have h : Continuous (f k n) := continuous_const.mul ((fourier n).continuous.mul (fourier k).continuous.star)
    exact integrableOn_univ.mp (h.continuousOn.integrableOn_compact isCompact_univ)
  have pt (x : UnitAddCircle) : (∑ n ∈ s,c n*fourier n x)*star (∑ k ∈ A,d k*fourier k x) =
      ∑ k ∈ A,∑ n ∈ s, f k n x := by
    simp only [star_sum,mul_sum]
    apply sum_congr rfl; intro k hk
    rw [sum_mul]; apply sum_congr rfl; intro n hn; simp only [f,star_mul]; ring
  simp only [pt]
  rw [integral_finsetSum A (fun k _ => integrable_finsetSum s fun n _ => integ k n)]
  apply sum_congr rfl; intro k hk
  rw [integral_finsetSum s (fun n _ => integ k n)]
  simp only [f,integral_const_mul,char_pair,mul_ite,mul_zero,mul_one]
  simp [sub hk]

end BedertTest
end

section
open Finset MeasureTheory
namespace BedertTest

/-- The loss from all higher-frequency corrections is bounded by a geometric
sum of their individual squared-energy bounds. -/
theorem ordered_row_loss {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {i J : ℕ} (hi : i<J) (D : X → ℂ) (q : ℕ → X → ℂ) (w : ℕ → ℝ)
    (cD : Continuous D) (cq : ∀ j, Continuous (q j)) (hw : ∀ k, 0 < w k)
    (grow : ∀ k, k+1<J → 64*w k ≤ w (k+1))
    (amp : ∀ j x, ‖q j x‖ ≤ 1) (size : ∫ x, ‖D x‖^2 ∂μ ≤ (3*w i)^2)
    (small : ∀ j < J, ∫ x, ‖1-q j x‖^2 ∂μ ≤ (3*(w j)⁻¹)^2) :
    (∫ x, ‖D x‖ * ‖1-∏ j ∈ Ico (i+1) J, q j x‖ ∂μ) ≤ 9/32 := by
  have integ {f : X → ℝ} (cf : Continuous f) : Integrable f μ :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  let I := Ico (i+1) J
  have comp (x : X) : ‖D x‖ * ‖1-∏ j ∈ I, q j x‖ ≤ ∑ j ∈ I, ‖D x‖ * ‖1-q j x‖ := by
    rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (complex_lost_weight I (fun j => q j x) (fun j _ => amp j x)) (norm_nonneg _)
  have cprod : Continuous (fun x => ∏ j ∈ I, q j x) := continuous_finsetProd _ fun j _ => cq j
  have ci (j : ℕ) : Continuous (fun x => ‖D x‖*‖1-q j x‖) := cD.norm.mul (continuous_const.sub (cq j)).norm
  calc
    _ ≤ ∫ x, ∑ j ∈ I, ‖D x‖*‖1-q j x‖ ∂μ := integral_mono
      (integ (cD.norm.mul (continuous_const.sub cprod).norm)) (integ (continuous_finsetSum _ fun j _ => ci j)) comp
    _ = ∑ j ∈ I, ∫ x, ‖D x‖*‖1-q j x‖ ∂μ := integral_finsetSum _ (fun j _ => integ (ci j))
    _ ≤ ∑ j ∈ I, (3*w i)*(3*(w j)⁻¹) := by
      apply sum_le_sum; intro j hj
      exact sqrt_pairing_bound μ cD (continuous_const.sub (cq j)) (by have := hw i; positivity)
        (by have := hw j; positivity) size (small j (mem_Ico.mp hj).2)
    _ = (9*w i)*∑ j ∈ I, (w j)⁻¹ := by rw [mul_sum]; apply sum_congr rfl; intros; ring
    _ ≤ (9*w i)*((w i)⁻¹/32) := mul_le_mul_of_nonneg_left (ordered_inverse_tail hw grow hi) (by have := hw i; positivity)
    _ = _ := by field_simp [ne_of_gt (hw i)]

/-- One corrected row detects a positive signal in the presence of a common
perturbation F↦F+E. Its energy hypotheses concern only a prefix D and E. -/
theorem ordered_row {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F E D g p : X → ℂ) (cF : Continuous F) (cE : Continuous E) (cD : Continuous D)
    (cg : Continuous g) (cp : Continuous p) (ag : ∀ x, ‖g x‖ ≤ 1) (ap : ∀ x, ‖p x‖ ≤ 1)
    (proj : (∫ x, (F x*star (g x*p x)).re ∂μ) = ∫ x, (D x*star (g x*p x)).re ∂μ)
    (main : 1 ≤ ∫ x, (D x*star (g x)).re ∂μ)
    (noise : (∫ x, ‖E x‖*‖g x‖ ∂μ) ≤ 1/4)
    (loss : (∫ x, ‖D x‖*‖1-p x‖ ∂μ) ≤ 9/32) :
    (15/32:ℝ) ≤ ∫ x, ((F x+E x)*star (g x*p x)).re ∂μ := by
  have integ {f : X → ℝ} (cf : Continuous f) : Integrable f μ :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  have npoint (x : X) : -(E x*star (g x*p x)).re ≤ ‖E x‖*‖g x‖ := by
    calc _ ≤ ‖E x*star (g x*p x)‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
         _ = (‖E x‖*‖g x‖)*‖p x‖ := by simp [mul_assoc]
         _ ≤ _ := mul_le_of_le_one_right (by positivity) (ap x)
  have lpoint (x : X) : (D x*star (g x)).re-(D x*star (g x*p x)).re ≤ ‖D x‖*‖1-p x‖ := by
    have id : D x*star (g x) - D x*star (g x*p x) = (D x*star (1-p x))*star (g x) := by simp only [star_sub,star_one,star_mul]; ring
    rw [←Complex.sub_re,id]
    calc _ ≤ ‖(D x*star (1-p x))*star (g x)‖ := Complex.re_le_norm _
         _ = (‖D x‖*‖1-p x‖)*‖g x‖ := by simp only [norm_mul,norm_star]
         _ ≤ _ := mul_le_of_le_one_right (by positivity) (ag x)
  have n := integral_mono (μ := μ) (f := fun x => -(E x*star (g x*p x)).re)
    (g := fun x => ‖E x‖*‖g x‖) (integ (by fun_prop)) (integ (by fun_prop)) npoint
  rw [integral_neg] at n
  have l := integral_mono (μ := μ) (f := fun x => (D x*star (g x)).re-(D x*star (g x*p x)).re)
    (g := fun x => ‖D x‖*‖1-p x‖) (integ (by fun_prop)) (integ (by fun_prop)) lpoint
  rw [integral_sub (integ (by fun_prop)) (integ (by fun_prop))] at l
  simp only [add_mul,Complex.add_re]
  rw [integral_add (integ (by fun_prop)) (integ (by fun_prop)),proj]
  linarith

end BedertTest
end

section
namespace GreenPackets

/-- The first k points of a nonempty finite ordered set are exactly its elements
below its kth point. -/
theorem prefix_size {α : Type*} [LinearOrder α] (S : Finset α) (k : Fin S.card) :
    (S.filter (· ≤ S.orderEmbOfFin rfl k)).card = k.val+1 := by
  classical
  let e := S.orderEmbOfFin rfl
  let embed : Fin (k.val+1) ↪ α := ⟨fun i => e ⟨i.val, by omega⟩, by
    intro a b h
    exact Fin.ext (congrArg (fun v : Fin S.card => v.val) (e.injective h))⟩
  have eq : S.filter (· ≤ e k) = Finset.univ.map embed := by
    ext x
    constructor
    · intro h
      obtain ⟨hs,ht⟩ := Finset.mem_filter.mp h
      have ran : x ∈ Set.range e := by rw [show Set.range e = (S:Set α) from S.range_orderEmbOfFin rfl]; exact hs
      obtain ⟨i,rfl⟩ := ran
      have le : i ≤ k := e.le_iff_le.mp ht
      exact Finset.mem_map.mpr ⟨⟨i.val,by omega⟩, Finset.mem_univ _, rfl⟩
    · intro h
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_filter.mpr ⟨S.orderEmbOfFin_mem rfl _,e.monotone (by
        change i.val ≤ k.val
        omega)⟩
  rw [show (S.filter (· ≤ S.orderEmbOfFin rfl k)) = _ from eq, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Successive packets of exact geometric sizes, each with a prefix cutoff
containing twice the packet size. Distinct packets are strictly ordered. -/
theorem ordered_packets (S : Finset ℤ) (J K : ℕ) (hk : 4096^(J+1) ≤ K)
    (large : K ≤ S.card) :
    ∃ (m : ℕ) (A : ℕ → Finset ℤ) (t : ℕ → ℤ), 0 < m ∧ 16*S.card ≤ m*K^2 ∧
      (∀ i < J, A i ⊆ S ∧ (∀ a ∈ A i, a ≤ t i) ∧
        (S.filter (· ≤ t i)).card ≤ 2*(A i).card ∧ (A i).card = 4096^i*m) ∧
      ∀ i j, i < j → j < J → ∀ x ∈ A i, ∀ y ∈ A j, x < y := by
  classical
  let N := S.card
  let m := N/K
  have klarge : 4096 ≤ K := (by
    simpa using Nat.pow_le_pow_right (by decide : 0<4096) (show 1 ≤ J+1 by omega) : 4096 ≤ 4096^(J+1)).trans hk
  have kp : 0<K := by omega
  have mp : 0 < m := Nat.div_pos large kp
  have km : m*K ≤ N := Nat.div_mul_le_self N K
  have nsmall : N < (m+1)*K := Nat.lt_mul_div_succ N kp |>.trans_eq (Nat.mul_comm _ _)
  have lb : 16*S.card ≤ m*K^2 := calc
    16*N ≤ 16*((m+1)*K) := Nat.mul_le_mul_left _ nsmall.le
    _ ≤ m*K^2 := by
      have hm : m+1 ≤ 2*m := by omega
      have t1 := Nat.mul_le_mul_right K hm
      have t2 := Nat.mul_le_mul_left (m*K) (show 32 ≤ K by omega)
      nlinarith
  let d (i : ℕ) := 4096^i*m
  have dp (i : ℕ) : 0 < d i := Nat.mul_pos (pow_pos (by decide) _) mp
  have sep (i j : ℕ) (lt : i < j) : 2*d i ≤ d j := by
    have hj := Nat.pow_le_pow_right (by decide : 0<4096) (show i+1 ≤ j by omega)
    rw [pow_succ] at hj
    dsimp [d]
    calc
      2*(4096^i*m) ≤ 4096*(4096^i*m) := Nat.mul_le_mul_right _ (by decide)
      _ = (4096^i*4096)*m := by ring
      _ ≤ _ := Nat.mul_le_mul_right m hj
  have fits (i : ℕ) (hi : i < J) : 2*d i ≤ S.card := calc
    2*d i ≤ d J := sep _ _ hi
    _ ≤ K*m := Nat.mul_le_mul_right m ((Nat.pow_le_pow_right (by decide : 0<4096) (Nat.le_succ J)).trans hk)
    _ = m*K := Nat.mul_comm _ _
    _ ≤ _ := km
  let e := S.orderEmbOfFin rfl
  let index (i : ℕ) (hi : i < J) (j : Fin (d i)) : Fin S.card := ⟨d i+j.val, by
    have := fits i hi; omega⟩
  let emb (i : ℕ) (hi : i < J) : Fin (d i) ↪ ℤ :=
    ⟨fun j => e (index i hi j), by
      intro a b h
      have eq := congrArg Fin.val (e.injective h)
      exact Fin.ext (Nat.add_left_cancel eq)⟩
  let last (i : ℕ) (hi : i < J) : Fin S.card := ⟨2*d i-1, by have := fits i hi; have := dp i; omega⟩
  let A (i : ℕ) := if hi : i < J then Finset.univ.map (emb i hi) else ∅
  let t (i : ℕ) := if hi : i < J then e (last i hi) else 0
  refine ⟨m,A,t,mp,lb,?_,?_⟩
  · intro i hi
    simp only [A,t,dif_pos hi,Finset.card_map,Finset.card_univ,Fintype.card_fin]
    refine ⟨?_,?_,?_,rfl⟩
    · intro x hx
      obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hx
      exact S.orderEmbOfFin_mem rfl _
    · intro x hx
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hx
      apply e.monotone
      change d i+j.val ≤ 2*d i-1
      omega
    · rw [show (S.filter (· ≤ e (last i hi))).card = _ from prefix_size S (last i hi)]
      dsimp [last]
      have := dp i
      omega
  · intro i j hij hj x hx y hy
    have hi := hij.trans hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp (show x ∈ Finset.univ.map (emb i hi) by simpa only [A,dif_pos hi] using hx)
    obtain ⟨b,_,rfl⟩ := Finset.mem_map.mp (show y ∈ Finset.univ.map (emb j hj) by simpa only [A,dif_pos hj] using hy)
    apply e.strictMono
    change d i+a.val < d j+b.val
    have := sep i j hij
    omega

end GreenPackets
end

section
open MeasureTheory Finset AddCircle Polynomial
namespace BedertTest

/-- An ordered-frequency, noise-stable form of the Littlewood inequality.
At each finite scale J the admissible perturbation has squared L² norm at most
N/K². This gives the logarithmic bound of Bedert 7.8 for trigonometric noise. -/
theorem ordered_mps (s : Finset ℤ) (c : ℤ → ℝ) (J K : ℕ)
    (hk : 4096^(J+1) ≤ K) (large : K ≤ s.card) (lower : ∀ n ∈ s, 1 ≤ c n)
    (upper : ∀ n ∈ s, c n ≤ 2) (E : UnitAddCircle → ℂ) (ce : Continuous E)
    (noise : (∫ x, ‖E x‖^2 ∂haarAddCircle) ≤ (s.card:ℝ)/(K:ℝ)^2) :
    (15/64 : ℝ)*J ≤ ∫ x : UnitAddCircle, ‖(∑ n ∈ s, (c n:ℂ)*fourier n x)+E x‖ ∂haarAddCircle := by
  classical
  obtain ⟨m,A,t,mp,mc,blocks,_⟩ := GreenPackets.ordered_packets s J K hk large
  let u (i : ℕ) : ℝ := max ((A i).card:ℝ) 1
  let w (i : ℕ) := Real.sqrt (u i)
  let g (i : ℕ) (x : UnitAddCircle) := ∑ n ∈ A i, (↑((u i)⁻¹):ℂ)*fourier n x
  let T (i : ℕ) := s.filter (· ≤ t i)
  let F (S : Finset ℤ) (x : UnitAddCircle) := ∑ n ∈ S, (c n:ℂ)*fourier n x
  have cF S : Continuous (F S) := continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous
  have cg i : Continuous (g i) := continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous
  have one i : 1 ≤ u i := le_max_right _ _
  have up i : 0<u i := by linarith [one i]
  have wp i : 0<w i := Real.sqrt_pos.mpr (up i)
  have sq i : w i^2 = u i := Real.sq_sqrt (up i).le
  have uval i (hi : i<J) : u i = (A i).card := by
    apply max_eq_left; have h := (blocks i hi).2.2.2
    exact_mod_cast (by rw [h]; positivity : 0 < (A i).card)
  have growth i (hi : i+1 < J) : 64*w i ≤ w (i+1) := by
    have ik := (blocks i (by omega)).2.2.2
    have sk := (blocks (i+1) hi).2.2.2
    have id : (A (i+1)).card=4096*(A i).card := by rw [ik,sk,pow_succ]; ring
    have re : u (i+1) = 4096*u i := by rw [uval _ hi,uval _ (by omega)]; exact_mod_cast id
    have bound : (64*w i)^2 ≤ (w (i+1))^2 := by rw [mul_pow,sq,sq,re]; norm_num
    exact nonneg_le_nonneg_of_sq_le_sq (wp _).le (by simpa only [pow_two] using bound)
  have ag i x : ‖g i x‖ ≤ 1 := by
    apply (norm_sum_le _ _).trans
    simp only [norm_mul,fourier_apply,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (up i)),sum_const,nsmul_eq_mul]
    calc _ ≤ u i*(u i)⁻¹ := mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr (up i).le)
         _ = 1 := mul_inv_cancel₀ (up i).ne'
  have ng i : ∫ x, ‖g i x‖^2 ∂haarAddCircle ≤ ((w i)⁻¹)^2 := by
    rw [show (∫ x, ‖g i x‖^2 ∂haarAddCircle) = _ from trig_square (A i) (fun _ => (↑((u i)⁻¹):ℂ))]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (up i)),sum_const,nsmul_eq_mul]
    calc _ ≤ u i*((u i)⁻¹)^2 := mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
         _ = _ := by rw [inv_pow,inv_pow,sq]; field_simp [(up i).ne']
  choose Q qa qs using fun i => one_sided_correction (g i) (cg i) (ag i) (inv_pos.mpr (wp i)) (ng i)
  let q (i : ℕ) (x : UnitAddCircle) := (Q i).eval (fourier (-1) x)
  let p (i : ℕ) (x : UnitAddCircle) := ∏ j ∈ Ico (i+1) J, q j x
  have cq i : Continuous (q i) := (Q i).continuous.comp (fourier (-1)).continuous
  have cp i : Continuous (p i) := continuous_finsetProd _ fun j _ => cq j
  have aq i x : ‖q i x‖ ≤ 1 := (qa i x).trans (by linarith [norm_nonneg (g i x)])
  have ap i x : ‖p i x‖ ≤ 1 := by dsimp only [p]; rw [norm_prod]; exact prod_le_one (fun j _ => norm_nonneg _) (fun j _ => aq j x)
  have integ {f : UnitAddCircle → ℝ} (hf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)
  have reint (f : UnitAddCircle → ℂ) (cf : Continuous f) :
      (∫ x, (f x).re ∂haarAddCircle) = (∫ x, f x ∂haarAddCircle).re := integral_re (integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ))
  have row i (hi : i<J) : (15/32:ℝ) ≤ ∫ x, ((F s x+E x)*star (g i x*p i x)).re ∂haarAddCircle := by
    apply ordered_row haarAddCircle (F s) E (F (T i)) (g i) (p i) (cF s) ce (cF _) (cg i) (cp i) (ag i) (ap i)
    · rw [reint (fun x => F s x*star (g i x*p i x)) (by fun_prop),reint (fun x => F (T i) x*star (g i x*p i x)) (by fun_prop)]
      apply congrArg Complex.re
      have pr := ordered_filter s (A i) (fun n => (c n : ℂ)) (fun _ => (↑((u i)⁻¹):ℂ)) (∏ j ∈ Ico (i+1) J,Q j) (t i) (blocks i hi).2.1
      simpa only [eval_prod] using pr
    · rw [reint (fun x => F (T i) x*star (g i x)) (by fun_prop)]
      have sub : A i ⊆ T i := fun n hn => mem_filter.mpr ⟨(blocks i hi).1 hn,(blocks i hi).2.1 n hn⟩
      rw [show (∫ x, F (T i) x * star (g i x) ∂haarAddCircle) = _ from packet_gram (T i) (A i) sub (fun n => (c n:ℂ)) (fun _ => (↑((u i)⁻¹):ℂ))]
      simp only [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,Complex.re_sum,Complex.ofReal_re]
      calc 1 = ∑ _n ∈ A i, (u i)⁻¹ := by simp [←uval i hi,(up i).ne']
           _ ≤ _ := sum_le_sum fun n hn => le_mul_of_one_le_left (inv_nonneg.mpr (up i).le) (lower n ((blocks i hi).1 hn))
    · have kp : 0 < (K:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by positivity) hk)
      have nsc : 16*(s.card:ℝ) ≤ (m:ℝ)*(K:ℝ)^2 := by exact_mod_cast mc
      have mm : (m:ℝ) ≤ u i := by
        rw [uval i hi]; exact_mod_cast (by rw [(blocks i hi).2.2.2]; exact Nat.le_mul_of_pos_left m (by positivity) : m ≤ (A i).card)
      have en : ∫ x, ‖E x‖^2 ∂haarAddCircle ≤ (w i/4)^2 := by
        apply noise.trans
        rw [div_le_iff₀ (by positivity),div_pow,sq]; nlinarith only [nsc,mul_le_mul_of_nonneg_right mm (sq_nonneg (K:ℝ))]
      apply (sqrt_pairing_bound haarAddCircle ce (cg i) (by have := wp i; positivity) (inv_pos.mpr (wp i)) en (ng i)).trans
      field_simp [(wp i).ne']; norm_num
    · apply ordered_row_loss haarAddCircle hi (F (T i)) q w (cF _) cq wp growth aq _ (fun j _ => qs j)
      rw [show (∫ x, ‖F (T i) x‖^2 ∂haarAddCircle) = _ from trig_square (T i) (fun n => (c n:ℂ))]
      have cb (n : ℤ) (hn : n ∈ T i) : ‖(c n:ℂ)‖^2 ≤ 4 := by
        have lo := lower n (mem_filter.mp hn).1; have hu := upper n (mem_filter.mp hn).1
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]; nlinarith
      have ne : ((T i).card : ℝ) ≤ 2*u i := by rw [uval i hi]; exact_mod_cast (blocks i hi).2.2.1
      calc _ ≤ ∑ _n ∈ T i, (4:ℝ) := sum_le_sum cb
           _ ≤ _ := by simp only [sum_const,nsmul_eq_mul,mul_pow,sq]; linarith [up i]
  let ff (x : UnitAddCircle) := F s x+E x
  have cff : Continuous ff := (cF s).add ce
  let h (i : ℕ) (x : UnitAddCircle) := (ff x*star (g i x*p i x)).re
  have ch i : Continuous (h i) := Complex.continuous_re.comp (cff.mul ((cg i).mul (cp i)).star)
  have point (x : UnitAddCircle) : ∑ i ∈ range J, h i x ≤ 2*‖ff x‖ := calc
    _ ≤ ∑ i ∈ range J, ‖ff x‖ * (‖g i x‖*‖p i x‖) := sum_le_sum (fun i _ => by simpa only [norm_mul,norm_star] using Complex.re_le_norm (ff x*star (g i x*p i x)))
    _ ≤ _ := by rw [←mul_sum,mul_comm (2:ℝ)]; exact mul_le_mul_of_nonneg_left (ordered_test_bound J (fun i => g i x) (fun j => q j x) (fun i => ag i x) (fun j => qa j x)) (norm_nonneg _)
  have steps : (15/32:ℝ)*J ≤ 2*∫ x, ‖ff x‖ ∂haarAddCircle := calc
    _ = ∑ _i ∈ range J, (15/32:ℝ) := by simp [mul_comm]
    _ ≤ ∑ i ∈ range J, ∫ x, h i x ∂haarAddCircle := sum_le_sum fun i hi => row i (mem_range.mp hi)
    _ = ∫ x, ∑ i ∈ range J, h i x ∂haarAddCircle := (integral_finsetSum _ (fun i _ => integ (ch i))).symm
    _ ≤ ∫ x, 2*‖ff x‖ ∂haarAddCircle := integral_mono (integ (continuous_finsetSum _ fun i _ => ch i)) (integ (continuous_const.mul cff.norm)) point
    _ = _ := integral_const_mul ..
  change _ ≤ ∫ x, ‖ff x‖ ∂haarAddCircle
  linarith

end BedertTest
end

section
open MeasureTheory Finset AddCircle
namespace BedertTest

theorem two_set_mps (B₁ B₂ : Finset ℤ) (J K : ℕ) (hk : 4096^(J+1) ≤ K) (large : K ≤ B₁.card)
    (E : UnitAddCircle → ℂ) (ce : Continuous E)
    (noise : (∫ x, ‖E x‖^2 ∂haarAddCircle) ≤ (B₁.card:ℝ)/(K:ℝ)^2) :
    (15/64:ℝ)*J ≤ ∫ x : UnitAddCircle,
      ‖((∑ n ∈ B₁, fourier n x)+(∑ n ∈ B₂, fourier n x))+E x‖ ∂haarAddCircle := by
  classical
  let S := B₁ ∪ B₂
  let a (T : Finset ℤ) (n : ℤ) : ℝ := if n ∈ T then 1 else 0
  let c n := a B₁ n + a B₂ n
  have present (n : ℤ) (hn : n ∈ S) : 1 ≤ c n ∧ c n ≤ 2 := by
    have either := mem_union.mp hn
    by_cases h₁ : n ∈ B₁ <;> by_cases h₂ : n ∈ B₂ <;> simp_all [c,a]
    norm_num
  have cnt : B₁.card ≤ S.card := card_le_card subset_union_left
  have b := ordered_mps S c J K hk (large.trans cnt) (fun n hn => (present n hn).1)
    (fun n hn => (present n hn).2) E ce (noise.trans (div_le_div_of_nonneg_right (by exact_mod_cast cnt) (sq_nonneg _)))
  have sum_eq (T : Finset ℤ) (sub : T ⊆ S) (x : UnitAddCircle) :
      (∑ n ∈ S, (a T n : ℂ)*fourier n x) = ∑ n ∈ T, fourier n x := by
    rw [←sum_subset sub (fun n _ hn => by simp [a,hn])]
    apply sum_congr rfl; intro n hn; simp [a,hn]
  have pt (x : UnitAddCircle) : (∑ n ∈ S, (c n:ℂ)*fourier n x) =
      (∑ n ∈ B₁, fourier n x)+(∑ n ∈ B₂, fourier n x) := by
    simp only [c,Complex.ofReal_add,add_mul,sum_add_distrib,sum_eq B₁ subset_union_left,sum_eq B₂ subset_union_right]
  simpa only [pt] using b

end BedertTest
end
end

section
section

end

section

namespace BedertSieve
open Finset Real

/-- Divisor mass for an arbitrary selected collection of small primes. -/
theorem prime_set_divisor_sum {Q : ℕ} (S : Finset ℕ) (sub : S ⊆ Nat.primesLE Q) :
    let M := ∏ p ∈ S,p
    ∑ d ∈ M.divisors, (1:ℝ)/d = ∏ p ∈ S, (1+(1:ℝ)/p) := by
  classical
  intro M
  have pr {p:ℕ} (hp : p∈S) := Nat.prime_of_mem_primesLE (sub hp)
  have hm : M ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun _ h => (pr h).ne_zero)
  have divides : M ∣ primorial Q := by
    rw [primorial_eq_prod_primesLE]
    exact prod_dvd_prod_of_subset _ _ _ sub
  have code (d : ℕ) (h : d∈M.divisors) : ∏ p ∈ d.primeFactors, p = d :=
    Nat.prod_primeFactors_of_squarefree (Squarefree.squarefree_of_dvd
      ((Nat.mem_divisors.mp h).1.trans divides) (squarefree_primorial Q))
  rw [prod_one_add]
  refine Finset.sum_bij' (fun d _ => d.primeFactors) (fun T _ => ∏ p∈T,p) ?_ ?_ code ?_ ?_
  · intro d hd
    have eq : M.primeFactors = S := Nat.primeFactors_prod (fun _ h => pr h)
    exact mem_powerset.mpr (eq ▸ Nat.primeFactors_mono (Nat.mem_divisors.mp hd).1 hm)
  · intro T hT
    exact Nat.mem_divisors.mpr ⟨prod_dvd_prod_of_subset _ _ _ (mem_powerset.mp hT),hm⟩
  · intro T hT
    exact Nat.primeFactors_prod (fun _ h => pr (mem_powerset.mp hT h))
  · intro d hd
    simp only [one_div,prod_inv_distrib]
    rw [← Nat.cast_prod,code d hd]

/-- Sifting only the primes in (x,y] costs the ratio of the logarithms of the
endpoints, uniformly for real endpoints. -/
theorem medium_prime_divisor_bound : ∃ C : ℝ, 0<C ∧ ∀ x y : ℝ, 2≤x → x≤y →
    let S := Nat.primesLE ⌊y⌋₊ \ Nat.primesLE ⌊x⌋₊
    ∑ d ∈ (∏ p ∈ S,p).divisors, (1:ℝ)/d ≤ C*(Real.log y / Real.log x) := by
  obtain ⟨b,mer⟩ := OMALib.Mertens.mertens2
  refine ⟨Real.exp (2*b),Real.exp_pos _,?_⟩
  intro x y hx xy S
  have lx := Real.log_pos (show 1<x by linarith)
  have ly := Real.log_pos (show 1<y by linarith)
  have sub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊y⌋₊ := by
    intro p hp
    obtain ⟨le,prime⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨le.trans (Nat.floor_le_floor xy),prime⟩
  have diff := Finset.sum_sdiff sub (f:=fun p : ℕ => (1:ℝ)/p)
  have lower := (abs_le.mp (mer x hx)).1
  have upper := (abs_le.mp (mer y (hx.trans xy))).2
  have bound : ∑ p∈S, (1:ℝ)/p ≤ 2*b + (Real.log (Real.log y)-Real.log (Real.log x)) := by
    dsimp only [S]
    linarith
  rw [prime_set_divisor_sum S sdiff_subset]
  calc
    _ ≤ ∏ p ∈ S, Real.exp ((1:ℝ)/p) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro p _; simpa [add_comm] using Real.add_one_le_exp ((1:ℝ)/p)
    _ = Real.exp (∑ p ∈ S, (1:ℝ)/p) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2*b+(Real.log (Real.log y)-Real.log (Real.log x))) := Real.exp_le_exp.mpr bound
    _ = _ := by rw [Real.exp_add,Real.exp_sub,Real.exp_log ly,Real.exp_log lx]

/-- The medium-prime sieve of Bedert §7 has absolute bounded divisor mass.
Here x=√(log N), so its upper endpoint x^40 is (log N)^20. -/
theorem medium_sieve_constant : ∃ D : ℝ, 0<D ∧ ∀ x:ℝ, 2≤x →
    let S := Nat.primesLE ⌊x^40⌋₊ \ Nat.primesLE ⌊x⌋₊
    ∑ d ∈ (∏ p ∈ S,p).divisors, (1:ℝ)/d ≤ D := by
  obtain ⟨C,hC,bound⟩ := medium_prime_divisor_bound
  refine ⟨C*40,by positivity,fun x hx => ?_⟩
  have h := bound x (x^40) hx (by
    calc x = x^1 := by simp
         _ ≤ x^40 := pow_le_pow_right₀ (by linarith) (by decide))
  simpa [Real.log_pow, (Real.log_pos (show 1<x by linarith)).ne'] using h

end BedertSieve
end

section

namespace BedertSieve
open Finset MeasureTheory AddCircle GreenBourgain
open scoped Classical

/-- The product of the medium primes is coprime to the multiplier exactly when
each such prime avoids it. This equivalence covers signed multipliers. -/
theorem medium_coprime_iff (L Q : ℕ) (n : ℤ) :
    let S := Nat.primesLE Q \ Nat.primesLE L
    (∏ p∈S,p).Coprime n.natAbs ↔ ∀p:ℕ, p.Prime → L<p → p≤Q → ¬(p:ℤ) ∣ n := by
  intro S
  have pr {p:ℕ} (h:p∈S) := Nat.prime_of_mem_primesLE (mem_sdiff.mp h).1
  constructor
  · intro cop p hp lq pq div
    have mem : p∈S := mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨pq,hp⟩,
      fun h => (not_le_of_gt lq) (Nat.mem_primesLE.mp h).1⟩
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes cop (dvd_prod_of_mem _ mem) (Int.natCast_dvd.mp div))
  · intro rough
    by_contra h
    obtain ⟨p,hp,div,absdiv⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    obtain ⟨q,hq,dvdq⟩ := (hp.prime.dvd_finsetProd_iff _).mp div
    have eq := (Nat.prime_dvd_prime_iff_eq hp (pr hq)).mp dvdq
    subst q
    obtain ⟨pq,npl⟩ := mem_sdiff.mp hq
    have lq : L<p := lt_of_not_ge (fun pl => npl (Nat.mem_primesLE.mpr ⟨pl,hp⟩))
    exact rough p hp lq (Nat.mem_primesLE.mp pq).1 (Int.natCast_dvd.mpr absdiv)

/-- Bound the true circle L1 norm of the arbitrary-modulus Möbius dilation sieve
by its divisor mass, and identify all its Fourier coefficients. -/
theorem sieve_signal (M : ℕ) (hm : M ≠ 0) (B : Finset ℤ) (nz : ∀ b∈B,b≠0) :
    let g := fun x:UnitAddCircle => ∑ d ∈ M.divisors,
      ((ArithmeticFunction.moebius d : ℂ)*weight d)*base ((d:ℤ) • x)
    let F := signal B g
    Integrable F haarAddCircle ∧ mass F ≤
        (∑ d∈M.divisors, (1:ℝ)/d) * mass (signal B base) ∧
      ∀ k:ℤ, fourierCoeff F k = ∑ b∈B, if b∣k ∧ M.Coprime (k/b).natAbs then weight (k/b).natAbs else 0 := by
  intro g F
  let a (d:ℕ) := (ArithmeticFunction.moebius d:ℂ)*weight d
  have baseint := base_memLp.integrable (by norm_num)
  have nzD {d:ℕ} (hd:d∈M.divisors) : (d:ℤ)≠0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have gint : Integrable g haarAddCircle := by
    apply integrable_finsetSum
    intro d hd
    exact ((Measure.measurePreserving_zsmul haarAddCircle (nzD hd)).integrable_comp
      baseint.aestronglyMeasurable).mpr baseint |>.const_mul _
  refine ⟨signal_int B nz g gint,?_,?_⟩
  · let f := signal B base
    have fi := signal_int B nz base baseint
    have swap : F = fun x => ∑ d∈M.divisors, a d*f ((d:ℤ) • x) := by
      funext x
      simp only [F,signal,g,a,f,Finset.mul_sum,smul_smul]
      rw [sum_comm]; congr! 5; ring
    rw [swap,sum_mul]
    refine (mass_sum M.divisors _ (fun d hd => ?_)).trans (sum_le_sum (fun d hd => ?_))
    · exact (((Measure.measurePreserving_zsmul haarAddCircle (nzD hd)).integrable_comp
        fi.aestronglyMeasurable).mpr fi).const_mul _
    · rw [mass_const,mass_dilate f fi _ (nzD hd)]
      exact mul_le_mul_of_nonneg_right (weight_moebius_bound _) (mass_nonnegative _)
  · intro k
    rw [show fourierCoeff F k = _ from Green1Circle.fourierCoeff_dilates g gint B nz k]
    apply sum_congr rfl
    intro b _
    rw [Green1Circle.fourierCoeff_sieve_signed base baseint weight base_coeff hm (k/b)]
    split_ifs <;> simp_all

/-- At Bedert's two cutoffs, the actual medium-sieved signal has uniformly bounded
circle integral relative to the unsieved signal and exactly the required signed coefficients. -/
theorem medium_signal_uniform : ∃ D : ℝ, 0<D ∧ ∀ x:ℝ, 2≤x → ∀ B:Finset ℤ,
    (∀ b∈B,b≠0) → ∃ F : UnitAddCircle → ℂ, Integrable F haarAddCircle ∧
      mass F ≤ D*mass (signal B base) ∧ ∀ k:ℤ, fourierCoeff F k = ∑ b∈B,
        if b∣k ∧ (∀p:ℕ, p.Prime → ⌊x⌋₊<p → p≤⌊x^40⌋₊ → ¬(p:ℤ)∣k/b)
        then weight (k/b).natAbs else 0 := by
  classical
  obtain ⟨D,pos,bound⟩ := medium_sieve_constant
  refine ⟨D,pos,?_⟩
  intro x hx B nz
  let S := Nat.primesLE ⌊x^40⌋₊ \ Nat.primesLE ⌊x⌋₊
  let M := ∏ p∈S,p
  have hm : M≠0 := prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1).ne_zero)
  obtain ⟨inte,massle,coeff⟩ := sieve_signal M hm B nz
  refine ⟨_,inte,massle.trans (mul_le_mul_of_nonneg_right (bound x hx) (mass_nonnegative _)),fun k => ?_⟩
  exact (coeff k).trans (Finset.sum_congr rfl (fun b _ => by
    simp only [show M.Coprime (k/b).natAbs ↔ _ from medium_coprime_iff ⌊x⌋₊ ⌊x^40⌋₊ (k/b)]))

end BedertSieve
end

section

namespace BedertSieve
open Finset MeasureTheory AddCircle GreenBourgain
open scoped Classical

/-- The full small-prime sieve is the same exact projected coefficient construction
and has at most logarithmic divisor mass. -/
theorem full_signal_uniform : ∃ C : ℝ, 0<C ∧ ∀ Q : ℕ, 2≤Q → ∀ B:Finset ℤ,
    (∀ b∈B,b≠0) → ∃ F : UnitAddCircle → ℂ, Integrable F haarAddCircle ∧
      mass F ≤ C*Real.log Q*mass (signal B base) ∧ ∀ k:ℤ, fourierCoeff F k = ∑ b∈B,
        if b∣k ∧ (∀p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣k/b)
        then weight (k/b).natAbs else 0 := by
  obtain ⟨C,pos,bound⟩ := primorial_divisor_bound
  refine ⟨C,pos,?_⟩
  intro Q hQ B nz
  obtain ⟨inte,est,coeff⟩ := sieve_signal (primorial Q) (primorial_ne_zero _) B nz
  refine ⟨_,inte,est.trans (mul_le_mul_of_nonneg_right (bound Q hQ) (mass_nonnegative _)),?_⟩
  intro k
  refine (coeff k).trans (sum_congr rfl (fun b _ => ?_))
  have iff : (primorial Q).Coprime (k/b).natAbs ↔ ∀p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣k/b := by
    have e := medium_coprime_iff 0 Q (k/b)
    simpa only [Nat.primesLE_zero, sdiff_empty,←primorial_eq_prod_primesLE] using
      e.trans ⟨fun h p hp hq => h p hp hp.pos hq,fun h p hp _ hq => h p hp hq⟩
  simp only [iff]

end BedertSieve
end

section

namespace GreenOneProjection
open AddCircle MeasureTheory Finset

theorem translate_coeff (f : UnitAddCircle → ℂ) (t : UnitAddCircle) (n : ℤ) :
    fourierCoeff (fun x => f (t+x)) n = fourier n t * fourierCoeff f n := by
  simp only [fourierCoeff,smul_eq_mul]
  rw [←integral_const_mul, ←integral_add_left_eq_self (μ := haarAddCircle)
      (fun x => fourier n t * (fourier (-n) x * f x)) t]
  apply integral_congr_ae
  filter_upwards with x
  rw [BedertTest.char_translate,←mul_assoc,←mul_assoc,←fourier_add]
  simp only [add_neg_cancel, fourier_zero, one_mul]

theorem torsion_sum (q : ℕ) (pos : 0 < q) (r n : ℤ) :
    let t : UnitAddCircle := ↑(1/(q:ℝ))
    ∑ i ∈ range q, fourier (-r) (i • t) * fourier n (i • t) =
      if (q:ℤ) ∣ n-r then (q:ℂ) else 0 := by
  intro t
  have power (m : ℤ) (i : ℕ) : fourier m (i • t) = (fourier m t)^i := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul,BedertTest.char_translate,ih,pow_succ]
  have p (i : ℕ) : fourier (-r) (i • t) * fourier n (i • t) = (fourier (n-r) t)^i := by
    rw [mul_comm,←fourier_add,←sub_eq_add_neg,power]
  simp_rw [p]
  have modl : fourier (n-r) t = 1 ↔ (q:ℤ) ∣ n-r := by
    simpa only [sub_zero,fourier_zero] using (BedertTest.phase_eq_iff pos (n-r) 0)
  split_ifs with dv
  · simp [modl.mpr dv]
  · have z : q • t = 0 := by
      rw [←show addOrderOf t = q from addOrderOf_period_div pos]
      exact addOrderOf_nsmul_eq_zero _
    have endp : (fourier (n-r) t)^q = 1 := by rw [←power,z,fourier_eval_zero]
    exact (mul_eq_zero.mp ((geom_sum_mul (fourier (n-r) t) q).trans (sub_eq_zero.mpr endp))).resolve_right
      (sub_ne_zero.mpr (modl.not.mpr dv))

/-- Averaging translates gives an L¹ contraction with the exact residue-class mask.
This is the Fourier projection used in §7 of Bedert's sum-free subset proof. -/
theorem residue_projection (q : ℕ) (pos : 0 < q) (r : ℤ) (f : UnitAddCircle → ℂ)
    (intg : Integrable f haarAddCircle) :
    ∃ g : UnitAddCircle → ℂ, Integrable g haarAddCircle ∧
      (∀ n, fourierCoeff g n = if (q:ℤ) ∣ n-r then fourierCoeff f n else 0) ∧
      (∫ x, ‖g x‖ ∂haarAddCircle) ≤ ∫ x, ‖f x‖ ∂haarAddCircle := by
  let t : UnitAddCircle := ↑(1/(q:ℝ))
  let term (i : ℕ) (x : UnitAddCircle) := fourier (-r) (i • t) * f (i • t + x)
  let μ : Measure UnitAddCircle := haarAddCircle
  have tr (i : ℕ) : Integrable (fun x => f (i • t+x)) μ :=
    ((measurePreserving_add_left μ (i • t)).integrable_comp intg.aestronglyMeasurable).mpr intg
  have ti (i : ℕ) : Integrable (term i) μ := (tr i).const_mul _
  let F := ∑ i ∈ range q, term i
  have fi : Integrable F μ := integrable_finsetSum' _ fun i _ => ti i
  refine ⟨fun x => (q:ℂ)⁻¹*F x,fi.const_mul _,?_,?_⟩
  · intro n
    rw [fourierCoeff.const_mul]
    have cf := congrFun (fourierCoeff.sum (range q) term (fun i _ => ti i)) n
    change fourierCoeff F n = _ at cf
    rw [cf,Finset.sum_apply]
    have row (i : ℕ) : fourierCoeff (term i) n =
        (fourier (-r) (i • t)*fourier n (i • t))*fourierCoeff f n := by
      dsimp only [term]
      rw [fourierCoeff.const_mul, translate_coeff,mul_assoc]
    simp_rw [row]
    rw [←sum_mul, torsion_sum q pos r n]
    split_ifs
    · rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast pos.ne'),one_mul]
    · simp
  · have size (i : ℕ) (x : UnitAddCircle) : ‖term i x‖ = ‖f (i • t+x)‖ := by
      simp only [term,norm_mul,fourier_apply,Circle.norm_coe,one_mul]
    have eq (i : ℕ) : (∫ x, ‖term i x‖ ∂μ) = ∫ x, ‖f x‖ ∂μ := by
      simp_rw [size]
      exact integral_add_left_eq_self (μ := μ) (fun x => ‖f x‖) (i • t)
    have bound : (∫ x, ‖F x‖ ∂μ) ≤ (q:ℝ)*(∫ x, ‖f x‖ ∂μ) := by
      calc
        _ ≤ ∫ x, ∑ i ∈ range q, ‖term i x‖ ∂μ := by
          apply integral_mono fi.norm (integrable_finsetSum _ fun i _ => (ti i).norm)
          intro x
          simpa only [F,Finset.sum_apply] using norm_sum_le (range q) (fun i => term i x)
        _ = _ := by rw [integral_finsetSum _ fun i _ => (ti i).norm]; simp [eq]
    change (∫ x, ‖(q:ℂ)⁻¹ * F x‖ ∂μ) ≤ _
    simp_rw [norm_mul,norm_inv,Complex.norm_natCast]
    rw [integral_const_mul]
    calc _ ≤ (q:ℝ)⁻¹*((q:ℝ)* ∫ x, ‖f x‖ ∂μ) := mul_le_mul_of_nonneg_left bound (by positivity)
         _ = _ := by rw [←mul_assoc, inv_mul_cancel₀ (by exact_mod_cast pos.ne'),one_mul]
end GreenOneProjection
end

section

namespace GreenOneProjection
open AddCircle MeasureTheory Finset

/-- The product of two Dirichlet kernels is a flat-top Fourier multiplier.
With a wide interval of length 3T and a short interval of length T it gives
the de la Vallée-Poussin truncation needed in Bedert §6, with L¹ norm at most 2. -/
theorem cutoff_kernel (T : ℕ) (pos : 0 < T) :
    ∃ K : UnitAddCircle → ℂ, Continuous K ∧
    (∫ x, ‖K x‖ ∂haarAddCircle) ≤ 2 ∧
    (∀ n, ‖fourierCoeff K n‖ ≤ 1) ∧
    (∀ n : ℤ, n.natAbs ≤ T → fourierCoeff K n = 1) ∧
    (∀ n : ℤ, 2*T ≤ n.natAbs → fourierCoeff K n = 0) := by
  classical
  let A := Ico (-(T:ℤ)) (2*(T:ℤ))
  let B := Ico (0:ℤ) T
  let D (S : Finset ℤ) (x : UnitAddCircle) := ∑ a ∈ S, fourier a x
  have cont (S : Finset ℤ) : Continuous (D S) := continuous_finsetSum _ fun a _ => (fourier a).continuous
  have ai : A.card = 3*T := by simp only [A,Int.card_Ico]; omega
  have bi : B.card = T := by simp [B]
  let K (x : UnitAddCircle) := (T:ℂ)⁻¹ * (D A x * star (D B x))
  have ct : Continuous K := continuous_const.mul ((cont A).mul (cont B).star)
  have itg {f : UnitAddCircle → ℝ} (cf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  have square (S : Finset ℤ) : (∫ x, ‖D S x‖^2 ∂haarAddCircle) = S.card := by
    simpa [D] using BedertTest.trig_square S (fun _ => (1:ℂ))
  have bound : (∫ x, ‖K x‖ ∂haarAddCircle) ≤ 2 := by
    have pt (x : UnitAddCircle) : ‖K x‖ ≤ (T:ℝ)⁻¹ * ((‖D A x‖^2+‖D B x‖^2)/2) := by
      simp only [K,norm_mul,norm_star,norm_inv,Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [sq_nonneg (‖D A x‖-‖D B x‖)]
    calc
      _ ≤ _ := integral_mono (itg ct.norm) (itg (continuous_const.mul
        ((((cont A).norm.pow 2).add ((cont B).norm.pow 2)).div_const _))) pt
      _ = _ := by
        change (∫ x, (T:ℝ)⁻¹*((‖D A x‖^2+‖D B x‖^2)/2) ∂haarAddCircle) = 2
        have sqint (S : Finset ℤ) : Integrable (fun x => ‖D S x‖^2) haarAddCircle := itg ((cont S).norm.pow 2)
        rw [integral_const_mul,integral_div,integral_add (sqint A) (sqint B),
          square,square,ai,bi]
        push_cast
        field_simp
        ring
  let sel (n : ℤ) := B.filter (fun b => n+b ∈ A)
  have repr : K = fun x => (T:ℂ)⁻¹*(∑ b ∈ B, ∑ a ∈ A, fourier (a-b) x) := by
    funext x
    dsimp only [K,D]
    congr 1
    simp only [Complex.star_def,map_sum, mul_sum, sum_mul]
    apply sum_congr rfl
    intro b hb
    apply sum_congr rfl
    intro a ha
    simp only [sub_eq_add_neg,fourier_add,fourier_neg]
  have ci {f : UnitAddCircle → ℂ} (cf : Continuous f) : Integrable f haarAddCircle :=
    integrableOn_univ.mp (cf.continuousOn.integrableOn_compact isCompact_univ)
  have coeff (n : ℤ) : fourierCoeff K n = (T:ℂ)⁻¹*(sel n).card := by
    rw [repr,fourierCoeff.const_mul]
    congr 1
    let modes (b a : ℤ) (x : UnitAddCircle) := fourier (a-b) x
    let rows (b : ℤ) := ∑ a ∈ A, modes b a
    have cd (a b : ℤ) : Continuous (modes b a) := (fourier (a-b)).continuous
    have cr (b : ℤ) : Continuous (rows b) := by
      have ee : rows b = fun x => ∑ a ∈ A, modes b a x := by funext x; simp only [rows,Finset.sum_apply]
      rw [ee]
      exact continuous_finsetSum A fun a _ => cd a b
    have id : (fun x => ∑ b ∈ B, ∑ a ∈ A, fourier (a-b) x) = ∑ b ∈ B, rows b := by
      funext x
      simp only [Finset.sum_apply,rows,modes]
    rw [id, fourierCoeff.sum B rows (fun b _ => ci (cr b)),Finset.sum_apply]
    have row (b : ℤ) : fourierCoeff (rows b) n = if n+b ∈ A then 1 else 0 := by
      rw [show rows b = _ from rfl, fourierCoeff.sum A (modes b) (fun a _ => ci (cd a b)),
        Finset.sum_apply]
      have chr (a : ℤ) : fourierCoeff (modes b a) n = if n+b=a then 1 else 0 := by
        have h := congrFun (@fourierCoeff_fourier (1:ℝ) _ (a-b)) n
        simpa only [modes,Pi.single_apply,eq_sub_iff_add_eq] using h
      simp_rw [chr]
      simp
    simp_rw [row]
    simp [sel]
  refine ⟨K,ct,bound,?_,?_,?_⟩
  · intro n
    rw [coeff,norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_natCast,←div_eq_inv_mul]
    apply (div_le_one (by exact_mod_cast pos)).mpr
    exact_mod_cast (card_le_card (filter_subset _ B)).trans_eq bi
  · intro n hn
    have eq : sel n = B := by
      apply filter_true_of_mem
      intro b hb
      obtain ⟨h0,h1⟩ := mem_Ico.mp hb
      apply mem_Ico.mpr
      omega
    rw [coeff,eq,bi,inv_mul_cancel₀ (by exact_mod_cast pos.ne')]
  · intro n hn
    have eq : sel n = ∅ := by
      apply filter_false_of_mem
      intro b hb aa
      obtain ⟨h0,h1⟩ := mem_Ico.mp hb
      obtain ⟨h2,h3⟩ := mem_Ico.mp aa
      omega
    simp [coeff,eq]
end GreenOneProjection
end

section

namespace GreenOneProjection
open MeasureTheory AddCircle ContinuousLinearMap
open scoped Convolution

/-- Convolution on the unit circle multiplies Fourier coefficients, and its
L¹ norm is bounded by the product of the L¹ norms. -/
theorem convolution_multiplier (K f : UnitAddCircle → ℂ)
    (ik : Integrable K haarAddCircle) (hf : Integrable f haarAddCircle) :
    ∃ g : UnitAddCircle → ℂ, Integrable g haarAddCircle ∧
      (∀ n, fourierCoeff g n = fourierCoeff K n * fourierCoeff f n) ∧
      (∫ x, ‖g x‖ ∂haarAddCircle) ≤ (∫ x, ‖K x‖ ∂haarAddCircle) * (∫ x, ‖f x‖ ∂haarAddCircle) := by
  let μ : Measure UnitAddCircle := haarAddCircle
  let g := K ⋆[mul ℂ ℂ, μ] f
  have ig : Integrable g μ := ik.integrable_convolution (mul ℂ ℂ) hf
  refine ⟨g,ig,?_,?_⟩
  · intro n
    let twist (u : UnitAddCircle → ℂ) (x : UnitAddCircle) := fourier (-n) x * u x
    have twistI (u : UnitAddCircle → ℂ) (iu : Integrable u μ) : Integrable (twist u) μ :=
      iu.fourier_smul (-n)
    have eq : twist g = (twist K ⋆[mul ℂ ℂ, μ] twist f) := by
      funext x
      simp only [twist,g,convolution_mul,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      have add : fourier (-n) x = fourier (-n) t * fourier (-n) (x-t) := by
        rw [←BedertTest.char_translate,add_sub_cancel]
      rw [add]
      ring
    change (∫ x, twist g x ∂μ) = (∫ x, twist K x ∂μ) * (∫ x, twist f x ∂μ)
    rw [eq]
    exact integral_convolution (mul ℂ ℂ) (twistI K ik) (twistI f hf)
  · let nk := fun x => ‖K x‖
    let nf := fun x => ‖f x‖
    let G := nk ⋆[mul ℝ ℝ, μ] nf
    have upper : Integrable G μ := ik.norm.integrable_convolution (mul ℝ ℝ) hf.norm
    calc _ ≤ ∫ x, G x ∂μ := by
           apply integral_mono ig.norm upper
           intro x
           simpa only [G,g,nk,nf,convolution_mul,norm_mul] using
             norm_integral_le_integral_norm (μ:=μ) (fun t => K t * f (x-t))
         _ = _ := integral_convolution (mul ℝ ℝ) ik.norm hf.norm

/-- Uniform approximation by a flat-top multiplier. The Fourier coefficients
below T are retained exactly, and those at or above 2T vanish. -/
theorem cutoff_function (T : ℕ) (pos : 0<T) (f : UnitAddCircle → ℂ)
    (hf : Integrable f haarAddCircle) :
    ∃ g : UnitAddCircle → ℂ, Integrable g haarAddCircle ∧
      (∫ x, ‖g x‖ ∂haarAddCircle) ≤ 2*(∫ x, ‖f x‖ ∂haarAddCircle) ∧
      (∀ n, ‖fourierCoeff g n‖ ≤ ‖fourierCoeff f n‖) ∧
      (∀ n : ℤ, n.natAbs ≤ T → fourierCoeff g n = fourierCoeff f n) ∧
      (∀ n : ℤ, 2*T ≤ n.natAbs → fourierCoeff g n = 0) := by
  obtain ⟨K,ck,bound,amp,low,high⟩ := cutoff_kernel T pos
  have ik : Integrable K haarAddCircle :=
    integrableOn_univ.mp (ck.continuousOn.integrableOn_compact isCompact_univ)
  obtain ⟨g,ig,prod,bg⟩ := convolution_multiplier K f ik hf
  refine ⟨g,ig,bg.trans (mul_le_mul_of_nonneg_right bound (integral_nonneg fun _ => norm_nonneg _)),?_,?_,?_⟩
  · intro n
    rw [prod,norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (amp n)
  · intro n hn
    rw [prod,low n hn,one_mul]
  · intro n hn
    rw [prod,high n hn,zero_mul]
end GreenOneProjection
end
end

section
namespace GreenOneProjection
open AddCircle MeasureTheory Finset ContinuousLinearMap
open scoped Convolution

/-- The flat cutoff gives a genuine finite polynomial with an L¹ bound for
every integrable input. The fixed Fourier coefficients need no regularity of the input. -/
theorem cutoff_polynomial (T : ℕ) (pos : 0<T) (f : UnitAddCircle → ℂ)
    (hf : Integrable f haarAddCircle) :
    let W := Ioo (-2*(T:ℤ)) (2*(T:ℤ))
    ∃ w : ℤ → ℂ, (∀ i, ‖w i‖ ≤ 1) ∧ (∀ i : ℤ, i.natAbs ≤ T → w i = 1) ∧
        (∀ i ∉ W, w i=0) ∧
        (∫ x : UnitAddCircle, ‖∑ i ∈ W, w i*fourierCoeff f i*fourier i x‖ ∂haarAddCircle)
        ≤ 2*(∫ x, ‖f x‖ ∂haarAddCircle) := by
  intro W
  obtain ⟨K,cK,bnd,cap,lo,hi⟩ := cutoff_kernel T pos
  let kc : C(UnitAddCircle,ℂ) := ⟨K,cK⟩
  let w := fourierCoeff K
  have tail (i : ℤ) (ni : i ∉ W) : w i = 0 := by
    apply hi
    change i ∉ Ioo (-2*(T:ℤ)) (2*(T:ℤ)) at ni
    simp only [mem_Ioo,not_and_or,not_lt] at ni
    omega
  refine ⟨w,cap,lo,tail,?_⟩
  have sm : Summable (fourierCoeff (kc : UnitAddCircle → ℂ)) :=
    (hasSum_sum_of_ne_finset_zero tail).summable
  have rep (x : UnitAddCircle) : K x = ∑ i ∈ W, w i * fourier i x := by
    have h := has_pointwise_sum_fourier_series_of_summable (f:=kc) sm x
    apply h.unique
    apply hasSum_sum_of_ne_finset_zero
    intro i h
    change w i • fourier i x = 0
    rw [tail i h,zero_smul]
  let μ : Measure UnitAddCircle := haarAddCircle
  let G := f ⋆[mul ℂ ℂ, μ] K
  have intK : Integrable K μ := integrableOn_univ.mp (cK.continuousOn.integrableOn_compact isCompact_univ)
  have fg (x : UnitAddCircle) : G x = ∑ i ∈ W, w i * fourierCoeff f i * fourier i x := by
    have chr (i : ℤ) (t : UnitAddCircle) : fourier i (x-t) = fourier i x * fourier (-i) t := by
      rw [sub_eq_add_neg,BedertTest.char_translate]
      simp only [fourier_apply,zsmul_neg,neg_zsmul]
    have pt (t : UnitAddCircle) : f t*K (x-t) =
        ∑ i ∈ W, (w i*fourier i x) * (fourier (-i) t*f t) := by
      rw [rep,mul_sum]
      apply sum_congr rfl
      intro i _
      rw [chr]
      ring
    change (∫ t, f t*K (x-t) ∂μ) = _
    simp_rw [pt]
    have it (i : ℤ) : Integrable (fun t => (w i*fourier i x)*(fourier (-i) t*f t)) μ :=
      (hf.fourier_smul (-i)).const_mul _
    rw [integral_finsetSum _ (fun i _ => it i)]
    apply sum_congr rfl
    intro i _
    rw [integral_const_mul]
    change (w i*fourier i x)*fourierCoeff f i = _
    ring
  have gI : Integrable G μ := hf.integrable_convolution (mul ℂ ℂ) intK
  let A := (fun x => ‖f x‖) ⋆[mul ℝ ℝ, μ] (fun x => ‖K x‖)
  have aI : Integrable A μ := hf.norm.integrable_convolution (mul ℝ ℝ) intK.norm
  calc
    _ = ∫ x, ‖G x‖ ∂μ := by simp only [μ,fg]
    _ ≤ ∫ x, A x ∂μ := by
      apply integral_mono gI.norm aI
      intro x
      simpa only [A,G,convolution_mul,norm_mul] using
        norm_integral_le_integral_norm (μ:=μ) (fun t => f t*K (x-t))
    _ = (∫ x, ‖f x‖ ∂μ)*(∫ x, ‖K x‖ ∂μ) := integral_convolution (mul ℝ ℝ) hf.norm intK.norm
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right bnd (integral_nonneg fun _=>norm_nonneg _)
end GreenOneProjection
end

section
namespace BedertSelection

/-- The selection step in Bedert, Lemma 8.1. Minimize a rank among the
labels below x whose size is still at least t times the next threshold. -/
theorem select_predecessor {X : Type*} [Preorder X] (rank : X → ℕ)
    (rank_mono : StrictMono rank) (w : X → ℝ) {t b : ℝ} (ht : 1 ≤ t) (hb : 1 ≤ b)
    (pred : ∀ z, t ≤ w z → ∃ y < z, w z ≤ t*w y)
    (x : X) (hx : t*(t*b) ≤ w x) :
    ∃ y < x, b ≤ w y ∧ t*w y < w x := by
  have pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have tb : t ≤ t*b := by simpa using mul_le_mul_of_nonneg_left hb pos.le
  have tbx : t*b ≤ w x := le_trans (by
    simpa using mul_le_mul_of_nonneg_right ht (mul_nonneg pos.le (zero_le_one.trans hb))) hx
  let P := {z : X | z ≤ x ∧ t*b ≤ w z}
  have wf : WellFounded (fun (z v : X) => rank z < rank v) := (measure rank).wf
  obtain ⟨v,hv,minimal⟩ := wf.has_min P ⟨x, le_rfl,tbx⟩
  obtain ⟨y,less,loss⟩ := pred v (tb.trans hv.2)
  have yx : y < x := lt_of_lt_of_le less hv.1
  have below : w y < t*b := by
    by_contra! hn
    exact minimal y ⟨yx.le,hn⟩ (rank_mono less)
  exact ⟨y,yx,(le_of_mul_le_mul_left (hv.2.trans loss) pos),
    (mul_lt_mul_of_pos_left below pos).trans_le hx⟩

/-- Bedert's chain-selection argument with an explicit number of levels.
For a seed of size at least (t²)^j, the result has j+1 labels. -/
theorem select_chain {X : Type*} [Preorder X] (rank : X → ℕ)
    (rank_mono : StrictMono rank) (w : X → ℝ) {t : ℝ} (ht : 1 ≤ t)
    (pred : ∀ z, t ≤ w z → ∃ y < z, w z ≤ t*w y)
    (j : ℕ) (x : X) (large : (t*t)^j ≤ w x) :
    ∃ f : Fin (j+1) → X, f (Fin.last j) = x ∧ StrictMono f ∧ 1 ≤ w (f 0) ∧
      ∀ i : Fin j, t*w (f i.castSucc) < w (f i.succ) := by
  have htt : 1 ≤ t*t := one_le_mul_of_one_le_of_one_le ht ht
  have build (k : ℕ) (z : X) (hz : (t*t)^k ≤ w z) :
      ∃ g : ℕ → X, g k=z ∧ 1 ≤ w (g 0) ∧
        ∀ i < k, g i < g (i+1) ∧ t*w (g i) < w (g (i+1)) := by
    induction k generalizing z with
    | zero => exact ⟨fun _ => z,rfl,by simpa using hz,fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ k ih =>
      have eq : (t*t)^(k+1) = t*(t*(t*t)^k) := by rw [pow_succ',mul_assoc]
      obtain ⟨y,less,lower,upper⟩ := select_predecessor rank rank_mono w ht
        (one_le_pow₀ htt) pred z (eq ▸ hz)
      obtain ⟨g,top,first,steps⟩ := ih y lower
      let g' (i : ℕ) := if i ≤ k then g i else z
      refine ⟨g',by simp [g'],by simpa [g'] using first,?_⟩
      intro i hi
      by_cases hik : i < k
      · simpa [g',hik.le,hik] using steps i hik
      · have ik : i=k := by omega
        subst i
        simpa [g',top] using And.intro less upper
  obtain ⟨g,top,first,steps⟩ := build j x large
  exact ⟨fun i => g i,top, Fin.strictMono_iff_lt_succ.mpr (fun i => (steps i i.isLt).1),first,
    fun i => (steps i i.isLt).2⟩

end BedertSelection

namespace BedertSelection

/-- Bedert, Lemma 8.1, with arbitrary finite residue labels and the coordinatewise
order on valuation vectors. A maximal residue is chosen separately at every level. -/
theorem fiber_chain {P R : Type*} [Fintype P] [Finite R] [Nonempty R]
    (card : (P → ℕ) → R → ℕ) {t : ℝ} (ht : 1 ≤ t)
    (pred : ∀ v r, (∀ s, card v s ≤ card v r) → t ≤ (card v r : ℝ) →
      ∃ u < v, ∃ s, (card v r : ℝ) ≤ t*card u s)
    (j : ℕ) (seed : P → ℕ) (r : R) (large : (t*t)^j ≤ (card seed r : ℝ)) :
    ∃ (v : Fin (j+1) → (P → ℕ)) (r : Fin (j+1) → R),
      v (Fin.last j) = seed ∧ StrictMono v ∧
      (∀ i s, card (v i) s ≤ card (v i) (r i)) ∧ 1 ≤ card (v 0) (r 0) ∧
      ∀ i : Fin j, t*card (v i.castSucc) (r i.castSucc) < (card (v i.succ) (r i.succ) : ℝ) := by
  classical
  choose pick maxim using fun u => Finite.exists_max (card u)
  let w (v : P → ℕ) := (card v (pick v) : ℝ)
  have dom (u : P → ℕ) (s : R) : (card u s : ℝ) ≤ w u := by dsimp [w]; exact_mod_cast maxim u s
  have step v (h : t ≤ w v) : ∃ u < v, w v ≤ t*w u := by
    obtain ⟨u,hu,s,hs⟩ := pred v (pick v) (maxim v) h
    exact ⟨u,hu,hs.trans (mul_le_mul_of_nonneg_left (dom u s) (zero_le_one.trans ht))⟩
  obtain ⟨v,top,mono,first,weights⟩ := select_chain (fun u : P → ℕ => ∑ p, u p)
    (fun u v huv => Finset.sum_lt_sum (fun i _ => huv.le i) (by simpa using (Pi.lt_def.mp huv).2)) w ht step j seed (large.trans (dom seed r))
  change 1 ≤ (card (v 0) (pick (v 0)) : ℝ) at first
  exact ⟨v,fun i => pick (v i),top,mono,fun i => maxim (v i),by exact_mod_cast first,weights⟩

/-- An explicit length bound: J=floor(log N/(16 log log N))+1. -/
theorem log_fiber_chain {P R : Type*} [Fintype P] [Finite R] [Nonempty R]
    (card : (P → ℕ) → R → ℕ) (N : ℕ) (hN : 1 < Real.log N)
    (pred : ∀ v r, (∀ s, card v s ≤ card v r) → (Real.log N)^4 ≤ (card v r : ℝ) →
      ∃ u < v, ∃ s, (card v r : ℝ) ≤ (Real.log N)^4*card u s)
    (seed : P → ℕ) (r : R) (large : Real.sqrt N ≤ (card seed r : ℝ)) :
    ∃ (J : ℕ) (v : Fin (J+1) → (P → ℕ)) (r : Fin (J+1) → R),
      (Real.log N)/(16*Real.log (Real.log N)) < J+1 ∧
      v (Fin.last J) = seed ∧ StrictMono v ∧
      (∀ i s, card (v i) s ≤ card (v i) (r i)) ∧ 1 ≤ card (v 0) (r 0) ∧
      ∀ i : Fin J, (Real.log N)^4*card (v i.castSucc) (r i.castSucc) <
        (card (v i.succ) (r i.succ) : ℝ) := by
  let X := Real.log N
  let Y := Real.log X
  let t := X^4
  let J := ⌊X/(16*Y)⌋₊
  have hx : 1 < X := hN
  have xp : 0 < X := zero_lt_one.trans hx
  have yp : 0 < Y := Real.log_pos hx
  have np : (0:ℝ)<N := by
    by_contra! h
    have eq : (N:ℝ)=0 := le_antisymm h (Nat.cast_nonneg _)
    rw [eq,Real.log_zero] at hN
    linarith
  have ht : 1 ≤ t := one_le_pow₀ hx.le
  have tp : 0<t := zero_lt_one.trans_le ht
  have jle : (J:ℝ)*(16*Y) ≤ X := (le_div_iff₀ (by positivity)).mp (Nat.floor_le (by positivity))
  have logt : Real.log (t*t) = 8*Y := by
    rw [Real.log_mul tp.ne' tp.ne']
    dsimp [t,Y]; rw [Real.log_pow]; ring
  have bound : (t*t)^J ≤ Real.sqrt N := by
    apply (Real.log_le_log_iff (pow_pos (mul_pos tp tp) _) (Real.sqrt_pos.mpr np)).mp
    rw [Real.log_pow,logt,Real.log_sqrt np.le]
    change (J:ℝ)*(8*Y) ≤ X/2
    linarith
  obtain ⟨v,r',top,mono,maximal,first,steps⟩ := fiber_chain card ht pred J seed r (bound.trans large)
  exact ⟨J,v,r',Nat.lt_floor_add_one _,top,mono,maximal,first,steps⟩

end BedertSelection

namespace BedertSelection

/-- The moduli of an increasing chain of valuation labels are divisible in order, and the
associated integer congruence classes are pairwise disjoint. The residue multipliers need
only avoid divisibility by the prime bases. -/
theorem valuation_cells {P : Type*} [Fintype P] {n : ℕ} (base : P → ℕ)
    (positive : ∀ p, 0 < base p) (v : Fin n → P → ℕ) (mono : StrictMono v)
    (r : Fin n → ℤ) (unit : ∀ i p, ¬(base p : ℤ) ∣ r i) :
    let V : Fin n → ℕ := fun i => ∏ p, base p^(v i p)
    let Q : Fin n → ℕ := fun i => ∏ p, base p^(v i p+1)
    (∀ i j, i ≤ j → Q i ∣ Q j) ∧
      Pairwise (fun i j => Disjoint {a : ℤ | a ≡ V i*r i [ZMOD Q i]}
        {a : ℤ | a ≡ V j*r j [ZMOD Q j]}) := by
  classical
  intro V Q
  let M := ∏ p, base p
  have cap (i : Fin n) : Q i = V i*M := by simp [V,Q,M,pow_succ,Finset.prod_mul_distrib]
  have ladder (i j : Fin n) (h : i ≤ j) : Q i ∣ Q j :=
    Finset.prod_dvd_prod_of_dvd _ _ fun p _ => pow_dvd_pow _ (Nat.succ_le_succ (mono.monotone h p))
  refine ⟨ladder,?_⟩
  have separate (i j : Fin n) (h : i < j) :
      Disjoint {a : ℤ | a ≡ V i*r i [ZMOD Q i]} {a : ℤ | a ≡ V j*r j [ZMOD Q j]} := by
    obtain ⟨le,p,lt⟩ := Pi.lt_def.mp (mono h)
    let W := ∏ p, base p^(v j p - v i p)
    have ratio : V j = V i*W := by
      dsimp [V,W]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q _
      rw [← pow_add,Nat.add_sub_of_le (le q)]
    have inM : base p ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    have inW : base p ∣ W := (dvd_pow_self _ (show v j p - v i p ≠ 0 by omega)).trans
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ p))
    have vi : (V i : ℤ) ≠ 0 := by
      have nz : V i ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun q _ => pow_ne_zero _ (positive q).ne')
      exact_mod_cast nz
    apply Set.disjoint_left.mpr
    intro a ha hb
    have qi : (Q i : ℤ) ∣ (Q j : ℤ) := by exact_mod_cast ladder i j h.le
    have clash := ha.symm.trans (hb.of_dvd qi)
    rw [cap,ratio,Nat.cast_mul,Nat.cast_mul,mul_assoc] at clash
    have eq := Int.ModEq.mul_left_cancel' vi clash
    have sub : (base p : ℤ) ∣ (M : ℤ) := by exact_mod_cast inM
    have div : (base p : ℤ) ∣ (W : ℤ) := by exact_mod_cast inW
    exact unit i p ((eq.of_dvd sub).dvd_iff.mpr (dvd_mul_of_dvd_left div _))
  intro i j ne
  rcases lt_or_gt_of_ne ne with h | h
  · exact separate i j h
  · exact (separate j i h).symm

end BedertSelection

namespace BedertSelection

/-- Passing from A to its symmetric frequency set increases a maximal residue slice
by a factor of at most two. No disjointness between A and its reflection is needed. -/
theorem symmetric_cell_size (A : Finset ℤ) (q r : ℤ) :
    let B := A ∪ A.image (fun x : ℤ => -x)
    let C (F : Finset ℤ) (s : ℤ) := (F.filter (fun x => x ≡ s [ZMOD q])).card
    C A r ≤ C B r ∧ C B r ≤ C A r + C A (-r) := by
  classical
  intro B C
  constructor
  · apply Finset.card_le_card
    intro x hx
    obtain ⟨ha,h⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ ha,h⟩
  · let pos := A.filter (fun x => x ≡ r [ZMOD q])
    let negs := A.filter (fun x => x ≡ -r [ZMOD q])
    have sub : B.filter (fun x => x ≡ r [ZMOD q]) ⊆ pos ∪ negs.image (fun x : ℤ => -x) := by
      intro x hx
      obtain ⟨ha,h⟩ := Finset.mem_filter.mp hx
      rcases Finset.mem_union.mp ha with hA | hn
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA,h⟩)
      · obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hn
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨y,Finset.mem_filter.mpr ⟨hy,by simpa using h.neg⟩,rfl⟩)
    exact (Finset.card_le_card sub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_image_le _))

/-- The residue classes of a Bedert chain meet his MPS growth condition on symmetric
frequencies whenever its original slices grow by a factor greater than twenty. -/
theorem symmetric_growth (A : Finset ℤ) (q r : ℕ → ℤ) (j : ℕ)
    (maximum : ∀ i ≤ j, (A.filter (fun x => x ≡ -(r i) [ZMOD q i])).card ≤
      (A.filter (fun x => x ≡ r i [ZMOD q i])).card)
    (growth : ∀ i < j, 20*(A.filter (fun x => x ≡ r i [ZMOD q i])).card <
      (A.filter (fun x => x ≡ r (i+1) [ZMOD q (i+1)])).card) :
    let B := A ∪ A.image (fun x : ℤ => -x)
    ∀ i < j, 10*(B.filter (fun x => x ≡ r i [ZMOD q i])).card <
      (B.filter (fun x => x ≡ r (i+1) [ZMOD q (i+1)])).card := by
  intro B i hi
  have small := (symmetric_cell_size A (q i) (r i)).2
  have big := (symmetric_cell_size A (q (i+1)) (r (i+1))).1
  have major := maximum i hi.le
  have next := growth i hi
  dsimp only at small big
  change 10*(B.filter _).card < (B.filter _).card
  dsimp only [B]
  omega

end BedertSelection

namespace BedertSelection

/-- The seed and predecessor estimates of Lemma 8.1 furnish the full combinatorial
inputs to Bedert's non-Archimedean test function, including growth for A union -A. -/
theorem structural_inputs {P R : Type*} [Fintype P] [Finite R] [Nonempty R]
    (base : P → ℕ) (positive : ∀ p, 0 < base p) (ρ : R → ℤ)
    (unit : ∀ s p, ¬(base p : ℤ) ∣ ρ s)
    (closed : ∀ s, ∃ t, ρ t ≡ -(ρ s) [ZMOD (∏ p, base p : ℕ)])
    (A : Finset ℤ) (N : ℕ) (hN : 1 < Real.log N) (twenty : 20 ≤ (Real.log N)^4) :
    let V := fun v : P → ℕ => ∏ p, base p^(v p)
    let Q := fun v : P → ℕ => ∏ p, base p^(v p+1)
    let card := fun v s => (A.filter (fun x => x ≡ V v*ρ s [ZMOD Q v])).card
    (∀ v r, (∀ s, card v s ≤ card v r) → (Real.log N)^4 ≤ (card v r : ℝ) →
      ∃ u < v, ∃ s, (card v r : ℝ) ≤ (Real.log N)^4*card u s) →
    (∃ seed r, Real.sqrt N ≤ (card seed r : ℝ)) →
    ∃ (J : ℕ) (q : Fin (J+1) → ℕ) (r : Fin (J+1) → ℤ),
      (Real.log N)/(16*Real.log (Real.log N)) < J+1 ∧
      (∀ i j, i ≤ j → q i ∣ q j) ∧
      Pairwise (fun i j => Disjoint {x : ℤ | x ≡ r i [ZMOD q i]}
                                     {x : ℤ | x ≡ r j [ZMOD q j]}) ∧
      let B := A ∪ A.image (fun x : ℤ => -x)
      let b := fun i => (B.filter fun x => x ≡ r i [ZMOD q i]).card
      1 ≤ b 0 ∧ ∀ i : Fin J, 10*b i.castSucc < b i.succ := by
  classical
  intro V Q card pred seed
  obtain ⟨z,t,large⟩ := seed
  obtain ⟨J,v,s,lower,_,mono,maximal,first,growth⟩ := log_fiber_chain card N hN pred z t large
  obtain ⟨order,disj⟩ := valuation_cells base positive v mono (fun i => ρ (s i)) (fun i => unit _)
  refine ⟨J,fun i => Q (v i),fun i => (V (v i) : ℤ)*ρ (s i),lower,order,disj,?_⟩
  intro B b
  have bound (i : Fin (J+1)) : card (v i) (s i) ≤ b i ∧ b i ≤ 2*card (v i) (s i) := by
    let u := v i
    let a : ℤ := V u*ρ (s i)
    obtain ⟨r',h'⟩ := closed (s i)
    have QQ : Q u = V u * ∏ p, base p := by simp [V,Q,pow_succ,Finset.prod_mul_distrib]
    have flip : (V u:ℤ)*ρ r' ≡ -a [ZMOD Q u] := by
      rw [QQ,Nat.cast_mul]
      simpa [a] using h'.mul_left' (c := (V u : ℤ))
    have revert : A.filter (fun x => x ≡ -a [ZMOD Q u]) =
        A.filter (fun x => x ≡ (V u:ℤ)*ρ r' [ZMOD Q u]) := by
      apply Finset.filter_congr
      intro x _
      exact ⟨fun h => h.trans flip.symm, fun h => h.trans flip⟩
    obtain ⟨lo,hi⟩ := symmetric_cell_size A (Q u) a
    dsimp only at hi
    rw [revert] at hi
    have hi' : b i ≤ card (v i) (s i) + card (v i) r' := hi
    exact ⟨lo,by have h := maximal i r'; omega⟩
  refine ⟨first.trans (bound 0).1,?_⟩
  intro i
  have grows : (20:ℝ)*card (v i.castSucc) (s i.castSucc) < card (v i.succ) (s i.succ) :=
    (mul_le_mul_of_nonneg_right twenty (Nat.cast_nonneg _)).trans_lt (growth i)
  have natg : 20*card (v i.castSucc) (s i.castSucc) < card (v i.succ) (s i.succ) := by exact_mod_cast grows
  obtain ⟨_,small⟩ := bound i.castSucc
  obtain ⟨big,_⟩ := bound i.succ
  omega

end BedertSelection

namespace BedertSelection

/-- Units modulo the product of the bases, represented by their ordinary integer values,
satisfy the two residue conditions of the structural theorem. -/
theorem unit_residue_conditions {P : Type*} [Fintype P] (base : P → ℕ) (gt : ∀ p, 1 < base p) :
    let M := ∏ p, base p
    let ρ := fun s : (ZMod M)ˣ => ((s : ZMod M).val : ℤ)
    (∀ s p, ¬ (base p : ℤ) ∣ ρ s) ∧
      ∀ s, ∃ t, ρ t ≡ -(ρ s) [ZMOD M] := by
  intro M ρ
  have nz : M ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun p _ => (zero_lt_one.trans (gt p)).ne')
  let : NeZero M := ⟨nz⟩
  constructor
  · intro s p div
    have d : base p ∣ (s : ZMod M).val := by dsimp [ρ] at div; exact_mod_cast div
    have e : base p ∣ M := Finset.dvd_prod_of_mem _ (Finset.mem_univ p)
    exact (gt p).ne' (Nat.eq_one_of_dvd_coprimes (ZMod.val_coe_unit_coprime s) d e)
  · intro s
    refine ⟨-s,?_⟩
    apply (ZMod.intCast_eq_intCast_iff _ _ _).mp
    simp [ρ]

end BedertSelection

open Finset

namespace BedertSelection

/-- Distinct valuations force dissociation by considering the term of smallest
valuation in a hypothetical equality of two disjoint subset sums (Bedert, Lemma 7.1). -/
theorem dissociated_of_valuation_injective (p : ℕ) (hp : p.Prime) (D : Finset ℤ)
    (nz : ∀ x ∈ D, x ≠ 0) (inj : Set.InjOn (fun x : ℤ => x.natAbs.factorization p) D) :
    AddDissociated (D : Set ℤ) := by
  classical
  by_contra h
  obtain ⟨T,U,hT,hU,disj,ne,sums⟩ := not_addDissociated_iff_exists_disjoint.mp h
  have exists' : (T ∪ U).Nonempty := by
    by_contra! he
    simp only [Finset.union_eq_empty] at he
    exact ne (he.1.trans he.2.symm)
  let ν := fun x : ℤ => x.natAbs.factorization p
  obtain ⟨x,hx,minimal⟩ := exists_min_image (T∪U) ν exists'
  have inside {y : ℤ} (hy : y ∈ T ∪ U) : y ∈ D :=
    (mem_union.mp hy).elim (fun h => hT h) (fun h => hU h)
  let q := (p^(ν x+1) : ℕ)
  have crit (y : ℤ) (hy : y ∈ T∪U) :
      (q:ℤ) ∣ y ↔ ν x+1 ≤ ν y := by
    rw [Int.natCast_dvd]
    exact hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr (nz _ (inside hy)))
  have except (y : ℤ) (hy : y ∈ T∪U) (hne : y ≠ x) : (q:ℤ) ∣ y := by
    apply (crit y hy).mpr
    exact Nat.succ_le_of_lt (lt_of_le_of_ne (minimal y hy)
      (fun hv => hne (inj (inside hx) (inside hy) hv).symm))
  have impossible (S W : Finset ℤ) (xS : x∈S) (xW : x∉W) (s : S ⊆ T∪U) (w : W ⊆ T∪U)
       (eqn : ∑ y∈S,y = ∑ y∈W,y) : False := by
    have hW : (q:ℤ) ∣ ∑y∈W,y := Finset.dvd_sum (fun y hy => except y (w hy) (ne_of_mem_of_not_mem hy xW))
    have hS : (q:ℤ) ∣ ∑y∈S.erase x,y := Finset.dvd_sum (fun y hy =>
      except y (s (mem_erase.mp hy).2) (mem_erase.mp hy).1)
    have diff := dvd_sub hW hS
    rw [sum_erase_eq_sub xS,eqn, sub_sub_cancel] at diff
    have := (crit x hx).mp diff
    omega
  rcases mem_union.mp hx with hxT|hxU
  · exact impossible T U hxT (disjoint_left.mp disj hxT) subset_union_left subset_union_right sums
  · exact impossible U T hxU (disjoint_left.mp disj.symm hxU) subset_union_right subset_union_left sums.symm

/-- The number of different valuations at each prime is at most the additive dimension. -/
theorem valuation_card_le (A : Finset ℤ) (k : ℕ) (nz : ∀ x∈A, x≠0)
    (dim : ∀ D : Finset ℤ, D⊆A → AddDissociated (D : Set ℤ) → D.card≤k)
    (p : ℕ) (hp : p.Prime) : (A.image fun x => x.natAbs.factorization p).card ≤ k := by
  classical
  let ν := fun x : ℤ => x.natAbs.factorization p
  obtain ⟨D,sub,inj,img⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn (f:=ν)
    (A : Set ℤ) (A.image ν) (fun _ hy => by simpa [Finset.mem_image] using hy)
  change (A.image ν).card ≤ k
  rw [← img, Finset.card_image_of_injOn inj]
  exact dim D sub (dissociated_of_valuation_injective p hp D (fun x hx => nz x (sub hx)) inj)

end BedertSelection

open Finset

namespace BedertSelection

/-- Removing all prime powers at the selected primes leaves a unit residue. -/
theorem valuation_unit_cover (Q : ℕ) (x : ℤ) (nz : x ≠ 0) :
    let P := ↥(Nat.primesLE Q)
    let v := fun p : P => x.natAbs.factorization p
    ∃ r : (ZMod (primorial Q))ˣ, x ≡ ((∏ p : P, (p:ℕ)^v p : ℕ) : ℤ) *
      ((r : ZMod (primorial Q)).val : ℤ) [ZMOD (∏ p : P, (p:ℕ)^(v p+1) : ℕ)] := by
  classical
  intro P v
  let V := ∏ p : P, (p:ℕ)^v p
  have prime (p : P) : (p:ℕ).Prime := Nat.prime_of_mem_primesLE p.property
  have proj (p : P) : (p:ℕ)^v p ∣ x.natAbs :=
    ((prime p).pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr nz)).2 le_rfl
  have prod_dvd : V ∣ x.natAbs := Fintype.prod_dvd_of_isRelPrime
    (fun p q pq => Nat.coprime_iff_isRelPrime.mp (((Nat.coprime_primes (prime p) (prime q)).mpr
      (fun h => pq (Subtype.ext h))).pow _ _)) proj
  obtain ⟨u, hu⟩ := Int.natCast_dvd.mpr prod_dvd
  let M := primorial Q
  let : NeZero M := ⟨primorial_ne_zero Q⟩
  let a := (u : ZMod M).val
  have mod_u : u ≡ (a : ℤ) [ZMOD M] := (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simp [a])
  have cop : a.Coprime M := by
    by_contra h
    obtain ⟨p,hp,hpa,hpM⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    let j : P := ⟨p, Nat.mem_primesLE.mpr ⟨(hp.dvd_primorial_iff.mp hpM),hp⟩⟩
    have pu : (p:ℤ) ∣ u := (mod_u.of_dvd (by exact_mod_cast hpM)).dvd_iff.mpr (by exact_mod_cast hpa)
    have pV : p^v j ∣ V := Finset.dvd_prod_of_mem (fun j:P => (j:ℕ)^v j) (Finset.mem_univ j)
    have px : ((p^(v j+1):ℕ):ℤ) ∣ x := by
      rw [pow_succ,Nat.cast_mul,hu]
      exact mul_dvd_mul (by exact_mod_cast pV) pu
    have bad := (hp.pow_dvd_iff_le_factorization (Int.natAbs_ne_zero.mpr nz)).mp
      (Int.natCast_dvd.mp px)
    exact Nat.not_succ_le_self _ bad
  let r := ZMod.unitOfCoprime a cop
  have ar : (r : ZMod M).val = a := by simp [r,a]
  have eqM : (∏ p:P, (p:ℕ)) = M := by
    rw [Finset.prod_coe_sort (Nat.primesLE Q) (fun z => z)]
    rfl
  have eqMod : (∏ p:P,(p:ℕ)^(v p+1)) = V*M := by simp [pow_succ,Finset.prod_mul_distrib,V,eqM]
  refine ⟨r,?_⟩
  change x ≡ (V:ℤ)*((r:ZMod M).val:ℤ) [ZMOD ((∏ p:P,(p:ℕ)^(v p+1):ℕ):ℤ)]
  rw [ar,eqMod,Nat.cast_mul,hu]
  exact mod_u.mul_left'

end BedertSelection

open Finset

namespace BedertSelection

/-- Bedert's Lemma 7.1, with the exact product bound and the same unit-modulo-primorial
parametrization as the non-Archimedean test function. -/
theorem large_valuation_cell (A : Finset ℤ) (nonempty : A.Nonempty) (nz : ∀ x∈A, x≠0)
    (k : ℕ) (dim : ∀ D : Finset ℤ, D⊆A → AddDissociated (D : Set ℤ) → D.card≤k)
    (Q : ℕ) : ∃ (v : ↥(Nat.primesLE Q) → ℕ) (r : (ZMod (primorial Q))ˣ),
    A.card ≤ k^(Nat.primesLE Q).card * primorial Q *
      (A.filter fun x => x ≡ ((∏ p : ↥(Nat.primesLE Q), (p:ℕ)^v p:ℕ):ℤ)*((r:ZMod (primorial Q)).val:ℤ)
        [ZMOD (∏ p : ↥(Nat.primesLE Q), (p:ℕ)^(v p+1):ℕ)]).card := by
  classical
  let P := ↥(Nat.primesLE Q)
  let M := primorial Q
  let : NeZero M := ⟨primorial_ne_zero Q⟩
  let W (p : P) := A.image fun x => x.natAbs.factorization p
  let Label := (∀ p:P, ↥(W p)) × (ZMod M)ˣ
  let val (l : Label) := fun p : P => (l.1 p : ℕ)
  let cell (l : Label) := A.filter fun x =>
    x ≡ ((∏ p:P, (p:ℕ)^(val l p):ℕ):ℤ)*((l.2:ZMod M).val:ℤ) [ZMOD (∏ p:P, (p:ℕ)^(val l p+1):ℕ)]
  have cover (x : ℤ) (hx : x ∈ A) : ∃ l : Label, x ∈ cell l := by
    obtain ⟨r,hr⟩ := valuation_unit_cover Q x (nz _ hx)
    let l : Label := ⟨fun p => ⟨_,mem_image_of_mem (fun x:ℤ => x.natAbs.factorization p) hx⟩,r⟩
    exact ⟨l,mem_filter.mpr ⟨hx,hr⟩⟩
  obtain ⟨x,hx⟩ := nonempty
  obtain ⟨l,_⟩ := cover x hx
  let : Nonempty Label := ⟨l⟩
  obtain ⟨best,_,maximal⟩ := exists_max_image univ (fun l : Label => (cell l).card) univ_nonempty
  have rc : Fintype.card (ZMod M)ˣ ≤ M := by
    simpa using Fintype.card_le_of_injective (fun r:(ZMod M)ˣ => (r:ZMod M)) Units.val_injective
  have vc : Fintype.card (∀ p:P, ↥(W p)) ≤ k^(Nat.primesLE Q).card := by
    calc
      _ = ∏ p:P, (W p).card := by simp
      _ ≤ ∏ _p:P, k := Finset.prod_le_prod' fun p _ => valuation_card_le A k nz dim p
        (Nat.prime_of_mem_primesLE p.property)
      _ = _ := by simp [P]
  have count : Fintype.card Label ≤ k^(Nat.primesLE Q).card*M := by
    simpa [Label] using Nat.mul_le_mul vc rc
  refine ⟨val best,best.2,?_⟩
  calc
    A.card ≤ (univ.biUnion cell).card := by
      apply card_le_card
      intro a ha
      obtain ⟨i,hi⟩ := cover a ha
      exact mem_biUnion.mpr ⟨i,mem_univ _,hi⟩
    _ ≤ ∑ i, (cell i).card := card_biUnion_le
    _ ≤ ∑ _i:Label, (cell best).card := sum_le_sum maximal
    _ = Fintype.card Label * (cell best).card := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ count

end BedertSelection

open Filter Finset Real

namespace BedertSelection

/-- The number of admissible valuation and unit labels is subpolynomial for
Q at most the square root of log N and polylogarithmic additive dimension. -/
theorem eventually_cell_loss (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k Q : ℕ, (k:ℝ) ≤ C*(Real.log N)^4 → (Q:ℝ) ≤ √(Real.log N) →
      ((k^(Nat.primesLE Q).card * primorial Q : ℕ):ℝ) ≤ (N:ℝ)^ε := by
  have grow : Tendsto (fun N:ℕ => √(Real.log N)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlog := Real.isLittleO_log_id_atTop.bound (show 0 < ε / 9 by positivity)
  filter_upwards [grow.eventually_ge_atTop 1, grow.eventually_ge_atTop (4*(C+1)),
    grow.eventually hlog, eventually_ge_atTop 1] with N ht hc hlogN hN k Q hk hQ
  let t := √(Real.log N)
  have ht' : 1 ≤ t := ht
  have nt : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have t2 : t^2 = Real.log N := Real.sq_sqrt (Real.log_nonneg (by exact_mod_cast hN))
  have t8 : t^8 = (Real.log N)^4 := by rw [←t2]; ring
  have hqt : 4*((k:ℝ)+1) ≤ t^9 := by
    calc
      4*((k:ℝ)+1) ≤ 4*((C+1)*t^8) := by rw [← t8] at hk; nlinarith [show 1 ≤ t^8 from one_le_pow₀ ht']
      _ ≤ t*t^8 := by nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (show 0≤t by linarith) 8)]
      _ = t^9 := by ring
  have cardP : (Nat.primesLE Q).card ≤ Q := by
    calc
      _ ≤ (Icc 1 Q).card := card_le_card (fun p hp => mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primesLE hp).one_lt.le,(Nat.mem_primesLE.mp hp).1⟩)
      _ = _ := by simp
  have cheap : k^(Nat.primesLE Q).card * primorial Q ≤ (4*(k+1))^Q := by
    rw [mul_pow,mul_comm (4^Q)]
    refine Nat.mul_le_mul ?_ (primorial_le_four_pow Q)
    exact (Nat.pow_le_pow_left (show k≤k+1 by omega) _).trans
      (Nat.pow_le_pow_right (by omega) cardP)
  have logt : 0 ≤ Real.log t := Real.log_nonneg ht'
  have logsmall : Real.log t ≤ ε/9*t := by
    change ‖Real.log t‖ ≤ ε/9*‖t‖ at hlogN
    simpa [Real.norm_eq_abs,abs_of_nonneg logt,abs_of_nonneg (show 0≤t by linarith)] using hlogN
  calc
    _ ≤ ((4*((k:ℝ)+1))^Q) := by exact_mod_cast cheap
    _ ≤ (t^9)^Q := pow_le_pow_left₀ (by positivity) hqt Q
    _ ≤ _ := by
      apply (Real.log_le_log_iff (by positivity : 0<(t^9)^Q) (Real.rpow_pos_of_pos nt ε)).mp
      rw [Real.log_pow,Real.log_pow,Real.log_rpow nt,←t2]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hQ (mul_nonneg (show (0:ℝ)≤9 by norm_num) logt),
        mul_le_mul_of_nonneg_right logsmall (show 0≤t by linarith)]

end BedertSelection

open Filter Finset Real

namespace BedertSelection

/-- Bedert's Corollary 7.2 on the low-dimensional branch, with unit leading
constant for all sufficiently large N and uniform in the choice of Q. -/
theorem eventually_large_cell (C ε : ℝ) (pos : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ), A.card = N → (∀ x∈A, x≠0) →
      ∀ k Q : ℕ, (∀ D : Finset ℤ, D⊆A → AddDissociated (D : Set ℤ) → D.card ≤ k) →
      (k:ℝ) ≤ C*(Real.log N)^4 → (Q:ℝ) ≤ √(Real.log N) →
      ∃ (v : ↥(Nat.primesLE Q) → ℕ) (r : (ZMod (primorial Q))ˣ),
        (N:ℝ)^(1-ε) ≤ ((A.filter fun x => x ≡
          ((∏ p : ↥(Nat.primesLE Q), (p:ℕ)^v p:ℕ):ℤ)*((r:ZMod (primorial Q)).val:ℤ)
            [ZMOD (∏ p : ↥(Nat.primesLE Q), (p:ℕ)^(v p+1):ℕ)]).card:ℝ) := by
  filter_upwards [eventually_cell_loss C ε pos,eventually_ge_atTop 1] with N loss hn A size nz k Q dim hk hQ
  obtain ⟨v,r,h⟩ := large_valuation_cell A (card_pos.mp (by omega)) nz k dim Q
  refine ⟨v,r,?_⟩
  let c := (A.filter fun x => x ≡
    ((∏ p : ↥(Nat.primesLE Q), (p:ℕ)^v p:ℕ):ℤ)*((r:ZMod (primorial Q)).val:ℤ)
      [ZMOD (∏ p : ↥(Nat.primesLE Q), (p:ℕ)^(v p+1):ℕ)]).card
  have hn' : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have h' : (N:ℝ) ≤ ((k^(Nat.primesLE Q).card * primorial Q:ℕ):ℝ)*c := by
    rw [size] at h
    exact_mod_cast h
  change _ ≤ (c:ℝ)
  rw [Real.rpow_sub hn',Real.rpow_one,div_le_iff₀ (Real.rpow_pos_of_pos hn' ε),mul_comm (c:ℝ)]
  exact h'.trans (mul_le_mul_of_nonneg_right (loss k Q hk hQ) (Nat.cast_nonneg _))

end BedertSelection

open Filter Finset Real

namespace BedertSelection

/-- Bedert's low-dimensional structural conclusion, with the single predecessor
estimate of Proposition 7.9 as the only remaining hypothesis on valuation cells. -/
theorem eventually_structural (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ), A.card = N → (∀ x∈A, x≠0) →
    ∀ k Q : ℕ, (∀ D : Finset ℤ, D⊆A → AddDissociated (D : Set ℤ) → D.card ≤ k) →
    (k:ℝ) ≤ C*(Real.log N)^4 → (Q:ℝ) ≤ √(Real.log N) →
    let P := ↥(Nat.primesLE Q)
    let M := primorial Q
    let card := fun (v : P → ℕ) (r : (ZMod M)ˣ) =>
      (A.filter fun x => x ≡ ((∏ p:P, (p:ℕ)^v p : ℕ):ℤ)*((r:ZMod M).val:ℤ)
        [ZMOD (∏ p:P, (p:ℕ)^(v p+1) : ℕ)]).card
    (∀ v r, (∀ s, card v s ≤ card v r) → (Real.log N)^4 ≤ (card v r:ℝ) →
      ∃ u < v, ∃ s, (card v r:ℝ) ≤ (Real.log N)^4*card u s) →
    ∃ (J : ℕ) (q : Fin (J+1) → ℕ) (r : Fin (J+1) → ℤ),
      (Real.log N)/(16*Real.log (Real.log N)) < J+1 ∧ (∀ i j, i ≤ j → q i ∣ q j) ∧
      Pairwise (fun i j => Disjoint {x : ℤ | x ≡ r i [ZMOD q i]} {x : ℤ | x ≡ r j [ZMOD q j]}) ∧
      let B := A ∪ A.image (fun x:ℤ => -x)
      let b := fun i => (B.filter fun x => x ≡ r i [ZMOD q i]).card
      1 ≤ b 0 ∧ ∀ i : Fin J, 10*b i.castSucc < b i.succ := by
  have grows : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_large_cell C (1/2) (by norm_num),grows.eventually_ge_atTop 3]
    with N seed hn A size nz k Q dim small cutoff P M card pred
  let base : P → ℕ := fun p => p
  have gt (p:P) : 1 < base p := (Nat.prime_of_mem_primesLE p.property).one_lt
  have eqM : (∏ p:P,base p) = M := by
    change (∏ p : ↥(Nat.primesLE Q), (p:ℕ)) = M
    rw [Finset.prod_coe_sort (Nat.primesLE Q) (fun z => z)]; rfl
  have units := unit_residue_conditions base gt
  dsimp only at units
  rw [eqM] at units
  let : NeZero M := ⟨primorial_ne_zero Q⟩
  apply structural_inputs base (fun p => zero_lt_one.trans (gt p))
    (fun r:(ZMod M)ˣ => ((r:ZMod M).val:ℤ)) units.1 (by rw [eqM]; exact units.2) A N
    (by change (3:ℝ)≤ Real.log N at hn; linarith)
    (by have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hn 4; norm_num at this; linarith) pred
  obtain ⟨v,r,large⟩ := seed A size nz k Q dim small cutoff
  refine ⟨v,r,?_⟩
  rw [show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow] at large
  exact large

end BedertSelection
end

section
namespace BedertSelection

/-- The seed and predecessor estimates of Lemma 8.1 furnish the full combinatorial
inputs to Bedert's non-Archimedean test function, including growth for A union -A. -/
theorem structural_levels {P R : Type*} [Fintype P] [Finite R] [Nonempty R]
    (base : P → ℕ) (positive : ∀ p, 0 < base p) (ρ : R → ℤ)
    (unit : ∀ s p, ¬(base p : ℤ) ∣ ρ s)
    (closed : ∀ s, ∃ t, ρ t ≡ -(ρ s) [ZMOD (∏ p, base p : ℕ)])
    (A : Finset ℤ) (N : ℕ) (hN : 1 < Real.log N) (twenty : 20 ≤ (Real.log N)^4) :
    let V := fun v : P → ℕ => ∏ p, base p^(v p)
    let Q := fun v : P → ℕ => ∏ p, base p^(v p+1)
    let card := fun v s => (A.filter (fun x => x ≡ V v*ρ s [ZMOD Q v])).card
    (∀ v r, (∀ s, card v s ≤ card v r) → (Real.log N)^4 ≤ (card v r : ℝ) →
      ∃ u < v, ∃ s, (card v r : ℝ) ≤ (Real.log N)^4*card u s) →
    (∃ seed r, Real.sqrt N ≤ (card seed r : ℝ)) →
    ∃ (J : ℕ) (v : Fin (J+1) → (P → ℕ)) (s : Fin (J+1) → R),
      let q := fun i => Q (v i)
      let r := fun i => (V (v i):ℤ)*ρ (s i)
      StrictMono v ∧ (∀ i t, card (v i) t ≤ card (v i) (s i)) ∧
      (Real.log N)/(16*Real.log (Real.log N)) < J+1 ∧
      (∀ i j, i ≤ j → q i ∣ q j) ∧
      Pairwise (fun i j => Disjoint {x : ℤ | x ≡ r i [ZMOD q i]}
                                     {x : ℤ | x ≡ r j [ZMOD q j]}) ∧
      let B := A ∪ A.image (fun x : ℤ => -x)
      let b := fun i => (B.filter fun x => x ≡ r i [ZMOD q i]).card
      1 ≤ b 0 ∧ ∀ i : Fin J, 10*b i.castSucc < b i.succ := by
  classical
  intro V Q card pred seed
  obtain ⟨z,t,large⟩ := seed
  obtain ⟨J,v,s,lower,_,mono,maximal,first,growth⟩ := log_fiber_chain card N hN pred z t large
  obtain ⟨order,disj⟩ := valuation_cells base positive v mono (fun i => ρ (s i)) (fun i => unit _)
  refine ⟨J,v,s,mono,maximal,lower,order,disj,?_⟩
  intro B b
  have bound (i : Fin (J+1)) : card (v i) (s i) ≤ b i ∧ b i ≤ 2*card (v i) (s i) := by
    let u := v i
    let a : ℤ := V u*ρ (s i)
    obtain ⟨r',h'⟩ := closed (s i)
    have QQ : Q u = V u * ∏ p, base p := by simp [V,Q,pow_succ,Finset.prod_mul_distrib]
    have flip : (V u:ℤ)*ρ r' ≡ -a [ZMOD Q u] := by
      rw [QQ,Nat.cast_mul]
      simpa [a] using h'.mul_left' (c := (V u : ℤ))
    have revert : A.filter (fun x => x ≡ -a [ZMOD Q u]) =
        A.filter (fun x => x ≡ (V u:ℤ)*ρ r' [ZMOD Q u]) := by
      apply Finset.filter_congr
      intro x _
      exact ⟨fun h => h.trans flip.symm, fun h => h.trans flip⟩
    obtain ⟨lo,hi⟩ := symmetric_cell_size A (Q u) a
    dsimp only at hi
    rw [revert] at hi
    have hi' : b i ≤ card (v i) (s i) + card (v i) r' := hi
    exact ⟨lo,by have h := maximal i r'; omega⟩
  refine ⟨first.trans (bound 0).1,?_⟩
  intro i
  have grows : (20:ℝ)*card (v i.castSucc) (s i.castSucc) < card (v i.succ) (s i.succ) :=
    (mul_le_mul_of_nonneg_right twenty (Nat.cast_nonneg _)).trans_lt (growth i)
  have natg : 20*card (v i.castSucc) (s i.castSucc) < card (v i.succ) (s i.succ) := by exact_mod_cast grows
  obtain ⟨_,small⟩ := bound i.castSucc
  obtain ⟨big,_⟩ := bound i.succ
  omega

end BedertSelection

open Filter Finset Real

namespace BedertSelection

/-- Bedert's low-dimensional structural conclusion, with the single predecessor
estimate of Proposition 7.9 as the only remaining hypothesis on valuation cells. -/
theorem eventually_structural_levels (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (A : Finset ℤ), A.card = N → (∀ x∈A, x≠0) →
    ∀ k Q : ℕ, (∀ D : Finset ℤ, D⊆A → AddDissociated (D : Set ℤ) → D.card ≤ k) →
    (k:ℝ) ≤ C*(Real.log N)^4 → (Q:ℝ) ≤ √(Real.log N) →
    let P := ↥(Nat.primesLE Q)
    let M := primorial Q
    let card := fun (v : P → ℕ) (r : (ZMod M)ˣ) =>
      (A.filter fun x => x ≡ ((∏ p:P, (p:ℕ)^v p : ℕ):ℤ)*((r:ZMod M).val:ℤ)
        [ZMOD (∏ p:P, (p:ℕ)^(v p+1) : ℕ)]).card
    (∀ v r, (∀ s, card v s ≤ card v r) → (Real.log N)^4 ≤ (card v r:ℝ) →
      ∃ u < v, ∃ s, (card v r:ℝ) ≤ (Real.log N)^4*card u s) →
    ∃ (J : ℕ) (v : Fin (J+1) → (P → ℕ)) (s : Fin (J+1) → (ZMod M)ˣ),
      let q := fun i => ∏ p:P, (p:ℕ)^(v i p+1)
      let r := fun i => ((∏ p:P, (p:ℕ)^(v i p):ℕ):ℤ) * ((s i:ZMod M).val:ℤ)
      StrictMono v ∧ (∀ i t, card (v i) t ≤ card (v i) (s i)) ∧
      (Real.log N)/(16*Real.log (Real.log N)) < J+1 ∧ (∀ i j, i ≤ j → q i ∣ q j) ∧
      Pairwise (fun i j => Disjoint {x : ℤ | x ≡ r i [ZMOD q i]} {x : ℤ | x ≡ r j [ZMOD q j]}) ∧
      let B := A ∪ A.image (fun x:ℤ => -x)
      let b := fun i => (B.filter fun x => x ≡ r i [ZMOD q i]).card
      1 ≤ b 0 ∧ ∀ i : Fin J, 10*b i.castSucc < b i.succ := by
  have grows : Tendsto (fun N:ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_large_cell C (1/2) (by norm_num),grows.eventually_ge_atTop 3]
    with N seed hn A size nz k Q dim small cutoff P M card pred
  let base : P → ℕ := fun p => p
  have gt (p:P) : 1 < base p := (Nat.prime_of_mem_primesLE p.property).one_lt
  have eqM : (∏ p:P,base p) = M := by
    change (∏ p : ↥(Nat.primesLE Q), (p:ℕ)) = M
    rw [Finset.prod_coe_sort (Nat.primesLE Q) (fun z => z)]; rfl
  have units := unit_residue_conditions base gt
  dsimp only at units
  rw [eqM] at units
  let : NeZero M := ⟨primorial_ne_zero Q⟩
  apply structural_levels base (fun p => zero_lt_one.trans (gt p))
    (fun r:(ZMod M)ˣ => ((r:ZMod M).val:ℤ)) units.1 (by rw [eqM]; exact units.2) A N
    (by change (3:ℝ)≤ Real.log N at hn; linarith)
    (by have := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤3) hn 4; norm_num at this; linarith) pred
  obtain ⟨v,r,large⟩ := seed A size nz k Q dim small cutoff
  refine ⟨v,r,?_⟩
  rw [show (1:ℝ)-1/2=1/2 by norm_num,← Real.sqrt_eq_rpow] at large
  exact large

end BedertSelection
end

section
open Filter Real
namespace GreenLow

/-- The terminal chain of length log N/(16 log log N) exceeds any fixed
multiple of the full prime-sieve cost log log N. -/
theorem eventual_chain_gain (C : ℝ) (hC : 0<C) :
    ∀ᶠ n : ℕ in atTop, C*Real.log (Real.log n) < (Real.log n)/(16*Real.log (Real.log n)) := by
  have logs : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have little := isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ)<1)
  have ev := little.bound (by positivity : 0 < (32*C)⁻¹)
  filter_upwards [logs.eventually ev,logs.eventually_ge_atTop 2] with n h hn
  let x := Real.log (n:ℝ)
  have hx : 2≤x := hn
  have lx : 0<Real.log x := Real.log_pos (by linarith)
  change C*Real.log x < x/(16*Real.log x)
  rw [lt_div_iff₀ (by positivity)]
  change ‖(Real.log x)^(2:ℝ)‖ ≤ _*‖x^(1:ℝ)‖ at h
  rw [Real.rpow_two,Real.rpow_one,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (by linarith)] at h
  have ratio : 32*C*(Real.log x)^2 ≤ x := by
    calc _ ≤ (32*C)*((32*C)⁻¹*x) := mul_le_mul_of_nonneg_left h (by positivity)
         _ = x := by field_simp
  nlinarith [sq_pos_of_pos lx,mul_pos hC (sq_pos_of_pos lx)]

end GreenLow
end

section
open Filter Real
namespace GreenLow

/-- The ordered branch is allowed a fixed number of packets (depending only
on the desired excess), while the modular branch absorbs its logarithmic sieve
loss using the much longer valuation chain. -/
theorem choose_scales (C D : ℝ) (hC : 0<C) (hD : 0<D) (goal : ℝ) (hg : 0≤goal) :
    ∃ (j K : ℕ), 4096^(j+1) ≤ K ∧ ∀ᶠ n : ℕ in atTop,
      (K:ℝ) ≤ Real.log n ∧ ∀ U : ℝ,
      ((15/64:ℝ)*j ≤ C*U ∨ ∃ len : ℕ,
        (Real.log n)/(16*Real.log (Real.log n)) < len ∧
        (7/20:ℝ)*len ≤ D*Real.log (Real.log n)*U) → goal < U := by
  obtain ⟨j,hj⟩ := exists_nat_gt (64*C*goal/15)
  let K := 4096^(j+1)
  refine ⟨j,K,le_rfl,?_⟩
  have logs := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let a := 3*D*(goal+1)
  have ha : 0<a := by dsimp [a]; positivity
  filter_upwards [eventual_chain_gain a ha,logs.eventually_ge_atTop (K:ℝ),logs.eventually_ge_atTop 2]
    with n gain hk hn
  change 2 ≤ Real.log (n:ℝ) at hn
  refine ⟨hk,fun U h => ?_⟩
  rcases h with h | ⟨len,long,fine⟩
  · by_contra! small; linarith [mul_le_mul_of_nonneg_left small hC.le]
  · have lp : 0<Real.log (Real.log n) := Real.log_pos (by linarith)
    by_contra! small
    have step := mul_le_mul_of_nonneg_left small (mul_nonneg hD.le lp.le)
    dsimp only [a] at gain
    nlinarith only [long,gain,fine.trans step,mul_pos hD lp,mul_nonneg (mul_nonneg hD.le lp.le) hg]

end GreenLow
end

section
open Filter MeasureTheory Finset Set
open scoped Classical
namespace GreenLow

/-- The two quantitative estimates from the valuation-cell argument imply the
literal bounded-model target of the public Green reduction. The sieve constants
are uniform in the level of the Fourier certificate. -/
theorem low_child_of_alternative (C D : ℝ) (hC : 0<C) (hD : 0<D)
    (alternatives : ∀ j K : ℕ, 4096^(j+1) ≤ K → ∀ᶠ n : ℕ in atTop,
      (K:ℝ) ≤ Real.log n → ∀ A : Finset ℤ, 0 ∉ A → A.card=n → (∀ a∈A,-a∉A) →
      let k := ⌈Real.log (n:ℝ)^4⌉₊
      (∀ B ⊆ A, AddDissociated (B:Set ℤ) → B.card ≤ k) →
      (∀ a∈A, |a| ≤ ((16*(k+1))^k : ℕ)) →
      let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3:ℝ) (2/3)
      let U := ∫ x : UnitAddCircle, |∑ a∈A, ((if a•x∈I then (1:ℝ) else 0)-1/3)|
      (15/64:ℝ)*j ≤ C*U ∨ ∃ len:ℕ, (Real.log n)/(16*Real.log (Real.log n)) < len ∧
        (7/20:ℝ)*len ≤ D*Real.log (Real.log n)*U) : OMA.R_Green1_green_1_R1.H2 := by
  intro g
  obtain ⟨j,K,scale,always⟩ := choose_scales C D hC hD (2*g) (by positivity)
  filter_upwards [always,alternatives j K scale] with n large fine
  intro A nz card antisym k dim radius
  let I := ((↑) : ℝ → UnitAddCircle) '' Ioo (1/3:ℝ) (2/3)
  let F := fun x : UnitAddCircle => ∑ b∈A, ((if b•x∈I then (1:ℝ) else 0)-1/3)
  have bne : ∀ b∈A,b≠0 := fun b hb h => nz (h ▸ hb)
  have hi : Integrable F := by
    apply integrable_finsetSum A
    intro b hb
    have sm := Green1Circle.middle_measure.1.preimage (Green1Circle.dilation_preserves b (bne b hb)).measurable
    exact ((integrable_const (1:ℝ)).indicator sm).sub (integrable_const _)
  have gt := large.2 (∫ x, |F x|) (fine large.1 A nz card antisym dim radius)
  obtain ⟨S,c,hc,hs⟩ := GreenBedert.finite_certificate F hi (2*g) gt
  refine ⟨S,c,hc,?_⟩
  dsimp only [F,I] at hs
  simp_rw [GreenArcFourier.signal_coeff A bne] at hs
  exact hs

end GreenLow
end

section
open MeasureTheory Finset AddCircle
open scoped Classical
namespace GreenLow

abbrev Levels (L : ℕ) := ↥(Nat.primesLE L) → ℕ
abbrev Residue (L : ℕ) := (ZMod (primorial L))ˣ
noncomputable def modulus {L : ℕ} (v : Levels L) := ∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p+1)
noncomputable def residue {L : ℕ} (v : Levels L) (s : Residue L) : ℤ :=
  ((∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p) : ℕ):ℤ)*((s:ZMod (primorial L)).val:ℤ)
noncomputable def cell {L : ℕ} (A : Finset ℤ) (v : Levels L) (s : Residue L) : Finset ℤ :=
  A.filter (fun n => n ≡ residue v s [ZMOD modulus v])
noncomputable def radius (n : ℕ) := let k := ⌈Real.log n^4⌉₊; (16*(k+1))^k
noncomputable def smallPrimes (n : ℕ) := ⌊Real.sqrt (Real.log n)⌋₊
noncomputable def bigPrimes (n : ℕ) := ⌊(Real.log n)^20⌋₊
def mirror (A : Finset ℤ) := A ∪ A.image (fun n : ℤ => -n)

theorem modulus_pos {L : ℕ} (v : Levels L) : 0 < modulus v := by
  unfold modulus
  apply Finset.prod_pos
  exact fun p _ => pow_pos (Nat.prime_of_mem_primesLE p.property).pos _

end GreenLow
end

section
open Finset MeasureTheory AddCircle
open scoped Classical
namespace GreenLow

noncomputable def window (T : ℕ) : Finset ℤ := (Ioo (-2*(T:ℤ)) (2*(T:ℤ))).erase 0

def medEligible (L Q : ℕ) (h : ℤ) := ∀ p:ℕ, p.Prime → L<p → p≤Q → ¬(p:ℤ)∣h
def fullEligible (Q : ℕ) (h : ℤ) := ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣h
noncomputable def coeff (A : Finset ℤ) (eligible : ℤ → Prop) (m : ℤ) : ℂ :=
  ∑ a∈A, if a∣m ∧ eligible (m/a) then GreenBourgain.weight (m/a).natAbs else 0
noncomputable def errorEnergy {L : ℕ} (A W : Finset ℤ) (v : Levels L) (r : Residue L)
    (cut : ℤ → ℂ) (eligible : ℤ → Prop) : ℝ :=
  ∑ m∈cell W v r, ‖cut m*coeff A eligible m - (if m∈mirror A then 1 else 0)‖^2

/-- Coefficient form of the two local bounds. All cutoffs and denominators
are fixed, and their normalization is the project's signed absolute-index weight. -/
def ProjectedBounds : Prop :=
  ∀ j : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℤ, 0∉A → A.card=n → (∀ a∈A,-a∉A) →
    (∀ a∈A, |a| ≤ (radius n:ℤ)) →
    let L:=smallPrimes n
    let Q:=bigPrimes n
    let T:=radius n
    ∀ v : Levels L, ∀ r : Residue L, (∀ s : Residue L, (cell A v s).card ≤ (cell A v r).card) →
    ∀ cut : ℤ → ℂ, (∀ m, ‖cut m‖ ≤ 1) → (∀ m : ℤ, m.natAbs ≤ T → cut m=1) →
    (errorEnergy A (window T) v r cut (fullEligible Q) ≤ ((cell A v r).card : ℝ)/100) ∧
    ((Real.log n)^4 ≤ ((cell A v r).card:ℝ) →
      (∀ u < v, ∀ s : Residue L, (Real.log n)^4*(cell A u s).card < ((cell A v r).card:ℝ)) →
      errorEnergy A (window T) v r cut (medEligible L Q) ≤
        ((cell A v r).card:ℝ) / (((4096^(j+1):ℕ):ℝ)^2))

end GreenLow
end

section
open Finset MeasureTheory AddCircle
namespace GreenLow

/-- A finite polynomial with Boolean main Fourier coefficients and nested
maximizing residue slices has large L¹ mass as soon as the rough remainder is
small in the individual slices. This uses the natural Fin indexing of §8.1. -/
theorem chain_estimate (W B : Finset ℤ) (included : B ⊆ W) (e : ℤ → ℂ) (J : ℕ)
    (q : Fin (J+1) → ℕ) (r : Fin (J+1) → ℤ) (pos : ∀ i, 0 < q i)
    (chain : ∀ i j, i ≤ j → q i ∣ q j) :
    let C := fun (S : Finset ℤ) (i : Fin (J+1)) => S.filter fun n => n ≡ r i [ZMOD q i]
    1 ≤ (C B 0).card → (∀ i : Fin J, 10*(C B i.castSucc).card < (C B i.succ).card) →
    (∀ i, (∑ n∈C W i, ‖e n‖^2) ≤ ((C B i).card : ℝ)/100) →
    (7/20:ℝ)*(J+1) ≤ ∫ x : UnitAddCircle, ‖∑ n∈W,
      ((if n∈B then 1 else 0)+e n)*fourier n x‖ ∂haarAddCircle := by
  classical
  intro C first grow err
  let idx (i : ℕ) : Fin (J+1) := if h : i<J+1 then ⟨i,h⟩ else 0
  let c (i : ℕ) := W.filter (fun n => (q (idx i):ℤ) ∣ n-r (idx i))
  let b (i : ℕ) := C B (idx i)
  have form (S : Finset ℤ) (i : Fin (J+1)) : S.filter (fun n => (q i:ℤ) ∣ n-r i) = C S i := by
    apply filter_congr; intro n _; exact (Int.modEq_iff_dvd (n := (q i:ℤ)) (a := r i) (b := n)).symm.trans ⟨Int.ModEq.symm,Int.ModEq.symm⟩
  have blocks (i : ℕ) : b i = (c i).filter fun n => decide (n∈B) := by
    ext n; simp only [b,c,form,C,mem_filter,decide_eq_true_eq]; constructor
    · intro h; exact ⟨⟨included h.1,h.2⟩,h.1⟩
    · intro h; exact ⟨h.2,h.1.2⟩
  have iuse (i : ℕ) (hi : i<J+1) : idx i = ⟨i,hi⟩ := dif_pos hi
  have nonempty (i : Fin (J+1)) : (C B i).Nonempty := by
    induction i using Fin.induction with
    | zero => exact card_pos.mp first
    | succ i ih => exact card_pos.mp ((Nat.zero_le _).trans_lt (grow i))
  have bound := BedertTest.nonarchimedean_mps W (fun n => decide (n∈B)) e (J+1)
    (fun i => q (idx i)) (fun i => r (idx i)) (fun i _ => pos _) (fun i k hk lt => chain _ _ (by
      rw [iuse k lt,iuse i (by omega)]; exact hk)) c (fun _ => rfl) b blocks (fun i _ => nonempty _)
    (fun i hi => by
      have hi' : i<J := by omega
      let i' : Fin J := ⟨i,hi'⟩
      simp only [b,iuse i (by omega),iuse (i+1) hi]
      have h := grow i'
      rw [show i'.castSucc = (⟨i,by omega⟩ : Fin (J+1)) from Fin.ext rfl,
        show i'.succ = (⟨i+1,hi⟩ : Fin (J+1)) from Fin.ext rfl] at h
      exact Nat.le_of_lt h)
    (fun i _ => by simpa [c,form,b] using err (idx i))
  simpa only [decide_eq_true_eq,Nat.cast_add,Nat.cast_one] using bound

end GreenLow
end

section
open Finset MeasureTheory AddCircle
open scoped Classical
namespace GreenLow

theorem mirror_in_window {A : Finset ℤ} {T : ℕ} (pos : 0<T) (nz : 0∉A)
    (rad : ∀ a∈A, |a| ≤ (T:ℤ)) : mirror A ⊆ window T := by
  intro n hn
  have hT : (0:ℤ)<T := by exact_mod_cast pos
  rw [window,mem_erase,mem_Ioo]
  rcases mem_union.mp hn with base | neg
  · have hn := rad n base
    have hn0 : n≠0 := fun he => nz (he ▸ base)
    exact ⟨hn0,by have := abs_le.mp hn; omega⟩
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp neg
    have sz := abs_le.mp (rad a ha)
    have ha0 : a≠0 := fun he => nz (he ▸ ha)
    exact ⟨neg_ne_zero.mpr ha0,by omega⟩

theorem cell_mono {L : ℕ} (v : Levels L) (r : Residue L) {A B : Finset ℤ} (sub : A⊆B) :
    cell A v r ⊆ cell B v r := filter_subset_filter _ sub

theorem coeff_zero (A : Finset ℤ) (elig : ℤ → Prop) : coeff A elig 0=0 := by
  classical
  apply sum_eq_zero; intro a ha
  simp [GreenBourgain.weight,GreenBourgain.chi]

/-- After applying the flat multiplier, the frequency at zero may be deleted. -/
theorem cutoff_window (T : ℕ) (pos : 0<T) (F : UnitAddCircle → ℂ) (hF : Integrable F haarAddCircle)
    (z : fourierCoeff F 0 = 0) :
    ∃ w : ℤ → ℂ, (∀ m, ‖w m‖ ≤ 1) ∧ (∀ m:ℤ, m.natAbs ≤ T → w m=1) ∧
    (∫ x : UnitAddCircle, ‖∑ m∈window T, w m * fourierCoeff F m * fourier m x‖ ∂haarAddCircle) ≤
      2*(∫ x, ‖F x‖ ∂haarAddCircle) := by
  obtain ⟨w,amp,flat,_,bound⟩ := GreenOneProjection.cutoff_polynomial T pos F hF
  refine ⟨w,amp,flat,?_⟩
  apply le_trans _ bound; apply le_of_eq; apply integral_congr_ae; filter_upwards with x
  congr 1
  apply sum_subset (erase_subset ..)
  intro m hm out
  have eq : m = 0 := by by_contra h; exact out (mem_erase.mpr ⟨h,hm⟩)
  simp [eq,z]

/-- On a single residue slice, the energy estimate gives the ordered MPS
lower bound for the complete smoothed projection. -/
theorem single_cell_gain {L : ℕ} (A W : Finset ℤ) (v : Levels L) (r : Residue L) (cut : ℤ → ℂ)
    (elig : ℤ → Prop) (J K : ℕ) (hk : 4096^(J+1) ≤ K) (large : K ≤ (cell A v r).card)
    (includeB : mirror A ⊆ W)
    (error : errorEnergy A W v r cut elig ≤ ((cell A v r).card:ℝ)/(K:ℝ)^2) :
    (15/64:ℝ)*J ≤ ∫ x : UnitAddCircle,
      ‖∑ n∈cell W v r, (cut n*coeff A elig n)*fourier n x‖ ∂haarAddCircle := by
  let S := cell (mirror A) v r
  let W' := cell W v r
  let e (n : ℤ) := cut n*coeff A elig n - (if n∈mirror A then 1 else 0)
  let E (x : UnitAddCircle) := ∑ n∈W', e n*fourier n x
  have sc : cell A v r ⊆ S := cell_mono v r subset_union_left
  have sw : S ⊆ W' := cell_mono v r includeB
  have intE : (∫ x, ‖E x‖^2 ∂haarAddCircle) ≤ (S.card:ℝ)/(K:ℝ)^2 := by
    rw [show (∫ x, ‖E x‖^2 ∂haarAddCircle) = _ from BedertTest.trig_square W' e]
    exact error.trans (div_le_div_of_nonneg_right (by exact_mod_cast card_le_card sc) (sq_nonneg _))
  have gain := BedertTest.ordered_mps S (fun _ => 1) J K hk (large.trans (card_le_card sc))
    (fun _ _ => le_rfl) (fun _ _ => by norm_num) E (continuous_finsetSum _ fun n _ => continuous_const.mul (fourier n).continuous) intE
  have eqn (x : UnitAddCircle) : (∑ n∈S, (↑(1:ℝ):ℂ)*fourier n x)+E x = ∑ n∈W', (cut n*coeff A elig n)*fourier n x := by
    have head : (∑ n∈S, (↑(1:ℝ):ℂ)*fourier n x) = ∑ n∈W', (if n∈mirror A then (1:ℂ) else 0)*fourier n x := by
      rw [←sum_subset sw (fun n hn ns => by
        have no : n∉mirror A := fun h => ns (mem_filter.mpr ⟨h,(mem_filter.mp hn).2⟩)
        simp [no])]
      apply sum_congr rfl; intro n hn; simp [(mem_filter.mp hn).1]
    rw [head]; dsimp only [E]; rw [←sum_add_distrib]
    apply sum_congr rfl; intro n hn; dsimp [e]; ring
  simpa only [eqn] using gain

end GreenLow
end

section
open Finset MeasureTheory AddCircle
open scoped Classical
namespace GreenLow

theorem medium_gain {T L : ℕ} (ht : 0<T) (A : Finset ℤ) (v : Levels L) (r : Residue L)
    (Bfits : mirror A ⊆ window T) (F : UnitAddCircle → ℂ) (hF : Integrable F haarAddCircle)
    (elig : ℤ → Prop) (four : ∀ m, fourierCoeff F m = coeff A elig m) (J : ℕ)
    (big : 4096^(J+1) ≤ (cell A v r).card)
    (localBound : ∀ cut : ℤ → ℂ, (∀ m, ‖cut m‖ ≤ 1) → (∀ m:ℤ, m.natAbs≤T → cut m=1) →
      errorEnergy A (window T) v r cut elig ≤ ((cell A v r).card:ℝ) / (((4096^(J+1):ℕ):ℝ)^2)) :
    (15/64:ℝ)*J ≤ 2*(∫ x, ‖F x‖ ∂haarAddCircle) := by
  obtain ⟨G,ig,fg,bd⟩ := GreenOneProjection.residue_projection (modulus v) (modulus_pos v) (residue v r) F hF
  have fg' m : fourierCoeff G m = if m ≡ residue v r [ZMOD modulus v] then coeff A elig m else 0 := by
    rw [fg,four]
    have prop : (↑(modulus v):ℤ) ∣ m-residue v r ↔ m ≡ residue v r [ZMOD modulus v] :=
      (Int.modEq_iff_dvd (n := (modulus v:ℤ)) (a := residue v r) (b := m)).symm.trans ⟨Int.ModEq.symm,Int.ModEq.symm⟩
    simp only [prop]
  have zero : fourierCoeff G 0 = 0 := by rw [fg',coeff_zero,ite_self]
  obtain ⟨cut,amp,flat,limit⟩ := cutoff_window T ht G ig zero
  have bound := single_cell_gain A (window T) v r cut elig J _ le_rfl big Bfits (localBound cut amp flat)
  have eqn (x : UnitAddCircle) : (∑ n∈window T, cut n*fourierCoeff G n*fourier n x) =
      ∑ n∈cell (window T) v r, cut n*coeff A elig n*fourier n x := by
    rw [cell,sum_filter]; apply sum_congr rfl; intro n hn; rw [fg']; split_ifs <;> simp_all
  simp_rw [eqn] at limit
  linarith

/-- The same polynomial is used in every cell of the chain. This is why the
full-sieve denominator is paid once. -/
theorem full_gain {T L : ℕ} (ht : 0<T) (A : Finset ℤ) (Bfits : mirror A ⊆ window T)
    (F : UnitAddCircle → ℂ) (hF : Integrable F haarAddCircle) (elig : ℤ → Prop)
    (four : ∀ m, fourierCoeff F m = coeff A elig m) (J : ℕ)
    (v : Fin (J+1) → Levels L) (r : Fin (J+1) → Residue L)
    (chain : ∀ i j, i≤j → modulus (v i) ∣ modulus (v j))
    (first : 1 ≤ (cell (mirror A) (v 0) (r 0)).card)
    (grow : ∀ i : Fin J, 10*(cell (mirror A) (v i.castSucc) (r i.castSucc)).card <
      (cell (mirror A) (v i.succ) (r i.succ)).card)
    (localBound : ∀ i, ∀ cut : ℤ → ℂ, (∀ m, ‖cut m‖ ≤ 1) → (∀ m:ℤ,m.natAbs≤T → cut m=1) →
      errorEnergy A (window T) (v i) (r i) cut elig ≤ ((cell A (v i) (r i)).card:ℝ)/100) :
    (7/20:ℝ)*(J+1) ≤ 2*(∫ x, ‖F x‖ ∂haarAddCircle) := by
  obtain ⟨cut,amp,flat,bound⟩ := cutoff_window T ht F hF ((four 0).trans (coeff_zero A elig))
  let e (n : ℤ) := cut n*coeff A elig n - (if n∈mirror A then 1 else 0)
  have cs := chain_estimate (window T) (mirror A) Bfits e J (fun i => modulus (v i))
    (fun i => residue (v i) (r i)) (fun i => modulus_pos _) chain first grow (fun i =>
      (localBound i cut amp flat).trans (div_le_div_of_nonneg_right (by
        exact_mod_cast card_le_card (cell_mono (v i) (r i) (show A ⊆ mirror A from subset_union_left))) (by norm_num)))
  have term (n : ℤ) (x : UnitAddCircle) : ((if n∈mirror A then 1 else 0)+e n)*fourier n x = cut n*fourierCoeff F n*fourier n x := by
    rw [four]; dsimp only [e]; ring
  simpa only [term] using cs.trans (by simpa only [←term] using bound)

end GreenLow
end

section
open Finset MeasureTheory AddCircle Filter Set
open scoped Classical
namespace GreenLow

/-- Both sieve branches and the §8.1 chain establish the full bounded-model
Fourier certificate from the two explicit arithmetic error estimates. -/
theorem low_of_projected_bounds (arithmetic : ProjectedBounds) : OMA.R_Green1_green_1_R1.H2 := by
  obtain ⟨C,cpos,medium⟩ := BedertSieve.medium_signal_uniform
  obtain ⟨D,dpos,full⟩ := BedertSieve.full_signal_uniform
  let a := 2*Real.pi/Real.sqrt 3
  have ap : 0 < a := by dsimp [a]; positivity
  apply low_child_of_alternative (2*C*a) (40*D*a) (by positivity) (by positivity)
  intro j K hK
  have logs : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [arithmetic j,BedertSelection.eventually_structural_levels 2,logs.eventually_ge_atTop 4]
    with n errors levels big
  intro klog A nz card antisym k dim rad I U
  let z := Real.log (n:ℝ)
  let x := Real.sqrt z
  let L := smallPrimes n
  let Q := bigPrimes n
  let T := radius n
  have zp : 0<z := by change 4≤z at big; linarith
  have x2 : 2≤x := by dsimp [x]; exact (Real.le_sqrt (by norm_num) zp.le).mpr (by change 4≤z at big; linarith)
  have x40 : x^40=z^20 := by rw [show 40=2*20 by norm_num,pow_mul,Real.sq_sqrt zp.le]
  have Qnat : Q=⌊z^20⌋₊ := rfl
  have q2 : 2≤Q := by
    rw [Qnat]; apply Nat.le_floor
    calc (2:ℝ) ≤ z := by change 4≤z at big; linarith
         _ = z^1 := (pow_one z).symm
         _ ≤ _ := pow_le_pow_right₀ (by change 4≤z at big; linarith) (by decide)
  have lQ : Real.log (Q:ℝ) ≤ 20*Real.log z := by
    rw [←show Real.log (z^20) = 20*Real.log z by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by decide : 0<2) q2)) (Nat.floor_le (by positivity : 0 ≤ z^20))
  have hT : 0<T := by dsimp [T,radius]; positivity
  have fits := mirror_in_window hT nz (show ∀b∈A, |b| ≤ (T:ℤ) from rad)
  have ck : (k:ℝ) ≤ 2*z^4 := by
    have upper := Nat.ceil_lt_add_one (by positivity : 0 ≤ z^4)
    have low := one_le_pow₀ (show 1≤z by change 4≤z at big; linarith) (n := 4)
    change (⌈z^4⌉₊:ℝ) ≤ _; linarith
  let cellN (v : Levels L) (r : Residue L) := (cell A v r).card
  have base : GreenBourgain.mass (GreenBourgain.signal A GreenBourgain.base) = a*U := GreenBourgain.base_discrepancy A
  have ne : ∀ b∈A,b≠0 := fun b hb he => nz (he ▸ hb)
  have up : 0≤U := integral_nonneg fun _ => abs_nonneg _
  by_cases pred : ∀ v r, (∀ s, cellN v s ≤ cellN v r) → z^4 ≤ (cellN v r:ℝ) →
      ∃ u < v, ∃ s, (cellN v r:ℝ) ≤ z^4*cellN u s
  · right
    obtain ⟨J,v,s,_,maxim,long,chain,_,first,grow⟩ := levels A card ne k L dim ck (Nat.floor_le (Real.sqrt_nonneg z)) pred
    obtain ⟨F,hF,mass,four⟩ := full Q q2 A ne
    have b := full_gain hT A fits F hF (fullEligible Q) four J v s chain first grow (fun i cut amp flat =>
      (errors A nz card antisym rad (v i) (s i) (maxim i) cut amp flat).1)
    refine ⟨J+1,by exact_mod_cast long,?_⟩
    rw [base] at mass
    change (∫ x, ‖F x‖ ∂haarAddCircle) ≤ _ at mass
    push_cast
    calc _ ≤ 2*(∫ x, ‖F x‖ ∂haarAddCircle) := b
         _ ≤ 2*(D*Real.log Q*(a*U)) := by gcongr
         _ ≤ _ := by
           change _ ≤ 40*D*a*Real.log z*U
           nlinarith only [mul_le_mul_of_nonneg_right lQ (mul_nonneg (mul_nonneg dpos.le ap.le) up)]
  · left
    push Not at pred
    obtain ⟨v,r,maxim,large,fail⟩ := pred
    obtain ⟨F,hF,mass,four⟩ := medium x x2 A ne
    have cc : ∀ m, fourierCoeff F m = coeff A (medEligible L Q) m := by
      intro m
      rw [four m,x40]
      unfold coeff medEligible
      apply sum_congr rfl; intro b hb
      congr 1
    have ks : 4096^(j+1) ≤ cellN v r := by
      apply (Nat.cast_le (α := ℝ)).mp
      calc (((4096^(j+1)):ℕ):ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
           _ ≤ z := klog
           _ = z^1 := (pow_one z).symm
           _ ≤ z^4 := pow_le_pow_right₀ (by change 4≤z at big; linarith) (by decide)
           _ ≤ _ := large
    have b := medium_gain hT A v r fits F hF (medEligible L Q) cc j ks (fun cut amp flat =>
      (errors A nz card antisym rad v r maxim cut amp flat).2 large fail)
    rw [base] at mass
    change (∫ x, ‖F x‖ ∂haarAddCircle) ≤ _ at mass
    nlinarith only [b,mass]

end GreenLow
end

section
open Finset

namespace BedertSelection

/-- Divide an exact common factor out of both the frequency and its congruence modulus. -/
theorem cell_quotient (V M : ℕ) (r x : ℤ) :
    x ≡ (V:ℤ)*r [ZMOD (V:ℤ)*M] ↔ ∃ y : ℤ, x=(V:ℤ)*y ∧ y ≡ r [ZMOD M] := by
  constructor
  · intro h
    obtain ⟨t,ht⟩ := Int.modEq_iff_add_fac.mp h
    refine ⟨r-(M:ℤ)*t,?_,Int.modEq_iff_add_fac.mpr ⟨t,by ring⟩⟩
    rw [mul_sub,ht]
    ring
  · rintro ⟨y,rfl,hy⟩
    exact hy.mul_left'

/-- A product of prime powers at distinct primes has the specified valuation at
every coordinate. -/
theorem factorization_of_levels (Q : ℕ) (v : ↥(Nat.primesLE Q) → ℕ) (p : ↥(Nat.primesLE Q)) :
    (∏ i : ↥(Nat.primesLE Q), (i:ℕ)^v i).factorization p = v p := by
  classical
  have hp (i : ↥(Nat.primesLE Q)) := Nat.prime_of_mem_primesLE i.property
  rw [Nat.factorization_prod_apply (fun i _ => pow_ne_zero _ (hp i).ne_zero),
    Finset.sum_eq_single p]
  · exact Nat.factorization_pow_self (hp p)
  · intro i _ ne
    rw [(hp i).factorization_pow]
    exact Finsupp.single_eq_of_ne (fun h => ne (Subtype.ext h.symm))
  · simp

/-- The unit residue condition recovers every exact valuation of an integer from
the projected frequency class. -/
theorem valuations_of_cell (Q : ℕ) (v : ↥(Nat.primesLE Q) → ℕ)
    (r : (ZMod (primorial Q))ˣ) (x : ℤ) (nz : x≠0) :
    let V := (∏ p : ↥(Nat.primesLE Q), (p:ℕ)^v p)
    x ≡ (V:ℤ)*((r:ZMod (primorial Q)).val:ℤ) [ZMOD (V:ℤ)*(primorial Q:ℕ)] →
    ∀ p : ↥(Nat.primesLE Q), x.natAbs.factorization p = v p := by
  intro V cell p
  let M := primorial Q
  obtain ⟨y,hxy,hy⟩ := (cell_quotient _ _ _ _).mp cell
  have non : V*y.natAbs ≠ 0 := by simpa [hxy,Int.natAbs_mul] using Int.natAbs_ne_zero.mpr nz
  have divM : (p:ℕ) ∣ M := (Nat.prime_of_mem_primesLE p.property).dvd_primorial_iff.mpr
    (Nat.mem_primesLE.mp p.property).1
  have ny : ¬(p:ℕ) ∣ y.natAbs := by
    intro divides
    have d := (hy.of_dvd (by exact_mod_cast divM)).dvd_iff.mp (Int.natCast_dvd.mpr divides)
    have d' : (p:ℕ) ∣ (r:ZMod M).val := by exact_mod_cast d
    exact (Nat.prime_of_mem_primesLE p.property).ne_one
      (Nat.eq_one_of_dvd_coprimes (ZMod.val_coe_unit_coprime r) d' divM)
  rw [hxy,Int.natAbs_mul,Int.natAbs_natCast,Nat.factorization_mul (left_ne_zero_of_mul non)
    (right_ne_zero_of_mul non),Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd ny,add_zero]
  exact factorization_of_levels Q v p

/-- In a selected dilated Fourier frequency, the input level is below the target
level, and the multiplier supplies their precise coordinatewise difference. -/
theorem multiplier_valuations (Q : ℕ) (mu ν : ↥(Nat.primesLE Q) → ℕ)
    (s r : (ZMod (primorial Q))ˣ) (a n : ℤ) (ha : a≠0) (hn : n≠0) :
    let V := fun u : ↥(Nat.primesLE Q) → ℕ => ∏ p : ↥(Nat.primesLE Q), (p:ℕ)^u p
    let cell := fun u (r : (ZMod (primorial Q))ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((r:ZMod (primorial Q)).val:ℤ) [ZMOD (V u:ℤ)*(primorial Q:ℕ)]
    cell mu s a → cell ν r (n*a) → mu ≤ ν ∧ (∀ p : ↥(Nat.primesLE Q), n.natAbs.factorization p = ν p-mu p) := by
  intro V cell source target
  have hv := valuations_of_cell Q ν r (n*a) (mul_ne_zero hn ha) target
  have hmu := valuations_of_cell Q mu s a ha source
  have eqn (p : ↥(Nat.primesLE Q)) : n.natAbs.factorization p + mu p = ν p := by
    simpa only [Int.natAbs_mul,Nat.factorization_mul (Int.natAbs_ne_zero.mpr hn)
      (Int.natAbs_ne_zero.mpr ha),Finsupp.add_apply,hmu] using hv p
  exact ⟨fun p => by change mu p ≤ ν p; have := eqn p; omega,fun p => by have := eqn p; omega⟩

end BedertSelection

open Finset

namespace BedertSelection

/-- An exact multiplier decomposition for Bedert's medium-prime sieve. Positive and
negative frequencies are covered by the signed integer n. The only surviving
multipliers are a prescribed product of small prime powers times a Q-rough integer,
in a prescribed unit residue modulo the small primorial. -/
theorem projected_multiplier_iff (L Q : ℕ)
    (mu v : ↥(Nat.primesLE L) → ℕ) (s r : (ZMod (primorial L))ˣ)
    (a n : ℤ) (ha : a ≠ 0) (hn : n ≠ 0)
    (medium : ∀ p : ℕ, p.Prime → L < p → p ≤ Q → ¬(p:ℤ) ∣ n) :
    let M := primorial L
    let V := fun u : ↥(Nat.primesLE L) → ℕ => ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
    let cell := fun u (r : (ZMod M)ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V u:ℤ)*M]
    cell mu s a → (cell v r (n*a) ↔ mu ≤ v ∧ ∃ h : ℤ,
      n=(V (v-mu):ℤ)*h ∧ (h : ZMod M)*(s : ZMod M) = r ∧
      ∀ p : ℕ, p.Prime → p ≤ Q → ¬(p:ℤ) ∣ h) := by
  classical
  intro M V cell source
  let : NeZero M := ⟨primorial_ne_zero L⟩
  have positive (u : ↥(Nat.primesLE L) → ℕ) : V u ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun i _ => pow_ne_zero _ (Nat.prime_of_mem_primesLE i.property).ne_zero)
  have prod (leq : mu ≤ v) : V (v-mu)*V mu = V v := by
    dsimp only [V]
    rw [← prod_mul_distrib]
    apply prod_congr rfl
    intro i _
    rw [← pow_add,Pi.sub_apply,Nat.sub_add_cancel (leq i)]
  obtain ⟨y,ay,ys⟩ := (cell_quotient _ _ _ _).mp source
  have valcast (z : ℤ) (u : (ZMod M)ˣ) :
      z ≡ ((u : ZMod M).val:ℤ) [ZMOD M] ↔ (z:ZMod M)=u := by
    rw [← ZMod.intCast_eq_intCast_iff]; simp
  have yc := (valcast y s).mp ys
  have test (leq : mu ≤ v) (h : ℤ) (nh : n=(V (v-mu):ℤ)*h) :
      cell v r (n*a) ↔ (h:ZMod M)*(s:ZMod M)=r := by
    have rearr : n*a = (V v:ℤ)*(h*y) := by
      rw [nh,ay,←prod leq,Nat.cast_mul]; ring
    change n*a ≡ (V v:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V v:ℤ)*M] ↔ _
    rw [rearr,Int.ModEq.mul_left_cancel_iff' (Nat.cast_ne_zero.mpr (positive v)),valcast,Int.cast_mul,yc]
  refine ⟨fun target => ?_,?_⟩
  · obtain ⟨leq,vals⟩ := multiplier_valuations L mu v s r a n ha hn source target
    let w := fun i : ↥(Nat.primesLE L) => n.natAbs.factorization i
    have wval : w = v-mu := funext vals
    obtain ⟨u,nu⟩ := valuation_unit_cover L n hn
    have mm : (∏ p : ↥(Nat.primesLE L),(p:ℕ)) = M := by
      rw [Finset.prod_coe_sort (Nat.primesLE L) (fun z => z)]; rfl
    change n ≡ (V w : ℤ)*((u:ZMod M).val:ℤ) [ZMOD ((∏ p : ↥(Nat.primesLE L),(p:ℕ)^(w p+1):ℕ):ℤ)] at nu
    simp only [pow_succ,prod_mul_distrib,mm,Nat.cast_mul] at nu
    obtain ⟨h,nh,hu⟩ := (cell_quotient (V w) M _ n).mp nu
    rw [wval] at nh
    refine ⟨leq,h,nh,(test leq h nh).mp target,?_⟩
    intro p hp pq ph
    by_cases pl : p ≤ L
    · have pM : p ∣ M := hp.dvd_primorial_iff.mpr pl
      have du := (hu.of_dvd (by exact_mod_cast pM)).dvd_iff.mp ph
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (ZMod.val_coe_unit_coprime u) (by exact_mod_cast du) pM)
    · apply medium p hp (lt_of_not_ge pl) pq
      rw [nh]; exact dvd_mul_of_dvd_right ph _
  · rintro ⟨leq,h,nh,residue,_⟩
    exact (test leq h nh).mpr residue

end BedertSelection

namespace BedertSelection
open Finset
open scoped Classical

theorem prime_outside_levels (L : ℕ) (v : ↥(Nat.primesLE L) → ℕ) (p : ℕ)
    (hp : p.Prime) (outside : L < p) : ¬ p ∣ ∏ i : ↥(Nat.primesLE L), (i:ℕ)^v i := by
  rintro h
  obtain ⟨i,_,di⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
  have eq := (Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primesLE i.property)).mp
    (hp.dvd_of_dvd_pow di)
  exact (not_le_of_gt outside) (eq ▸ (Nat.mem_primesLE.mp i.property).1)

/-- Coefficient-by-coefficient form of the medium-prime block identity in Bedert §7.
For each source slice, the remaining rough weight is dilated by its prescribed
prime powers, and multiplied by the scalar weight of that dilation. -/
theorem medium_block_coefficient {R : Type*} [CommSemiring R] (w : ℕ →* R) (L Q : ℕ)
    (mu v : ↥(Nat.primesLE L) → ℕ) (s r : (ZMod (primorial L))ˣ) (A : Finset ℤ)
    (anz : ∀ a ∈ A, a≠0) (m : ℤ) (mnz : m≠0) :
    let M := primorial L
    let V := fun u : ↥(Nat.primesLE L) → ℕ => ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
    let cell := fun u (r : (ZMod M)ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V u:ℤ)*M]
    let K := V (v-mu)
    let medium := fun n:ℤ => ∀ p:ℕ, p.Prime → L<p → p≤Q → ¬(p:ℤ) ∣ n
    let rough := fun n:ℤ => ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ) ∣ n
    (∀ a ∈ A, cell mu s a) → cell v r m →
    (∑ a ∈ A, if a ∣ m ∧ medium (m/a) then w (m/a).natAbs else 0) =
      if mu ≤ v then w K * ∑ a ∈ A, let h := m/((K:ℤ)*a)
        if (K:ℤ)*a ∣ m ∧ (h:ZMod M)*(s:ZMod M)=r ∧ rough h then w h.natAbs else 0
      else 0 := by
  intro M V cell K medium rough src tgt
  have Kn : K ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _
    (Nat.prime_of_mem_primesLE i.property).ne_zero)
  have Kz : (K:ℤ) ≠ 0 := by exact_mod_cast Kn
  have forward (a : ℤ) (ha : a ∈ A) (hit : a ∣ m ∧ medium (m/a)) :
      mu ≤ v ∧ (K:ℤ)*a ∣ m ∧
        ((m/((K:ℤ)*a):ℤ):ZMod M)*(s:ZMod M) = r ∧ rough (m/((K:ℤ)*a)) ∧
        m/a = (K:ℤ)*(m/((K:ℤ)*a)) := by
    have ma := Int.ediv_mul_cancel hit.1
    have nz : m/a≠0 := fun h => mnz (by rwa [h,zero_mul,eq_comm] at ma)
    obtain ⟨leq,h,nh,hs,hr⟩ := (projected_multiplier_iff L Q mu v s r a (m/a)
      (anz a ha) nz hit.2 (src a ha)).mp (by change cell v r (m/a*a); rw [ma]; exact tgt)
    have eq : m = (K:ℤ)*a*h := by rw [← ma,nh]; ring
    have quotient : m/((K:ℤ)*a)=h := by
      nth_rw 1 [eq]; exact Int.mul_ediv_cancel_left _ (mul_ne_zero Kz (anz a ha))
    exact ⟨leq,⟨h,eq⟩,quotient ▸ hs,quotient ▸ hr,quotient ▸ nh⟩
  by_cases leq : mu ≤ v
  · rw [if_pos leq,mul_sum]
    apply sum_congr rfl
    intro a ha
    dsimp only
    by_cases hit : a ∣ m ∧ medium (m/a)
    · obtain ⟨_,div,res,rou,eq⟩ := forward a ha hit
      rw [if_pos hit,if_pos ⟨div,res,rou⟩,eq,Int.natAbs_mul,Int.natAbs_natCast,map_mul]
    · rw [if_neg hit]
      have no : ¬ ((K:ℤ)*a ∣ m ∧ ((m/((K:ℤ)*a):ℤ):ZMod M)*(s:ZMod M)=r ∧
          rough (m/((K:ℤ)*a))) := by
        rintro ⟨div,_,hr⟩
        apply hit
        have da : a ∣ m := (dvd_mul_left a (K:ℤ)).trans div
        have eq : m/a = (K:ℤ)*(m/((K:ℤ)*a)) := by
          apply mul_right_cancel₀ (anz a ha)
          rw [Int.ediv_mul_cancel da, mul_assoc, mul_comm (m/((K:ℤ)*a)) a,
            ←mul_assoc,Int.mul_ediv_cancel_of_dvd div]
        refine ⟨da,fun p hp pl pq pd => ?_⟩
        rw [eq] at pd
        have d := Int.natCast_dvd.mp pd
        rw [Int.natAbs_mul,Int.natAbs_natCast] at d
        rcases hp.dvd_mul.mp d with dK|dh
        · exact prime_outside_levels L (v-mu) p hp pl dK
        · exact hr p hp pq (Int.natCast_dvd.mpr dh)
      rw [if_neg no,mul_zero]
  · rw [if_neg leq]
    apply sum_eq_zero
    intro a ha
    exact if_neg (fun hit => leq (forward a ha hit).1)

end BedertSelection

namespace BedertSelection
open Finset
open scoped Classical

/-- Partition any finite sum by the exact valuation levels and unit residues of its
integer frequencies. -/
theorem sum_valuation_cells {R : Type*} [AddCommMonoid R] (L : ℕ) (A : Finset ℤ)
    (nz : ∀ a ∈ A, a≠0) (F : ℤ → R) :
    let M := primorial L
    letI : NeZero M := ⟨primorial_ne_zero L⟩
    let levels := fun x:ℤ => fun p : ↥(Nat.primesLE L) => x.natAbs.factorization p
    let V := fun u : ↥(Nat.primesLE L) → ℕ => ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
    let cell := fun u (r : (ZMod M)ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V u:ℤ)*M]
    ∑ a ∈ A, F a = ∑ u ∈ A.image levels, ∑ r : (ZMod M)ˣ, ∑ a ∈ A.filter (cell u r),F a := by
  intro M levels V cell
  let : NeZero M := ⟨primorial_ne_zero L⟩
  have covers (a:ℤ) (ha : a≠0) : ∃ r, cell (levels a) r a := by
    obtain ⟨r,hr⟩ := valuation_unit_cover L a ha
    have mm : (∏ p : ↥(Nat.primesLE L),(p:ℕ)) = M := by
      rw [Finset.prod_coe_sort (Nat.primesLE L) (fun z => z)]; rfl
    refine ⟨r,?_⟩
    simpa only [pow_succ,prod_mul_distrib,mm,Nat.cast_mul] using hr
  let residue := fun a : ℤ => if h : a≠0 then (covers a h).choose else 1
  have spec {a} (ha : a∈A) := (covers a (nz a ha)).choose_spec
  have classify {a} (ha : a∈A) (u) (r : (ZMod M)ˣ) :
      (levels a,residue a)=(u,r) ↔ cell u r a := by
    have cur : cell (levels a) (residue a) a := by simpa [residue,nz _ ha] using spec ha
    refine ⟨fun h => by obtain ⟨rfl,rfl⟩ := Prod.mk.inj h; exact cur,fun target => ?_⟩
    have eq : levels a=u := funext (valuations_of_cell L u r a (nz _ ha) target)
    apply Prod.ext eq
    rw [←eq] at target
    have nonzero : (V (levels a):ℤ)≠0 := Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun i _ => pow_ne_zero _ (Nat.prime_of_mem_primesLE i.property).ne_zero))
    have same := Int.ModEq.mul_left_cancel' nonzero (cur.symm.trans target)
    apply Units.ext
    simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr same
  let T := (A.image levels) ×ˢ (univ : Finset (ZMod M)ˣ)
  let assign := fun a => (levels a,residue a)
  have hmap (a:ℤ) (ha : a∈A) : assign a ∈ T := mem_product.mpr
    ⟨mem_image_of_mem _ ha,mem_univ _⟩
  rw [← sum_fiberwise_of_maps_to hmap F]
  change ∑ i ∈ (A.image levels) ×ˢ univ, _ = _
  rw [sum_product]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro r _
  congr 1
  apply filter_congr
  intro a ha
  exact classify ha u r

end BedertSelection

namespace BedertSelection
open Finset
open scoped Classical

/-- A coefficient of the medium-sieved sum at level v consists of the rough
coefficients of the finite source levels mu ≤ v, weighted by their dilation. -/
theorem medium_spectrum {R : Type*} [CommSemiring R] (w : ℕ →* R) (L Q : ℕ)
    (v : ↥(Nat.primesLE L) → ℕ) (r : (ZMod (primorial L))ˣ)
    (A : Finset ℤ) (nz : ∀ a ∈ A, a≠0) (m : ℤ) (mnz : m≠0) :
    let M := primorial L
    letI : NeZero M := ⟨primorial_ne_zero L⟩
    let V := fun u : ↥(Nat.primesLE L) → ℕ => ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
    let cell := fun u (s : (ZMod M)ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((s:ZMod M).val:ℤ) [ZMOD (V u:ℤ)*M]
    let levels := fun x:ℤ => fun p : ↥(Nat.primesLE L) => x.natAbs.factorization p
    let medium := fun n:ℤ => ∀ p:ℕ, p.Prime → L<p → p≤Q → ¬(p:ℤ)∣n
    let rough := fun n:ℤ => ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣n
    cell v r m →
    (∑ a∈A, if a∣m ∧ medium (m/a) then w (m/a).natAbs else 0) =
      ∑ mu ∈ (A.image levels).filter (fun u => u≤v),
        let K := V (v-mu)
        w K * ∑ s : (ZMod M)ˣ, ∑ a ∈ A.filter (cell mu s),
          let h := m/((K:ℤ)*a)
          if (K:ℤ)*a ∣ m ∧ (h:ZMod M)*(s:ZMod M)=r ∧ rough h then w h.natAbs else 0 := by
  intro M V cell levels medium rough selected
  let : NeZero M := ⟨primorial_ne_zero L⟩
  let F := fun a:ℤ => if a∣m ∧ medium (m/a) then w (m/a).natAbs else 0
  rw [show (∑ a∈A, F a) = _ from sum_valuation_cells L A nz F, Finset.sum_filter]
  apply sum_congr rfl
  intro mu _
  dsimp only
  by_cases leq : mu≤v
  · rw [if_pos leq,mul_sum]
    apply sum_congr rfl
    intro s _
    simpa only [if_pos leq] using medium_block_coefficient w L Q mu v s r (A.filter (cell mu s))
      (fun a ha => nz a (mem_filter.mp ha).1) m mnz (fun _ h => (mem_filter.mp h).2) selected
  · rw [if_neg leq]
    apply sum_eq_zero
    intro s _
    simpa only [if_neg leq] using medium_block_coefficient w L Q mu v s r (A.filter (cell mu s))
      (fun a ha => nz a (mem_filter.mp ha).1) m mnz (fun _ h => (mem_filter.mp h).2) selected

end BedertSelection
end

section
namespace BedertSelection
open Finset
open scoped Classical

/-- For the full small-prime sieve, multiplication by a rough frequency leaves
the valuation levels unchanged. Only the single target level can contribute. -/
theorem full_spectrum {R : Type*} [CommSemiring R] (w : ℕ →* R) (L Q : ℕ) (cut : L≤Q)
    (v : ↥(Nat.primesLE L) → ℕ) (r : (ZMod (primorial L))ˣ) (A : Finset ℤ)
    (nz : ∀ a ∈ A, a≠0) (m : ℤ) (mnz : m≠0) :
    let M := primorial L
    letI : NeZero M := ⟨primorial_ne_zero L⟩
    let V := fun u : ↥(Nat.primesLE L) → ℕ => ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
    let cell := fun u (s : (ZMod M)ˣ) (x:ℤ) =>
      x ≡ (V u:ℤ)*((s:ZMod M).val:ℤ) [ZMOD (V u:ℤ)*M]
    let rough := fun n:ℤ => ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣n
    cell v r m → (∑ a∈A, if a∣m ∧ rough (m/a) then w (m/a).natAbs else 0) =
      ∑ s : (ZMod M)ˣ, ∑ a∈A.filter (cell v s), let h := m/a
        if a∣m ∧ (h:ZMod M)*(s:ZMod M)=r ∧ rough h then w h.natAbs else 0 := by
  intro M V cell rough tgt
  let : NeZero M := ⟨primorial_ne_zero L⟩
  let levels := fun a:ℤ => fun p:↥(Nat.primesLE L) => a.natAbs.factorization p
  let F := fun a:ℤ => if a∣m ∧ rough (m/a) then w (m/a).natAbs else 0
  let row := fun u => ∑s:(ZMod M)ˣ, ∑a∈A.filter (cell u s),F a
  have force {a : ℤ} {u} {s} (ha : a∈A) (src : cell u s a) (div : a∣m) (hr : rough (m/a)) :
      u=v ∧ ((m/a:ℤ):ZMod M)*(s:ZMod M)=r := by
    have ma := Int.ediv_mul_cancel div
    have nn : m/a≠0 := fun h => mnz (by rwa [h,zero_mul,eq_comm] at ma)
    have sel : cell v r (m/a*a) := ma.symm ▸ tgt
    obtain ⟨le,vals⟩ := multiplier_valuations L u v s r a (m/a) (nz a ha) nn src sel
    have uv : u=v := by
      funext p
      have zer := Nat.factorization_eq_zero_of_not_dvd (fun d => hr p (Nat.prime_of_mem_primesLE p.property)
        ((Nat.mem_primesLE.mp p.property).1.trans cut) (Int.natCast_dvd.mpr d))
      have h := vals p
      have lo : u p ≤ v p := le p
      omega
    subst u
    obtain ⟨_,h,nh,hs,_⟩ := (projected_multiplier_iff L Q v v s r a (m/a) (nz a ha) nn
      (fun p hp _ hi => hr p hp hi) src).mp sel
    have same : m/a=h := by simpa using nh
    exact ⟨rfl,same ▸ hs⟩
  have last : (∑a∈A,F a) = row v := by
    rw [show (∑a∈A,F a) = ∑u∈A.image levels,row u from sum_valuation_cells L A nz F]
    apply sum_eq_single v
    · intro u _ une
      apply sum_eq_zero
      intro s _
      apply sum_eq_zero
      intro a ha
      exact if_neg (fun h => une (force (mem_filter.mp ha).1 (mem_filter.mp ha).2 h.1 h.2).1)
    · intro absent
      apply sum_eq_zero
      intro s _
      apply sum_eq_zero
      intro a ha
      have eq : levels a=v := funext (valuations_of_cell L v s a (nz a (mem_filter.mp ha).1)
        (mem_filter.mp ha).2)
      exact False.elim (absent (mem_image.mpr ⟨a,(mem_filter.mp ha).1,eq⟩))
  refine last.trans (sum_congr rfl (fun s _ => sum_congr rfl (fun a ha => ?_)))
  dsimp only [F]
  by_cases ok : a∣m ∧ rough (m/a)
  · rw [if_pos ok, if_pos ⟨ok.1,(force (mem_filter.mp ha).1 (mem_filter.mp ha).2 ok.1 ok.2).2,ok.2⟩]
  · rw [if_neg ok,if_neg (fun h => ok ⟨h.1,h.2.2⟩)]

end BedertSelection
end

section
open Finset

namespace GreenLayers

/-- Telescoping over all natural numbers already bounds the small-prime Euler
product sufficiently at the square-root logarithmic cutoff. -/
theorem euler_product_le (L : ℕ) :
    ∏ p ∈ Nat.primesLE L, ((p:ℝ)/((p:ℝ)-1)) ≤ (max 1 L : ℕ) := by
  induction L with
  | zero => simp
  | succ n ih =>
    rw [Nat.primesLE_succ]
    split_ifs with hp
    · have hpos : 0 < n := by have := hp.two_le; omega
      have cast_pos : (0:ℝ) < n := by exact_mod_cast hpos
      have fresh : n + 1 ∉ Nat.primesLE n := by
        intro h
        have := Nat.le_of_mem_primesLE h
        omega
      rw [Finset.prod_insert fresh]
      simp only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right]
      rw [max_eq_right hpos] at ih
      rw [max_eq_right (show 1 ≤ n+1 by omega), Nat.cast_add,Nat.cast_one]
      calc _ ≤ ((n:ℝ)+1)/n*n := mul_le_mul_of_nonneg_left ih (by positivity)
           _ = _ := by field_simp
    · exact ih.trans (by exact_mod_cast max_le_max_left 1 (Nat.le_succ n))

/-- Sum over any finite set of predecessor exponent vectors, with the exact
valuation ratios used in the projected multiplier formula. -/
theorem reciprocal_layers (L : ℕ) (v : ↥(Nat.primesLE L) → ℕ)
    (U : Finset (↥(Nat.primesLE L) → ℕ)) (pre : ∀ u ∈ U, u ≤ v) :
    (∑ u ∈ U, ((∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p-u p) : ℕ):ℝ)⁻¹) ≤
      (max 1 L : ℕ) := by
  classical
  let P := ↥(Nat.primesLE L)
  let f := fun (p:P) (j:ℕ) => ((p:ℕ):ℝ)⁻¹^(v p-j)
  let box := Fintype.piFinset (fun p:P => range (v p+1))
  have ub : U ⊆ box := by
    intro u hu
    apply Fintype.mem_piFinset.mpr
    intro p
    exact mem_range.mpr (Nat.lt_succ_of_le (pre u hu p))
  have primeBound (p:P) : (∑ j ∈ range (v p+1), f p j) ≤ (p:ℕ)/(((p:ℕ):ℝ)-1) := by
    have hp : (1:ℝ)<(p:ℕ) := by exact_mod_cast (Nat.prime_of_mem_primesLE p.property).one_lt
    have hpos : (0:ℝ)<(p:ℕ) := zero_lt_one.trans hp
    have hi : ((p:ℕ):ℝ)⁻¹ < 1 := (inv_lt_one₀ hpos).2 hp
    have revsum := sum_range_reflect (fun j : ℕ => ((p:ℕ):ℝ)⁻¹^j) (v p+1)
    simp only [Nat.add_sub_cancel] at revsum
    rw [show (∑ j ∈ range (v p+1), f p j) = _ from revsum, geom_sum_eq hi.ne]
    calc
      _ = (1-((p:ℕ):ℝ)⁻¹^(v p+1))/(1-((p:ℕ):ℝ)⁻¹) := by rw [← neg_div_neg_eq]; ring_nf
      _ ≤ 1/(1-((p:ℕ):ℝ)⁻¹) := by
        apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hi.le)
        have := pow_nonneg (inv_nonneg.mpr hpos.le) (v p+1)
        linarith
      _ = _ := by field_simp
  calc
    _ = ∑ u ∈ U, ∏ p : P, f p (u p) := by simp only [f,Nat.cast_prod,Nat.cast_pow,Finset.prod_inv_distrib,inv_pow]; rfl
    _ ≤ ∑ u ∈ box, ∏ p : P, f p (u p) := sum_le_sum_of_subset_of_nonneg ub (by intros; dsimp [f]; positivity)
    _ = ∏ p : P, ∑ j ∈ range (v p+1), f p j := (prod_univ_sum _ f).symm
    _ ≤ ∏ p : P, (p:ℕ)/(((p:ℕ):ℝ)-1) := by
      apply prod_le_prod
      · intros; dsimp [f]; positivity
      · exact fun p _ => primeBound p
    _ = _ := Finset.prod_coe_sort (Nat.primesLE L) (fun p => (p:ℝ)/(p-1))
    _ ≤ _ := euler_product_le L

end GreenLayers

open Finset
open scoped Classical

namespace GreenLayers

/-- The finite coefficient ℓ¹ estimate in the rough layer lemma (Bedert 6.9).
For a fixed signed multiplier each source contributes at only one frequency.
The residue restriction gives at most K sources for either sign. -/
theorem rough_tail_mass (A W : Finset ℤ) (k : ℤ) (H K : ℕ)
    (hW : ∀ m∈W, m≠0 ∧ m.natAbs≤H)
    (eligible : ℤ → ℤ → Prop) (w : ℕ → ℂ)
    (weight : ∀ d, ‖w d‖ ≤ (d:ℝ)⁻¹)
    (rows : ∀ h : ℤ, 1<h.natAbs → h.natAbs≤H →
      (A.filter (fun a => eligible a h)).card≤K) :
    let tail := fun m => ∑ a∈A, let h := m/(k*a)
      if k*a ∣ m ∧ 1<h.natAbs ∧ eligible a h then w h.natAbs else 0
    (∑ m∈W, ‖tail m‖) ≤ 2 * (K:ℝ) * (∑ d∈Icc 1 H, (d:ℝ)⁻¹) := by
  classical
  intro tail
  let R (m a h : ℤ) : ℝ := if eligible a h then
    (if k*a*h = m then (h.natAbs:ℝ)⁻¹ else 0) else 0
  let D := Icc 2 H
  have nonneg m a h : 0 ≤ R m a h := by dsimp [R]; split_ifs <;> positivity
  have entry (m a : ℤ) (hm : m∈W) :
      ‖(if k*a ∣ m ∧ 1<(m/(k*a)).natAbs ∧ eligible a (m/(k*a)) then w (m/(k*a)).natAbs else 0)‖ ≤
      ∑ d∈D, (R m a (d:ℤ) + R m a (-(d:ℤ))) := by
    split_ifs with hit
    · let h := m/(k*a)
      have mul : k*a*h=m := Int.mul_ediv_cancel' hit.1
      have divides : h.natAbs ∣ m.natAbs := by
        rw [←mul,Int.natAbs_mul]
        exact dvd_mul_left _ _
      have dh : h.natAbs ∈ D := mem_Icc.mpr ⟨hit.2.1,Nat.le_trans
        (Nat.le_of_dvd (Int.natAbs_pos.mpr (hW m hm).1) divides) (hW m hm).2⟩
      apply (weight h.natAbs).trans
      apply le_trans _ (Finset.single_le_sum (f:= fun d : ℕ => R m a (d:ℤ)+R m a (-(d:ℤ)))
        (fun i _ => add_nonneg (nonneg ..) (nonneg ..)) dh)
      have he : eligible a h := hit.2.2
      have yes : R m a h = (h.natAbs:ℝ)⁻¹ := by simp only [R,if_pos he,if_pos mul]
      rcases Int.natAbs_eq h with pos|neg
      · rw [←yes]
        conv_lhs => rw [pos]
        exact le_add_of_nonneg_right (nonneg ..)
      · rw [←yes]
        conv_lhs => rw [neg]
        exact le_add_of_nonneg_left (nonneg ..)
    · simpa only [norm_zero] using (sum_nonneg fun i (_:i∈D) => add_nonneg (nonneg m a (i:ℤ)) (nonneg m a (-(i:ℤ))))
  have column (h : ℤ) (hl : 1<h.natAbs) (hu : h.natAbs≤H) :
      (∑ m∈W, ∑ a∈A, R m a h) ≤ (K:ℝ)*(h.natAbs:ℝ)⁻¹ := by
    rw [sum_comm]
    calc
      _ ≤ ∑ a∈A, if eligible a h then (h.natAbs:ℝ)⁻¹ else 0 := by
        apply sum_le_sum
        intro a _
        by_cases active : eligible a h
        · simp only [R,if_pos active,sum_ite_eq]
          split_ifs <;> first | rfl | positivity
        · simp [R,active]
      _ = ((A.filter (fun a => eligible a h)).card:ℝ)*(h.natAbs:ℝ)⁻¹ := by
        rw [←sum_filter]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast rows h hl hu) (by positivity)
  calc
    _ ≤ ∑ m∈W, ∑ a∈A, ∑ d∈D, (R m a (d:ℤ) + R m a (-(d:ℤ))) := by
      apply sum_le_sum
      intro m hm
      exact (norm_sum_le _ _).trans (sum_le_sum (fun a _ => entry m a hm))
    _ = ∑ d∈D, ((∑ m∈W, ∑ a∈A, R m a (d:ℤ))+(∑ m∈W, ∑ a∈A, R m a (-(d:ℤ)))) := by
      simp only [←sum_add_distrib]
      simp_rw [sum_comm (s:=A) (t:=D)]
      rw [sum_comm (s:=W) (t:=D)]
    _ ≤ ∑ d∈D, (2*(K:ℝ))*(d:ℝ)⁻¹ := by
      apply sum_le_sum
      intro d hd
      obtain ⟨dl,du⟩ := mem_Icc.mp hd
      have plus := column (d:ℤ) (by simpa using (show 1<d by omega)) (by simpa using du)
      have minus := column (-(d:ℤ)) (by simpa using (show 1<d by omega)) (by simpa using du)
      simp only [Int.natAbs_neg,Int.natAbs_natCast] at plus minus
      linarith
    _ ≤ _ := by
      rw [←mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg (show D ⊆ Icc 1 H from Icc_subset_Icc_left (by decide)) (by intros; positivity)

theorem harmonic_bound (H : ℕ) : (∑ d∈Icc 1 H, (d:ℝ)⁻¹) ≤ 1+Real.log H := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log H

end GreenLayers

open Finset AddCircle
open scoped Classical

namespace GreenLayers

/-- Reflection takes the unit slice -r exactly onto the slice r even though
ZMod.val uses the nonnegative representatives. -/
theorem negative_cell (M V : ℕ) [NeZero M] (r : (ZMod M)ˣ) (a : ℤ) :
    a ≡ (V:ℤ)*(((-r : (ZMod M)ˣ):ZMod M).val:ℤ) [ZMOD (V:ℤ)*M] ↔
      -a ≡ (V:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V:ℤ)*M] := by
  have rr : (((-r : (ZMod M)ˣ):ZMod M).val:ℤ) ≡ -((r:ZMod M).val:ℤ) [ZMOD (M:ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff ..).mp
    simp
  have sr : (V:ℤ)*_ ≡ (V:ℤ)*_ [ZMOD (V:ℤ)*M] := rr.mul_left'
  simp only [mul_neg] at sr
  exact ⟨fun h => by simpa using (h.trans sr).neg,
    fun h => (by simpa using h.neg : a ≡ -((V:ℤ)*((r:ZMod M).val:ℤ)) [ZMOD (V:ℤ)*M]).trans sr.symm⟩

/-- The complete leading packet of a valuation slice survives the plateau of
the cutoff. The two signed packets have disjoint supports in a model of a
set of positive integers. Thus their coefficients on the symmetric cell are
exactly one, as required by the ordered perturbation inequality. -/
theorem top_packets (M V T : ℕ) [NeZero M] (r : (ZMod M)ˣ) (A : Finset ℤ)
    (nz : ∀ a∈A, a≠0) (sign : ∀ a∈A, -a∉A) (radius : ∀ a∈A, a.natAbs ≤ T)
    (cut : ℤ → ℂ) (plateau : ∀ m:ℤ, m.natAbs≤T → cut m=1) :
    let cell := fun (s:(ZMod M)ˣ) (a:ℤ) =>
      a ≡ (V:ℤ)*((s:ZMod M).val:ℤ) [ZMOD (V:ℤ)*M]
    let P := A.filter (cell r)
    let N := (A.filter (cell (-r))).image (fun a => -a)
    let S := P ∪ N
    let W := (Ioo (-((2*T:ℕ):ℤ)) ((2*T:ℕ):ℤ)).filter (fun m => m≠0 ∧ cell r m)
    S = (A ∪ A.image (fun a => -a)).filter (cell r) ∧
    Disjoint P N ∧ P.card≤S.card ∧ S ⊆ W ∧
    (∀ m∈W, m≠0 ∧ m.natAbs≤2*T ∧ cell r m) ∧
    (∀ m∈S, cut m=1) ∧
    (∀ m:ℤ, cut m*((if m∈P then 1 else 0)+(if m∈N then 1 else 0))=
      if m∈S then 1 else 0) ∧
    (∀ m:ℤ, cell r m → cut m*((if m∈P then 1 else 0)+(if m∈N then 1 else 0)) =
      if m∈A ∪ A.image (fun a => -a) then 1 else 0) ∧
    ∀ x:UnitAddCircle,
      ∑ m∈W, (cut m*((if m∈P then 1 else 0)+(if m∈N then 1 else 0)))*fourier m x =
        ∑ m∈S, fourier m x := by
  classical
  intro cell P N S W
  have flip (a:ℤ) : cell (-r) a ↔ cell r (-a) := negative_cell M V r a
  have support : S = (A ∪ A.image (fun a => -a)).filter (cell r) := by
    ext a
    constructor
    · intro mem
      rcases mem_union.mp mem with hp | hn
      · exact mem_filter.mpr ⟨mem_union_left _ (mem_filter.mp hp).1,(mem_filter.mp hp).2⟩
      · obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
        exact mem_filter.mpr ⟨mem_union_right _ (mem_image.mpr ⟨b,(mem_filter.mp hb).1,rfl⟩),
          (flip b).mp (mem_filter.mp hb).2⟩
    · intro mem
      rcases mem_filter.mp mem with ⟨ha,hr⟩
      rcases mem_union.mp ha with hp | hn
      · exact mem_union_left _ (mem_filter.mpr ⟨hp,hr⟩)
      · obtain ⟨b,hb,rfl⟩ := mem_image.mp hn
        exact mem_union_right _ (mem_image.mpr ⟨b,mem_filter.mpr ⟨hb,(flip b).mpr hr⟩,rfl⟩)
  have exclusive : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro m hp hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hn
    exact sign a (mem_filter.mp ha).1 (mem_filter.mp hp).1
  have hs (m:ℤ) (hm:m∈S) : m≠0 ∧ m.natAbs≤T ∧ cell r m := by
    rw [support] at hm
    obtain ⟨incl,hr⟩ := mem_filter.mp hm
    rcases mem_union.mp incl with ha|hneg
    · exact ⟨nz m ha,radius m ha,hr⟩
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp hneg
      simpa only [neg_ne_zero, Int.natAbs_neg] using And.intro (nz a ha) (And.intro (radius a ha) hr)
  have sub : S⊆W := by
    intro m hm
    obtain ⟨mn,mb,mc⟩ := hs m hm
    exact mem_filter.mpr ⟨mem_Ioo.mpr (by omega),mn,mc⟩
  have ones (m:ℤ) (hm:m∈S) := plateau m (hs m hm).2.1
  have weight (m:ℤ) : cut m*((if m∈P then 1 else 0)+(if m∈N then 1 else 0))=
      if m∈S then 1 else 0 := by
    by_cases hp : m∈P
    · have hn : m∉N := Finset.disjoint_left.mp exclusive hp
      have mem : m∈S := mem_union_left _ hp
      simp [hp,hn,mem,ones m mem]
    · by_cases hn : m∈N
      · have mem : m∈S := mem_union_right _ hn
        simp [hp,hn,mem,ones m mem]
      · have mem : m∉S := by simpa [S,hp] using hn
        simp [hp,hn,mem]
  refine ⟨support,exclusive,card_le_card (subset_union_left),sub,?_,ones,weight,?_,?_⟩
  · intro m hm
    obtain ⟨mI,mn,mc⟩ := mem_filter.mp hm
    have := mem_Ioo.mp mI; exact ⟨mn,by omega,mc⟩
  · intro m hm
    rw [weight,support]; simp [hm]
  · intro x
    simp_rw [weight,ite_mul,one_mul,zero_mul]
    rw [←sum_filter]
    have ws : W.filter (fun m => m∈S) = S := by
      ext m; simp only [mem_filter]; exact ⟨And.right,fun h=>⟨sub h,h⟩⟩
    rw [ws]

end GreenLayers

open MeasureTheory Finset AddCircle

namespace GreenLayers

/-- The ℓ² norm of a filtered coefficient packet with distinct frequencies is
bounded by the square root of the packet size, including after a cutoff. -/
theorem packet_norm (W S : Finset ℤ) (a : ℤ → ℂ) (ha : ∀ n∈W, ‖a n‖ ≤ 1) :
    ‖(WithLp.toLp 2 (fun i : ↥W => if (i:ℤ) ∈ S then a i else 0) :
      EuclideanSpace ℂ ↥W)‖^2 ≤ (S.card:ℝ) := by
  classical
  rw [EuclideanSpace.norm_sq_eq]
  let D := W.filter (fun n => n ∈ S)
  calc
    _ = ∑ i ∈ W, ‖if i ∈ S then a i else 0‖^2 := Finset.sum_coe_sort W _
    _ = ∑ i ∈ D, ‖a i‖^2 := by simp only [D,sum_filter]; apply sum_congr rfl; intro n _; split_ifs <;> simp
    _ ≤ ∑ _i ∈ D, (1:ℝ) := by
      apply sum_le_sum
      intro n hn
      simpa using pow_le_pow_left₀ (norm_nonneg (a n)) (ha n (mem_filter.mp hn).1) 2
    _ ≤ _ := by
      simp only [sum_const, nsmul_eq_mul,mul_one]
      exact_mod_cast card_le_card (show D ⊆ S from fun n hn => (mem_filter.mp hn).2)

/-- Bedert's valuation-layer contamination estimate (Lemma 7.14), after any
finite Fourier cutoff. A per-layer tail of energy at most d² and two leading
packets of size at most d² off the distinguished layer contribute total energy
at most (3 max(1,L) d)². The weights have exactly the prime-power denominators
from the medium-sieve factorization. -/
theorem layer_error (L : ℕ) (v : ↥(Nat.primesLE L) → ℕ)
    (U : Finset (↥(Nat.primesLE L) → ℕ)) (pre : ∀ u ∈ U, u ≤ v)
    (W : Finset ℤ) (cut : ℤ → ℂ) (bounded : ∀ m ∈ W, ‖cut m‖ ≤ 1)
    (tail : (↥(Nat.primesLE L) → ℕ) → ℤ → ℂ)
    (A B : (↥(Nat.primesLE L) → ℕ) → Finset ℤ)
    (w : (↥(Nat.primesLE L) → ℕ) → ℂ) (d : ℝ) (hd : 0 ≤ d)
    (coef : ∀ u∈U, ‖w u‖ ≤ ((∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p-u p) : ℕ):ℝ)⁻¹)
    (tails : ∀ u∈U, (∑ m∈W, ‖tail u m‖^2) ≤ d^2)
    (small : ∀ u∈U, u≠v → ((A u).card:ℝ) ≤ d^2 ∧ ((B u).card:ℝ) ≤ d^2) :
    let coeff := fun m => ∑ u∈U, w u * (tail u m + (if u=v then 0 else
      (if m∈A u then cut m else 0) + (if m∈B u then cut m else 0)))
    (∫ x : UnitAddCircle, ‖∑ m∈W, coeff m*fourier m x‖^2 ∂haarAddCircle) ≤
      (3 * (max 1 L : ℕ) * d)^2 := by
  classical
  intro coeff
  let V := ↥(Nat.primesLE L) → ℕ
  let H := EuclideanSpace ℂ ↥W
  let noise (u : V) : H := WithLp.toLp 2 (fun i : ↥W => tail u i)
  let packet (S : Finset ℤ) : H := WithLp.toLp 2 fun i : ↥W => if (i:ℤ)∈S then cut i else 0
  let head (u : V) : H := if u=v then 0 else packet (A u) + packet (B u)
  have boundNoise (u : V) (hu : u∈U) : ‖noise u‖ ≤ d := by
    rw [←sq_le_sq₀ (norm_nonneg _) hd,EuclideanSpace.norm_sq_eq]
    exact (Finset.sum_coe_sort W (fun i => ‖tail u i‖^2)).le.trans (tails u hu)
  have boundHead (u : V) (hu : u∈U) : ‖head u‖ ≤ 2*d := by
    by_cases eq : u=v
    · simpa [head,eq] using (show 0 ≤ 2*d by positivity)
    · simp only [head,if_neg eq]
      apply (norm_add_le _ _).trans
      have single (S : Finset ℤ) (sz : (S.card:ℝ) ≤ d^2) : ‖packet S‖ ≤ d :=
        (sq_le_sq₀ (norm_nonneg _) hd).mp ((packet_norm W S cut bounded).trans sz)
      linarith [single (A u) (small u hu eq).1,single (B u) (small u hu eq).2]
  let T : H := ∑ u∈U, w u • (noise u + head u)
  have val (i : ↥W) : T i = coeff i := by
    change (∑ u∈U, w u • (noise u + head u)) i = _
    change (PiLp.projₗ (𝕜:=ℂ) 2 (fun _ : ↥W => ℂ) i) (∑ u∈U, w u • (noise u + head u)) = _
    rw [map_sum]
    apply sum_congr rfl
    intro u _
    change w u * (noise u i + head u i) = _
    by_cases hu : u = v <;> simp only [head,hu,if_true,if_false,PiLp.zero_apply] <;> rfl
  have bound : ‖T‖ ≤ 3*(max 1 L : ℕ)*d := calc
    _ ≤ ∑ u∈U, ‖w u • (noise u + head u)‖ := norm_sum_le _ _
    _ ≤ ∑ u∈U, ((∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p-u p) : ℕ):ℝ)⁻¹ * (3*d) := by
      apply sum_le_sum
      intro u hu
      rw [norm_smul]
      apply mul_le_mul (coef u hu) _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (by linarith [boundNoise u hu,boundHead u hu])
    _ ≤ _ := by
      rw [← sum_mul]
      calc _ ≤ (max 1 L:ℕ)*(3*d) := mul_le_mul_of_nonneg_right (reciprocal_layers L v U pre) (by positivity)
           _ = _ := by ring
  rw [BedertTest.trig_square]
  have eq : ‖T‖^2 = ∑ m∈W, ‖coeff m‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp_rw [val]
    exact Finset.sum_coe_sort W (fun n => ‖coeff n‖^2)
  rw [←eq]
  exact pow_le_pow_left₀ (norm_nonneg _) bound 2

end GreenLayers

open Finset
open scoped Classical

namespace GreenLayers

/-- Coefficient version of the layer estimate, with the top packet subtracted
from the actual finite medium spectrum. Only the raw tails, before cutting,
are needed to express the coefficient identity. -/
theorem layer_discrepancy (L : ℕ) (v : ↥(Nat.primesLE L) → ℕ)
    (U : Finset (↥(Nat.primesLE L) → ℕ)) (pre : ∀ u ∈ U, u ≤ v) (top : v∈U)
    (W : Finset ℤ) (cut : ℤ → ℂ) (bounded : ∀ m ∈ W, ‖cut m‖ ≤ 1)
    (tail : (↥(Nat.primesLE L) → ℕ) → ℤ → ℂ)
    (A B : (↥(Nat.primesLE L) → ℕ) → Finset ℤ)
    (w : (↥(Nat.primesLE L) → ℕ) → ℂ) (d : ℝ) (hd : 0 ≤ d)
    (coef : ∀ u∈U, ‖w u‖ ≤ ((∏ p : ↥(Nat.primesLE L), (p:ℕ)^(v p-u p) : ℕ):ℝ)⁻¹)
    (unit : w v = 1)
    (tails : ∀ u∈U, (∑ m∈W, ‖cut m * tail u m‖^2) ≤ d^2)
    (small : ∀ u∈U, u≠v → ((A u).card:ℝ) ≤ d^2 ∧ ((B u).card:ℝ) ≤ d^2)
    (raw head : ℤ → ℂ)
    (decomp : ∀ m∈W, raw m = ∑ u∈U, w u*((if m∈A u then 1 else 0) +
      (if m∈B u then 1 else 0)+tail u m))
    (main : ∀ m∈W, cut m*((if m∈A v then 1 else 0)+(if m∈B v then 1 else 0))=head m) :
    ∑ m∈W, ‖cut m*raw m-head m‖^2 ≤ (3*(max 1 L : ℕ)*d)^2 := by
  classical
  have h := layer_error L v U pre W cut bounded (fun u m => cut m * tail u m)
    A B w d hd coef tails small
  dsimp only at h
  rw [BedertTest.trig_square] at h
  refine le_trans (le_of_eq (sum_congr rfl ?_)) h
  intro m hm
  congr 2
  have point : head m = ∑ u∈U, if u=v then head m else 0 := by simp [top]
  rw [decomp m hm,mul_sum,point,←sum_sub_distrib]
  apply sum_congr rfl
  intro u _
  by_cases eq : u=v
  · subst u
    simp only [if_true,unit,one_mul,← main m hm]
    ring
  · simp only [eq,if_false,sub_zero]
    by_cases a : m∈A u <;> by_cases b : m∈B u <;> simp [a,b] <;> ring

end GreenLayers

open Filter
namespace GreenLayers

/-- The actual radius in the low-dimensional reduction against the two sieve
cutoffs. The constants are uniform in the chosen valuation layer and frequency. -/
theorem eventually_noise_scales (C : ℝ) (J : ℕ) :
    ∀ᶠ n : ℕ in atTop,
    let z := Real.log n
    let k := ⌈z^4⌉₊
    let H := 2*(16*(k+1))^k
    let Q := ⌊z^20⌋₊
    let L := ⌊Real.sqrt z⌋₊
    0 < H ∧ 0<Q ∧ L≤Q ∧
    2*Real.log H ≤ Q*Real.log 2 ∧
    C*(1+Real.log H)^2/(Q:ℝ) ≤ 1/z^4 ∧
    (3*(max 1 L:ℕ):ℝ)^2/z^4 ≤ 1/z^2 ∧
    1/z^4 ≤ 1/100 ∧
    ((4096^(J+1):ℕ):ℝ) ≤ z := by
  have tend : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [tend.eventually_ge_atTop (max (100:ℝ) (max (2*max 1 C*106^2) (424/Real.log 2))),
    tend.eventually_ge_atTop (((4096^(J+1)):ℕ):ℝ)] with n nb num
  intro z k H Q L
  have zone : 1≤z := by dsimp [z]; exact le_trans (by norm_num) ((le_max_left _ _).trans nb)
  have big : 100≤z := (le_max_left _ _).trans nb
  have cst : 2*max 1 C*106^2 ≤ z := (le_max_left _ _).trans ((le_max_right _ _).trans nb)
  have biglog : 424 ≤ z*Real.log 2 := (div_le_iff₀ l2).mp
    ((le_max_right _ _).trans ((le_max_right _ _).trans nb))
  have zp : 0<z := zero_lt_one.trans_le zone
  have Hp : 0<H := by dsimp [H]; positivity
  have Hlog : 0≤Real.log H := Real.log_nonneg (by exact_mod_cast Hp)
  have radius := GreenOneFinal.model_radius_growth (n:=n) zone
  change Real.log (↑((16*(k+1))^k):ℝ) ≤ 104*z^5 at radius
  have five : 1≤z^5 := one_le_pow₀ zone
  have bound : 1+Real.log H ≤ 106*z^5 := by
    dsimp only [H]
    rw [Nat.cast_mul,Real.log_mul (by norm_num) (by positivity : (↑((16*(k+1))^k):ℝ)≠0)]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have qfloor := Nat.lt_floor_add_one (z^20)
  change z^20 < (Q:ℝ)+1 at qfloor
  have powstep (a b : ℕ) (h : a≤b) : z^a ≤ z^b := pow_le_pow_right₀ zone h
  have twenty : 2≤z^20 := by linarith [powstep 1 20 (by decide),pow_one z]
  have qbound : z^20 ≤ 2*(Q:ℝ) := by linarith
  have qp : 0<Q := by exact_mod_cast (show 0<(Q:ℝ) by linarith)
  have zQ : z ≤ (Q:ℝ) := by
    have h := powstep 2 20 (by decide)
    have g : 2*z ≤ z^2 := by nlinarith [mul_nonneg (show 0≤z-2 by linarith) zp.le]
    linarith
  have sq : (Real.sqrt z)^2=z := Real.sq_sqrt zp.le
  have rs : 1 ≤ Real.sqrt z := (Real.one_le_sqrt).mpr zone
  have cut : (L:ℝ) ≤ Real.sqrt z := Nat.floor_le (Real.sqrt_nonneg _)
  have maxcut : ((max 1 L : ℕ):ℝ) ≤ Real.sqrt z := by
    rw [Nat.cast_max,Nat.cast_one]; exact max_le rs cut
  refine ⟨Hp,qp,?_,?_,?_,?_,?_,num⟩
  · have sr : Real.sqrt z ≤ z := by nlinarith [mul_nonneg (sub_nonneg.mpr rs) (Real.sqrt_nonneg z)]
    exact_mod_cast (cut.trans (sr.trans zQ))
  · have aux : 424*z^5 ≤ z^20*Real.log 2 := calc
      _ ≤ (z*Real.log 2)*z^5 := mul_le_mul_of_nonneg_right biglog (by positivity)
      _ = z^6*Real.log 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (powstep 6 20 (by decide)) l2.le
    linarith [mul_le_mul_of_nonneg_right qbound l2.le]
  · rw [div_le_div_iff₀ (by exact_mod_cast qp) (by positivity)]
    rw [one_mul]
    have g : C*(1+Real.log H)^2*z^4 ≤ (max 1 C*106^2)*z^14 := calc
      _ ≤ max 1 C*(106*z^5)^2*z^4 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (by linarith) bound 2) (sq_nonneg _) (by positivity)
      _ = _ := by ring
    have u : (2*max 1 C*106^2)*z^14 ≤ z^20 := calc
      _ ≤ z*z^14 := mul_le_mul_of_nonneg_right cst (by positivity)
      _ = z^15 := by ring
      _ ≤ _ := powstep 15 20 (by decide)
    linarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
    have hf : (3*((max 1 L:ℕ):ℝ))^2 ≤ 9*z := calc
      _ ≤ (3*Real.sqrt z)^2 := pow_le_pow_left₀ (by positivity) (by gcongr) 2
      _ = _ := by rw [mul_pow,sq]; norm_num
    calc _ ≤ (9*z)*z^2 := mul_le_mul_of_nonneg_right hf (by positivity)
         _ = 9*z^3 := by ring
         _ ≤ z*z^3 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
         _ = _ := by ring
  · apply one_div_le_one_div_of_le (by norm_num)
    simpa using big.trans (by simpa using powstep 1 4 (by decide))

/-- Direct normalization of the product of the signed-divisor supremum and
the signed-multiplier mass, plus the comparison with the ordered and
non-Archimedean perturbation tolerances. -/
theorem eventually_noise_energy (J : ℕ) :
    ∀ᶠ n : ℕ in atTop,
    let z := Real.log n
    let k := ⌈z^4⌉₊
    let H := 2*(16*(k+1))^k
    let Q := ⌊z^20⌋₊
    let L := ⌊Real.sqrt z⌋₊
    0 < H ∧ 0<Q ∧ L≤Q ∧ 2*Real.log H ≤ Q*Real.log 2 ∧
    ∀ S : ℝ, 0 ≤ S →
      let d := Real.sqrt S / z^2
      (4*Real.log H/(Real.log 2*Q))*(2*S*(1+Real.log H)) ≤ d^2 ∧
      d^2 ≤ S/100 ∧
      (3*(max 1 L:ℕ)*d)^2 ≤ S/((4096^(J+1):ℕ):ℝ)^2 := by
  have tend : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_noise_scales (8/Real.log 2) J,tend.eventually_ge_atTop 1]
    with n bounds zn
  intro z k H Q L
  obtain ⟨hp,qp,lq,rough,per,aggregate,hundred,packet⟩ := bounds
  refine ⟨hp,qp,lq,rough,?_⟩
  intro S s d
  have lp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have qpos : 0 < (Q:ℝ) := by exact_mod_cast qp
  have lh : 0 ≤ Real.log H := Real.log_nonneg (by exact_mod_cast hp)
  have zp : 0 < z := zero_lt_one.trans_le zn
  have ds : d^2 = S * (1/z^4) := by
    dsimp only [d]; rw [div_pow,Real.sq_sqrt s]; ring
  refine ⟨?_,?_,?_⟩
  · rw [ds]
    calc _ ≤ (4*(1+Real.log H)/(Real.log 2*Q))*(2*S*(1+Real.log H)) := by
              gcongr; linarith
         _ = S*((8/Real.log 2)*(1+Real.log H)^2/Q) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left per s
  · rw [ds]
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hundred s
  · have e : 0<((4096^(J+1):ℕ):ℝ) := by positivity
    calc _ = S*((3*(max 1 L:ℕ):ℝ)^2/z^4) := by rw [mul_pow,ds]; ring
         _ ≤ S*(1/z^2) := mul_le_mul_of_nonneg_left aggregate s
         _ ≤ _ := by
           rw [←div_eq_mul_one_div]
           exact div_le_div_of_nonneg_left s (by positivity) (pow_le_pow_left₀ e.le packet 2)

end GreenLayers
end

section
open Finset
namespace GreenRough

/-- Removing one prime factor injects each nonunit rough divisor into a pair.
Summing 1/d first over this image avoids estimating the divisor count. -/
theorem reciprocal_recursion (D P : Finset ℕ) (Q : ℕ) (pos : 0 < Q)
    (one : 1 ∈ D)
    (fac : ∀ d ∈ D.erase 1, ∃ p ∈ P, Q ≤ p ∧ ∃ q ∈ D, 0 < q ∧ d = p*q) :
    (Q : ℝ) * (∑ d ∈ D.erase 1, (d : ℝ)⁻¹) ≤
      (P.card : ℝ) * ((∑ d ∈ D.erase 1, (d : ℝ)⁻¹) + 1) := by
  classical
  let f (d : ℕ) : ℕ × ℕ :=
    if h : d ∈ D.erase 1 then
      ((fac d h).choose, (fac d h).choose_spec.2.2.choose) else (0,0)
  have hf (d : ℕ) (hd : d ∈ D.erase 1) :
      (f d).1 ∈ P ∧ Q ≤ (f d).1 ∧ (f d).2 ∈ D ∧ 0 < (f d).2 ∧
        d = (f d).1 * (f d).2 := by
    simp only [f, dif_pos hd]
    obtain ⟨hp, hq, rest⟩ := (fac d hd).choose_spec
    exact ⟨hp, hq, rest.choose_spec⟩
  have hj : Set.InjOn f ↑(D.erase 1) := by
    intro u hu v hv he
    rw [(hf u hu).2.2.2.2,(hf v hv).2.2.2.2,he]
  let w (z : ℕ × ℕ) := (z.2 : ℝ)⁻¹
  have he : ((D.erase 1).image f) ⊆ P ×ˢ D := by
    intro z hz
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hz
    exact mem_product.mpr ⟨(hf d hd).1, (hf d hd).2.2.1⟩
  calc
    _ = ∑ d ∈ D.erase 1, (Q:ℝ) * (d:ℝ)⁻¹ := mul_sum ..
    _ ≤ ∑ d ∈ D.erase 1, w (f d) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_, hp, _, hq, eq⟩ := hf d hd
      have hp' : (0:ℝ) < (f d).1 := by exact_mod_cast lt_of_lt_of_le pos hp
      have hq' : (0:ℝ) < (f d).2 := by exact_mod_cast hq
      simp only [w]
      conv_lhs => rw [eq, Nat.cast_mul]
      field_simp
      exact_mod_cast hp
    _ = ∑ z ∈ (D.erase 1).image f, w z := (sum_image hj).symm
    _ ≤ ∑ z ∈ P ×ˢ D, w z := sum_le_sum_of_subset_of_nonneg he (fun _ _ _ ↦ by dsimp [w]; positivity)
    _ = _ := by
      rw [sum_product]
      simp only [w, sum_const, nsmul_eq_mul]
      rw [← sum_erase_add _ _ one]
      simp

theorem reciprocal_bound (m Q : ℕ) (hm : 0 < m) (hq : 0 < Q)
    (few : 2 * m.primeFactors.card ≤ Q) :
    let D := m.divisors.filter (fun d ↦ ∀ p ∈ d.primeFactors, Q ≤ p)
    ∑ d ∈ D.erase 1, (d:ℝ)⁻¹ ≤ 2 * m.primeFactors.card / (Q:ℝ) := by
  intro D
  have one : 1 ∈ D := by simp [D, hm.ne']
  have h := reciprocal_recursion D m.primeFactors Q hq one (by
    intro d hd
    obtain ⟨hne, hd⟩ := mem_erase.mp hd
    obtain ⟨div, rough⟩ := mem_filter.mp hd
    have dpos := Nat.pos_of_mem_divisors div
    have dvd := (Nat.mem_divisors.mp div).1
    let p := d.minFac
    have pp : p.Prime := Nat.minFac_prime hne
    have pd : p ∣ d := Nat.minFac_dvd d
    have eq : d = p * (d/p) := (Nat.mul_div_cancel' pd).symm
    have qd : d/p ∣ d := ⟨p, by simpa only [mul_comm] using eq⟩
    have qp : 0 < d/p := by by_contra! hz; rw [Nat.eq_zero_of_le_zero hz, mul_zero] at eq; omega
    refine ⟨p, Nat.mem_primeFactors.mpr ⟨pp,pd.trans dvd,hm.ne'⟩,
      rough p (Nat.mem_primeFactors.mpr ⟨pp,pd,dpos.ne'⟩), d/p, ?_, qp, eq⟩
    refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨qd.trans dvd,hm.ne'⟩,?_⟩
    intro l hl
    obtain ⟨lp,ld,_⟩ := Nat.mem_primeFactors.mp hl
    exact rough l (Nat.mem_primeFactors.mpr ⟨lp,ld.trans qd,dpos.ne'⟩))
  have f : (2:ℝ) * m.primeFactors.card ≤ Q := by exact_mod_cast few
  have u : 0 ≤ ∑ d ∈ D.erase 1, (d:ℝ)⁻¹ := sum_nonneg (fun _ _ ↦ by positivity)
  apply (le_div_iff₀ (by exact_mod_cast hq)).mpr
  nlinarith [mul_nonneg (show 0 ≤ (Q:ℝ)-2*m.primeFactors.card by linarith) u]

lemma factor_card_log (m : ℕ) (hm : 0 < m) :
    (m.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log m := by
  have prod : 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
    simpa using (Finset.prod_le_prod' (s := m.primeFactors) (f := fun _ ↦ (2:ℕ))
      (g := id) (fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le))
  have total := prod.trans (Nat.le_of_dvd hm m.prod_primeFactors_dvd)
  have hreal : (2:ℝ)^m.primeFactors.card ≤ m := by exact_mod_cast total
  simpa only [Real.log_pow] using Real.log_le_log (by positivity) hreal

end GreenRough
end

section
open Finset
open scoped Classical
namespace GreenDistribution

/-- A fixed signed divisor determines its source. There can be at most two
sources for an absolute divisor, even if the source set contains opposites. -/
theorem rough_tail_sup (A : Finset ℤ) (k m : ℤ) (hk : k ≠ 0) (hm : m ≠ 0)
    (Q : ℕ) (hQ : 0<Q) (few : 2*m.natAbs.primeFactors.card≤Q)
    (eligible : ℤ → ℤ → Prop)
    (rough : ∀ a∈A, ∀ h, eligible a h → ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣h)
    (w : ℕ → ℂ) (weight : ∀ d, ‖w d‖ ≤ (d:ℝ)⁻¹) :
    ‖∑ a∈A, let h := m/(k*a)
      if k*a ∣ m ∧ 1<h.natAbs ∧ eligible a h then w h.natAbs else 0‖ ≤
      4*m.natAbs.primeFactors.card/(Q:ℝ) := by
  classical
  let h (a:ℤ) := m/(k*a)
  let B := A.filter fun a => k*a∣m ∧ 1<(h a).natAbs ∧ eligible a (h a)
  let D := (m.natAbs.divisors.filter (fun d => ∀ p∈d.primeFactors, Q≤p)).erase 1
  have spec {a} (ha : a∈B) := (mem_filter.mp ha).2
  have mul {a} (ha : a∈B) : k*a*h a=m := Int.mul_ediv_cancel' (spec ha).1
  have nz {a} (ha : a∈B) : h a ≠ 0 := fun z => hm (by simpa only [z,mul_zero] using (mul ha).symm)
  have inject : Set.InjOn h (↑B) := by
    intro a ha b hb eq
    have rel := (mul ha).trans (mul hb).symm
    rw [eq] at rel
    exact mul_left_cancel₀ hk (mul_right_cancel₀ (nz hb) rel)
  have member {a} (ha : a∈B) : (h a).natAbs ∈ D := by
    have pos := Int.natAbs_pos.mpr hm
    have div : (h a).natAbs ∣ m.natAbs := by
      have eq := congrArg Int.natAbs (mul ha); rw [Int.natAbs_mul] at eq
      rw [←eq]; exact dvd_mul_left _ _
    refine mem_erase.mpr ⟨by have := (spec ha).2.1; omega,
      mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨div,pos.ne'⟩,?_⟩⟩
    intro p hp
    obtain ⟨prime,pd,_⟩ := Nat.mem_primeFactors.mp hp
    by_contra! lt
    exact rough a (mem_filter.mp ha).1 (h a) (spec ha).2.2 p prime lt.le (Int.natCast_dvd.mpr pd)
  let absWeight (z:ℤ) := (z.natAbs:ℝ)⁻¹
  let plus (d:ℕ) := (d:ℤ)
  let minus (d:ℕ) := -(d:ℤ)
  have sub : B.image h ⊆ D.image plus ∪ D.image minus := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    rcases Int.natAbs_eq (h a) with hp | hn
    · exact mem_union_left _ (mem_image.mpr ⟨_,member ha,hp.symm⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨_,member ha,hn.symm⟩)
  have posinj : Set.InjOn plus (↑D) := fun a _ b _ e => Int.ofNat_inj.mp e
  have neginj : Set.InjOn minus (↑D) := by
    intro a _ b _ e; exact Int.ofNat_inj.mp (neg_inj.mp e)
  have bound := GreenRough.reciprocal_bound m.natAbs Q (Int.natAbs_pos.mpr hm) hQ few
  change ∑ d∈D, (d:ℝ)⁻¹ ≤ _ at bound
  change ‖∑ a∈A, if k*a∣m ∧ 1<(h a).natAbs ∧ eligible a (h a) then w (h a).natAbs else 0‖ ≤ _
  rw [←sum_filter]
  change ‖∑ a∈B, w (h a).natAbs‖ ≤ _
  calc
    _ ≤ ∑ a∈B, absWeight (h a) :=
      (norm_sum_le _ _).trans (sum_le_sum fun a _ => weight (h a).natAbs)
    _ = ∑ z∈B.image h, absWeight z := (sum_image inject).symm
    _ ≤ ∑ z∈D.image plus ∪ D.image minus, absWeight z :=
      sum_le_sum_of_subset_of_nonneg sub (by intros; dsimp [absWeight]; positivity)
    _ ≤ (∑ z∈D.image plus, absWeight z)+(∑ z∈D.image minus, absWeight z) := by
      rw [←sum_union_inter]
      exact le_add_of_nonneg_right (sum_nonneg (by intros; dsimp [absWeight]; positivity))
    _ = (∑ d∈D, (d:ℝ)⁻¹)+(∑ d∈D, (d:ℝ)⁻¹) := by
      rw [sum_image posinj,sum_image neginj]
      simp only [absWeight,plus,minus,Int.natAbs_neg,Int.natAbs_natCast]
    _ ≤ _ := (add_le_add bound bound).trans_eq (by ring)

end GreenDistribution
end

section
open Finset
open scoped Classical
namespace GreenDistribution

/-- After a contraction on its Fourier coefficients the rough part of a
single layer has energy O(K log² H / Q), uniformly in the dilation. -/
theorem rough_tail_energy (A W : Finset ℤ) (k : ℤ) (hk : k≠0) (H Q K : ℕ)
    (hQ : 0<Q) (pos : 0<H)
    (hW : ∀ m∈W, m≠0 ∧ m.natAbs≤H)
    (few : 2*Real.log (H:ℝ) ≤ Q*Real.log 2)
    (eligible : ℤ → ℤ → Prop)
    (rough : ∀ a∈A, ∀ h, eligible a h → ∀ p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣h)
    (rows : ∀ h:ℤ, 1<h.natAbs → h.natAbs≤H → (A.filter (fun a => eligible a h)).card≤K)
    (w : ℕ → ℂ) (weight : ∀ d, ‖w d‖≤(d:ℝ)⁻¹)
    (cut : ℤ → ℂ) (contraction : ∀ m∈W, ‖cut m‖≤1) :
    let tail := fun m => ∑ a∈A, let h := m/(k*a)
      if k*a ∣ m ∧ 1<h.natAbs ∧ eligible a h then w h.natAbs else 0
    (∑ m∈W, ‖cut m*tail m‖^2) ≤
      (4*Real.log H/(Real.log 2*Q))*(2*K*(1+Real.log H)) := by
  classical
  intro tail
  have l2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have qpos : (0:ℝ)<Q := by exact_mod_cast hQ
  have Hge : (1:ℝ)≤H := by exact_mod_cast pos
  have lH : 0≤Real.log H := Real.log_nonneg Hge
  have inf (m : ℤ) (hm : m∈W) : ‖tail m‖ ≤ 4*Real.log H/(Real.log 2*Q) := by
    obtain ⟨mnz,mb⟩ := hW m hm
    have logm := (GreenRough.factor_card_log m.natAbs (Int.natAbs_pos.mpr mnz)).trans
      (Real.log_le_log (by exact_mod_cast (Int.natAbs_pos.mpr mnz)) (show (m.natAbs:ℝ)≤(H:ℝ) by exact_mod_cast mb))
    have few' : 2*m.natAbs.primeFactors.card≤Q := by
      have l : (2*(m.natAbs.primeFactors.card:ℝ))*Real.log 2 ≤ (Q:ℝ)*Real.log 2 := by linarith
      exact_mod_cast (le_of_mul_le_mul_right l l2)
    apply (rough_tail_sup A k m hk mnz Q hQ few' eligible rough w weight).trans
    rw [div_le_div_iff₀ qpos (mul_pos l2 qpos)]
    nlinarith [mul_nonneg (show 0 ≤ Real.log H-(m.natAbs.primeFactors.card:ℝ)*Real.log 2 by linarith) qpos.le]
  have mass := GreenLayers.rough_tail_mass A W k H K hW eligible w weight rows
  change ∑m∈W, ‖tail m‖ ≤ _ at mass
  have mass' := mass.trans (mul_le_mul_of_nonneg_left (GreenLayers.harmonic_bound H)
    (show 0≤2*(K:ℝ) by positivity))
  calc
    _ ≤ ∑m∈W, (4*Real.log H/(Real.log 2*Q))*‖tail m‖ := by
      apply sum_le_sum
      intro m hm
      have cap : ‖cut m * tail m‖ ≤ ‖tail m‖ := by
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right (contraction m hm) (norm_nonneg (tail m))
      rw [pow_two]
      exact mul_le_mul (cap.trans (inf m hm)) cap (norm_nonneg _) ((norm_nonneg _).trans (inf m hm))
    _ = _ * ∑m∈W, ‖tail m‖ := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left mass' (by positivity)

end GreenDistribution
end

section
open Finset
open scoped Classical
namespace GreenDistribution

/-- A unit residue of a source is unique once its valuation vector is fixed. -/
theorem cell_unique (V M : ℕ) [NeZero M] (v : V≠0) (x : ℤ)
    (r s : (ZMod M)ˣ)
    (first : x ≡ (V:ℤ)*((r:ZMod M).val:ℤ) [ZMOD (V:ℤ)*M])
    (second : x ≡ (V:ℤ)*((s:ZMod M).val:ℤ) [ZMOD (V:ℤ)*M]) : r=s := by
  have eq := Int.ModEq.mul_left_cancel' (Nat.cast_ne_zero.mpr v) (first.symm.trans second)
  apply Units.ext
  simpa using (ZMod.intCast_eq_intCast_iff _ _ _).mpr eq

/-- The two unit multipliers give exactly the positive and negative
dilations of the bins r and -r. All remaining multipliers have absolute
value greater than one. -/
theorem split_bin (A : Finset ℤ) (S : ℤ → Prop) (k m : ℤ) (hk : k≠0)
    (nz : ∀a∈A, a≠0) (mnz : m≠0) (M Q : ℕ) (s r : (ZMod M)ˣ)
    (w : ℕ →* ℂ) :
    let rough := fun h:ℤ => ∀p:ℕ,p.Prime → p≤Q → ¬(p:ℤ)∣h
    let ok := fun h:ℤ => (h:ZMod M)*(s:ZMod M)=r ∧ rough h
    let B := A.filter S
    (∑ a∈B, let h := m/(k*a); if k*a∣m ∧ ok h then w h.natAbs else 0) =
      (if s=r ∧ m∈B.image (fun a => k*a) then 1 else 0) +
      (if s= -r ∧ m∈B.image (fun a => -(k*a)) then 1 else 0) +
      ∑ a∈B, let h := m/(k*a); if k*a∣m ∧ 1<h.natAbs ∧ ok h then w h.natAbs else 0 := by
  classical
  intro rough ok B
  have onerough : rough 1 := by
    intro p hp _ h
    have eq := Int.natCast_dvd.mp h
    exact hp.ne_one (Nat.dvd_one.mp (by simpa using eq))
  have negrough : rough (-1) := by
    intro p hp hq hn
    exact onerough p hp hq ((dvd_neg.mp hn))
  have op : ok 1 ↔ s=r := by simp [ok,onerough,Units.ext_iff]
  have om : ok (-1) ↔ s= -r := by simp [ok,negrough,Units.ext_iff,neg_eq_iff_eq_neg]
  let f (a:ℤ) := k*a
  have nonzero (a:ℤ) (ha:a∈B) : f a ≠0 := mul_ne_zero hk (nz a (mem_filter.mp ha).1)
  have inj : Function.Injective f := fun _ _ h => mul_left_cancel₀ hk h
  have inj' : Function.Injective (fun a=> -(f a)) := fun _ _ h => inj (neg_inj.mp h)
  have term (a:ℤ) (ha:a∈B) :
      (if f a∣m ∧ ok (m/f a) then w (m/f a).natAbs else 0) =
        (if s=r ∧ f a=m then 1 else 0)+(if s= -r ∧ -(f a)=m then 1 else 0)+
        (if f a∣m ∧ 1<(m/f a).natAbs ∧ ok (m/f a) then w (m/f a).natAbs else 0) := by
    have fn := nonzero a ha
    by_cases positive : f a=m
    · have q : m/f a=1 := by rw [←positive,Int.ediv_self fn]
      have nd : -(f a)≠m := by omega
      have d : f a∣m := positive ▸ dvd_refl (f a)
      rw [q]
      simp only [op,Int.natAbs_one,map_one,d, not_lt_of_ge le_rfl, true_and,
        false_and,and_false,if_false,nd,add_zero]
      simp only [positive, and_true]
    by_cases negative : -(f a)=m
    · have q : m/f a= -1 := by rw [←negative, Int.neg_ediv_of_dvd (dvd_refl _), Int.ediv_self fn]
      have d : f a∣m := negative ▸ (dvd_neg.mpr (dvd_refl (f a)))
      simp only [q,om,Int.natAbs_neg,Int.natAbs_one,map_one,not_lt_of_ge le_rfl,
        d,true_and,false_and,and_false,if_false,positive,negative,and_true,zero_add,add_zero]
    simp only [positive,negative,and_false,if_false,zero_add]
    by_cases d : f a∣m
    · have eq := Int.mul_ediv_cancel' d
      have q0 : m/f a≠0 := fun e => mnz (by simpa [e] using eq.symm)
      have q1 : m/f a≠1 := fun e => positive (by simpa [e] using eq)
      have q2 : m/f a≠ -1 := fun e => negative (by simpa [e] using eq)
      have big : 1<(m/f a).natAbs := by omega
      simp [d,big]
    · simp [d]
  have count (g : ℤ→ℤ) (ig : Function.Injective g) (P:Prop) [Decidable P] :
      (∑ a∈B, if P ∧ g a=m then (1:ℂ) else 0) =
        if P ∧ m∈B.image g then 1 else 0 := by
    by_cases p:P
    · simp only [p,true_and]
      rw [← sum_image (f:=fun z:ℤ => if z=m then (1:ℂ) else 0) (g:=g) ig.injOn]
      simp
    · simp [p]
  change (∑ a∈B, if f a∣m ∧ ok (m/f a) then w (m/f a).natAbs else 0) = _
  rw [sum_congr rfl term,sum_add_distrib,sum_add_distrib]
  exact congrArg₂ (·+·) (congrArg₂ (·+·) (count f inj (s=r))
    (count (fun a=> -(f a)) inj' (s= -r))) rfl

end GreenDistribution
end

section
open Finset
open scoped Classical
namespace GreenDistribution

set_option maxHeartbeats 900000 in
/-- Bedert's single-layer decomposition after projection, for arbitrary disjoint
source bins and the actual signed arithmetic multiplier filter. Both leading
packets are indicators; the remainder has a uniform finite Fourier energy bound. -/
theorem single_layer (A W : Finset ℤ) (M Q H K : ℕ) [NeZero M]
    (k : ℤ) (hk : k≠0) (nz : ∀a∈A, a≠0)
    (r : (ZMod M)ˣ) (cell : (ZMod M)ˣ → ℤ → Prop)
    (uniq : ∀a∈A, ∀s t, cell s a → cell t a → s=t)
    (bins : ∀s, (A.filter (cell s)).card ≤ K)
    (hQ : 0<Q) (pos : 0<H) (hW : ∀m∈W,m≠0 ∧ m.natAbs≤H)
    (few : 2*Real.log (H:ℝ)≤Q*Real.log 2)
    (w : ℕ →* ℂ) (weight : ∀ d, ‖w d‖≤(d:ℝ)⁻¹)
    (cut : ℤ → ℂ) (contr : ∀m∈W, ‖cut m‖≤1) :
    let rough := fun h:ℤ => ∀p:ℕ, p.Prime → p≤Q → ¬(p:ℤ)∣h
    let source := fun s => A.filter (cell s)
    let positive := (source r).image (fun a=>k*a)
    let negative := (source (-r)).image (fun a=> -(k*a))
    ∃ tail : ℤ→ℂ, (∀m∈W,
      (∑s : (ZMod M)ˣ, ∑a∈source s, let h := m/(k*a)
        if k*a∣m ∧ (h:ZMod M)*(s:ZMod M)=r ∧ rough h then w h.natAbs else 0) =
      (if m∈positive then 1 else 0)+(if m∈negative then 1 else 0)+tail m) ∧
      (∑m∈W, ‖cut m*tail m‖^2) ≤
        (4*Real.log H/(Real.log 2*Q))*(2*K*(1+Real.log H)) := by
  classical
  intro rough source positive negative
  let ok (s : (ZMod M)ˣ) (h:ℤ) := (h:ZMod M)*(s:ZMod M)=r ∧ rough h
  let eligible (a h:ℤ) := ∃s, cell s a ∧ ok s h
  let (a h : ℤ) : Decidable (eligible a h) := Classical.propDecidable _
  let tail (m:ℤ) := ∑a∈A, let h := m/(k*a)
    if k*a∣m ∧ 1<h.natAbs ∧ eligible a h then w h.natAbs else 0
  refine ⟨tail,?_,?_⟩
  · intro m hm
    let B (s : (ZMod M)ˣ) := (source s).image (fun a=>k*a)
    let C (s : (ZMod M)ˣ) := (source s).image (fun a=> -(k*a))
    let rest (s : (ZMod M)ˣ) (a:ℤ) := let h := m/(k*a)
      if k*a∣m ∧ 1<h.natAbs ∧ ok s h then w h.natAbs else 0
    have collapsed : (∑s : (ZMod M)ˣ,∑a∈source s, rest s a)=tail m := by
      simp only [source,sum_filter]
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      let h := m/(k*a)
      change (∑s : (ZMod M)ˣ, if cell s a then rest s a else 0) =
        if k*a∣m ∧ 1<h.natAbs ∧ eligible a h then w h.natAbs else 0
      by_cases ex : ∃s,cell s a
      · obtain ⟨s,hs⟩ := ex
        have e : eligible a h ↔ ok s h := ⟨fun ⟨t,ht,ho⟩ => uniq a ha t s ht hs ▸ ho,
          fun ho=>⟨s,hs,ho⟩⟩
        rw [Fintype.sum_eq_single s,if_pos hs]
        · simp only [e]; rfl
        intro t ne
        exact if_neg (fun ht => ne (uniq a ha t s ht hs))
      · have no : ¬eligible a h := fun ⟨s,hs,_⟩=>ex ⟨s,hs⟩
        simp [no, show ∀s,¬cell s a from fun s hs=>ex ⟨s,hs⟩]
    have split (s : (ZMod M)ˣ) := split_bin A (cell s) k m hk nz (hW m hm).1 M Q s r w
    change (∑s : (ZMod M)ˣ, ∑a∈source s,
      if k*a∣m ∧ ok s (m/(k*a)) then w (m/(k*a)).natAbs else 0) = _
    calc _ = ∑s : (ZMod M)ˣ,
              ((if s=r ∧ m∈B s then 1 else 0)+(if s= -r ∧ m∈C s then 1 else 0)+
              ∑a∈source s, rest s a) := sum_congr rfl (fun s _ => split s)
         _ = _ := by
           rw [sum_add_distrib,sum_add_distrib,collapsed]
           simp only [ite_and, Fintype.sum_ite_eq',B,C,positive,negative]
  · have rows (h:ℤ) : (A.filter (fun a=>eligible a h)).card≤K := by
      by_cases ex : ∃s,ok s h
      · obtain ⟨s,eq,hr⟩ := ex
        have unit : IsUnit (h:ZMod M) := isUnit_of_mul_isUnit_left (show IsUnit ((h:ZMod M)*(s:ZMod M)) by rw [eq]; exact r.isUnit)
        apply (card_le_card _).trans (bins s)
        intro a ha
        obtain ⟨ha,t,ht,c,_⟩ := mem_filter.mp ha
        have same : t=s := Units.ext (unit.mul_left_cancel (c.trans eq.symm))
        exact mem_filter.mpr ⟨ha,same ▸ ht⟩
      · have no (a:ℤ) : ¬eligible a h := fun ⟨s,_,h⟩=>ex ⟨s,h⟩
        simp only [no,filter_false,card_empty,Nat.zero_le]
    have rg : ∀a∈A, ∀h, eligible a h → rough h := fun a _ h ⟨_,_,_,hr⟩=>hr
    apply (rough_tail_energy A W k hk H Q K hQ pos hW few eligible rg (fun h _ _=>rows h) w weight cut contr).trans_eq
    rfl

end GreenDistribution
end

section
open Finset GreenLow
open scoped Classical
namespace GreenDistribution

noncomputable def powers {L:ℕ} (u : Levels L) : ℕ :=
  ∏ p : ↥(Nat.primesLE L), (p:ℕ)^u p
abbrev selected {L:ℕ} (u : Levels L) (s : Residue L) (x:ℤ) : Prop :=
  x ≡ (powers u:ℤ)*((s:ZMod (primorial L)).val:ℤ) [ZMOD (powers u:ℤ)*(primorial L)]
noncomputable def level (L:ℕ) (a:ℤ) : Levels L := fun p=>a.natAbs.factorization p
noncomputable def plusPacket {L:ℕ} (A:Finset ℤ) (v u : Levels L) (r:Residue L) :=
  (cell A u r).image (fun a=>(powers (v-u):ℤ)*a)
noncomputable def minusPacket {L:ℕ} (A:Finset ℤ) (v u : Levels L) (r:Residue L) :=
  (cell A u (-r)).image (fun a=> -((powers (v-u):ℤ)*a))

theorem powers_nz {L:ℕ} (v : Levels L) : powers v ≠0 := Finset.prod_ne_zero_iff.mpr
  (fun i _ => pow_ne_zero _ (Nat.prime_of_mem_primesLE i.property).ne_zero)

theorem modulus_eq {L:ℕ} (v : Levels L) : modulus v = powers v*(primorial L) := by
  have mm : (∏p:↥(Nat.primesLE L),(p:ℕ))=primorial L := by
    rw [prod_coe_sort (Nat.primesLE L) (fun z=>z)]; rfl
  simp only [modulus,powers,pow_succ,prod_mul_distrib,mm]

theorem cell_eq {L:ℕ} (A:Finset ℤ) (v:Levels L) (r:Residue L) :
    cell A v r = A.filter (selected v r) := by
  ext a; simp only [cell,selected,residue,modulus_eq,Nat.cast_mul,mem_filter,powers]

theorem window_spec (T:ℕ) {L:ℕ} (v : Levels L) (r : Residue L) :
    ∀m∈cell (window T) v r,m≠0 ∧ m.natAbs≤2*T ∧ selected v r m := by
  rw [cell_eq]
  intro m h
  obtain ⟨hm,hs⟩ := mem_filter.mp h
  obtain ⟨nz,mh⟩ := mem_erase.mp hm
  obtain ⟨lo,hi⟩ := mem_Ioo.mp mh
  exact ⟨nz,by omega,hs⟩

theorem plateau_head {L:ℕ} (v : Levels L) (r : Residue L) (A : Finset ℤ)
    (nz : ∀a∈A,a≠0) (sign : ∀a∈A,-a∉A) (T:ℕ) (size : ∀a∈A,a.natAbs≤T)
    (cut : ℤ→ℂ) (flat : ∀ m:ℤ,m.natAbs≤T → cut m=1) :
    ∀ m, selected v r m →
      cut m*((if m∈plusPacket A v v r then 1 else 0)+(if m∈minusPacket A v v r then 1 else 0))=
      if m∈mirror A then 1 else 0 := by
  let : NeZero (primorial L) := ⟨primorial_ne_zero L⟩
  have packets := GreenLayers.top_packets (primorial L) (powers v) T r A nz sign size cut flat
  have zero : powers (v-v)=1 := by simp [powers]
  intro m hm
  have e := packets.2.2.2.2.2.2.2.1 m hm
  simp only [plusPacket,minusPacket,zero,Nat.cast_one,one_mul,image_id',cell_eq,mirror,
    selected,mem_image,mem_filter,Finset.mem_union] at e ⊢
  split_ifs at e ⊢ <;> simp_all only

end GreenDistribution
end

section
open Finset GreenLow
open scoped Classical
namespace GreenDistribution

noncomputable def rawLayer {L:ℕ} (Q:ℕ) (A:Finset ℤ) (u v:Levels L) (r:Residue L) (m:ℤ) : ℂ :=
  let : NeZero (primorial L) := ⟨primorial_ne_zero L⟩
  let k : ℤ := powers (v-u)
  ∑s : Residue L, ∑a∈cell A u s,
    let h := m/(k*a)
    if k*a∣m ∧ (h:ZMod (primorial L))*(s:ZMod (primorial L))=r ∧ fullEligible Q h
    then GreenBourgain.weight h.natAbs else 0

theorem actual_layer {L Q H K:ℕ} (A W : Finset ℤ) (u v : Levels L) (r : Residue L)
    (nz : ∀a∈A,a≠0) (bins : ∀s,(cell A u s).card≤K)
    (hQ : 0<Q) (pos : 0<H) (hW : ∀m∈W,m≠0 ∧ m.natAbs≤H)
    (few : 2*Real.log (H:ℝ)≤Q*Real.log 2)
    (cut : ℤ→ℂ) (amp : ∀m∈W, ‖cut m‖≤1) :
    ∃ tail : ℤ→ℂ, (∀m∈W,rawLayer Q A u v r m =
      (if m∈plusPacket A v u r then 1 else 0) +
      (if m∈minusPacket A v u r then 1 else 0)+tail m) ∧
    (∑m∈W, ‖cut m*tail m‖^2) ≤
      (4*Real.log H/(Real.log 2*Q))*(2*K*(1+Real.log H)) := by
  classical
  let : NeZero (primorial L) := ⟨primorial_ne_zero L⟩
  let k : ℤ := powers (v-u)
  have hk : k≠0 := Nat.cast_ne_zero.mpr (powers_nz _)
  let pred : Residue L→ℤ→Prop := selected u
  let src (s:Residue L) := @Finset.filter _ (pred s) (fun x=>Classical.propDecidable _) A
  have sets (s:Residue L) : src s=cell A u s := by
    rw [cell_eq]; ext; simp only [src,mem_filter,pred]
  have unique : ∀a∈A, ∀s t, pred s a → pred t a → s=t :=
    fun a _ s t h j => cell_unique (powers u) (primorial L) (powers_nz u) a s t h j
  have groupmax (s:Residue L) : (src s).card≤K := (sets s) ▸ bins s
  have w := fun d => (show ‖GreenBourgain.weight d‖≤(d:ℝ)⁻¹ by
    simpa only [one_div] using GreenBourgain.weight_bound d)
  obtain ⟨tail,split,energy⟩ := single_layer A W (primorial L) Q H K k hk nz r pred unique groupmax
    hQ pos hW few GreenBourgain.weight w cut amp
  refine ⟨tail,?_,energy⟩
  intro m hm
  have e := split m hm
  change (∑s : Residue L, ∑a∈src s, if k*a∣m ∧ ((m/(k*a):ℤ):ZMod (primorial L))*(s:ZMod (primorial L))=r ∧
      (∀p:ℕ,p.Prime → p≤Q → ¬(p:ℤ)∣m/(k*a)) then GreenBourgain.weight (m/(k*a)).natAbs else 0)
      = (if m∈(src r).image (fun a=>k*a) then 1 else 0)+
      (if m∈(src (-r)).image (fun a=> -(k*a)) then 1 else 0)+tail m at e
  simp_rw [sets] at e
  exact e

end GreenDistribution
end

section
open Finset GreenLow
open scoped Classical
namespace GreenDistribution

noncomputable def predecessors {L:ℕ} (A:Finset ℤ) (v : Levels L) :=
  (A.image (level L)).filter (fun u=>u≤v)

theorem medium_raw {L Q:ℕ} (A:Finset ℤ) (v:Levels L) (r:Residue L)
    (nz:∀a∈A,a≠0) (m:ℤ) (mnz:m≠0) (target:selected v r m) :
    coeff A (medEligible L Q) m = ∑u∈predecessors A v,
      GreenBourgain.weight (powers (v-u))*rawLayer Q A u v r m := by
  classical
  let : NeZero (primorial L) := ⟨primorial_ne_zero L⟩
  have e := BedertSelection.medium_spectrum GreenBourgain.weight L Q v r A nz m mnz target
  unfold rawLayer
  simp_rw [cell_eq]
  exact e

/-- For the medium sieve every proper predecessor is small when the descent
alternative fails. Their leading packets and the rough tails fit the aggregate
energy bound; only the distinguished packet remains. -/
theorem medium_actual {L Q T K : ℕ} (A : Finset ℤ) (v : Levels L) (r:Residue L)
    (nz : ∀a∈A,a≠0) (sign : ∀a∈A,-a∉A) (size : ∀a∈A,a.natAbs≤T)
    (hQ : 0<Q) (pos : 0<2*T) (few : 2*Real.log ((2*T:ℕ):ℝ)≤Q*Real.log 2)
    (large : (cell A v r).Nonempty)
    (bins : ∀u≤v, ∀s,(cell A u s).card≤K)
    (d:ℝ) (hd : 0≤d)
    (numeric : (4*Real.log ((2*T:ℕ):ℝ)/(Real.log 2*Q))*(2*K*(1+Real.log ((2*T:ℕ):ℝ)))≤d^2)
    (small : ∀u<v,∀s,((cell A u s).card:ℝ)≤d^2)
    (cut:ℤ→ℂ) (amp:∀m,‖cut m‖≤1) (flat:∀m:ℤ,m.natAbs≤T → cut m=1) :
    errorEnergy A (window T) v r cut (medEligible L Q) ≤ (3*(max 1 L:ℕ)*d)^2 := by
  classical
  let W := cell (window T) v r
  let U := predecessors A v
  have pre (u) (hu:u∈U) : u≤v := (mem_filter.mp hu).2
  have top : v∈U := by
    obtain ⟨a,ha⟩ := large
    rw [cell_eq] at ha
    obtain ⟨mem,tgt⟩ := mem_filter.mp ha
    have eq : level L a=v := funext (BedertSelection.valuations_of_cell L v r a (nz a mem) tgt)
    exact mem_filter.mpr ⟨mem_image.mpr ⟨a,mem,eq⟩,le_rfl⟩
  have Wspec := window_spec T v r
  have hW (m:ℤ) (hm:m∈W) : m≠0 ∧ m.natAbs≤2*T := ⟨(Wspec m hm).1,(Wspec m hm).2.1⟩
  have all (u : ↥U) := actual_layer A W (u:Levels L) v r nz (bins _ (pre _ u.property))
    hQ pos hW few cut (fun m _=> amp m)
  choose t identity bound using all
  let tail (u:Levels L) : ℤ→ℂ := if hu:u∈U then t ⟨u,hu⟩ else 0
  let w (u:Levels L) := GreenBourgain.weight (powers (v-u))
  have coef (u) (_:u∈U) : ‖w u‖ ≤ ((powers (v-u):ℕ):ℝ)⁻¹ := by
    simpa only [w,one_div] using GreenBourgain.weight_bound (powers (v-u))
  have unit : w v=1 := by simp [w,powers]
  have tails (u) (hu:u∈U) : ∑m∈W, ‖cut m*tail u m‖^2≤d^2 := by
    simpa only [tail,dif_pos hu] using (bound ⟨u,hu⟩).trans numeric
  have sizes (u) (hu:u∈U) (ne:u≠v) :
      ((plusPacket A v u r).card:ℝ)≤d^2 ∧ ((minusPacket A v u r).card:ℝ)≤d^2 := by
    have lt := lt_of_le_of_ne (pre u hu) ne
    exact ⟨(Nat.cast_le.mpr card_image_le).trans (small u lt r),
      (Nat.cast_le.mpr card_image_le).trans (small u lt (-r))⟩
  let raw := coeff A (medEligible L Q)
  let head := fun m : ℤ => if m∈mirror A then (1:ℂ) else 0
  apply GreenLayers.layer_discrepancy L v U pre top W cut (fun m _=>amp m) tail
    (fun u=>plusPacket A v u r) (fun u=>minusPacket A v u r) w d hd coef unit tails sizes raw head
  · intro m hm
    rw [show raw m=_ from medium_raw A v r nz m (hW m hm).1 (Wspec m hm).2.2]
    apply sum_congr rfl
    intro u hu
    rw [show rawLayer Q A u v r m=_ from identity ⟨u,hu⟩ m hm]
    have hu₁ : u∈U := hu
    simp only [tail,dif_pos hu₁,w]
  · intro m hm
    exact plateau_head v r A nz sign T size cut flat m (Wspec m hm).2.2

end GreenDistribution
end

section
open Finset GreenLow
open scoped Classical
namespace GreenDistribution

/-- The full sieve has no lower-level contamination: all rough multipliers
preserve the valuation vector, and its ±1 multipliers are the Boolean head. -/
theorem full_actual {L Q T : ℕ} (lq : L≤Q) (qp : 0<Q) (tp : 0<2*T)
    (few : 2*Real.log (2*T:ℕ) ≤ Q*Real.log 2)
    (A : Finset ℤ) (nz : ∀a∈A,a≠0) (sign : ∀a∈A,-a∉A) (size : ∀a∈A,a.natAbs≤T)
    (v : Levels L) (r : Residue L) (maxim : ∀ s, (cell A v s).card ≤ (cell A v r).card)
    (cut : ℤ → ℂ) (amp : ∀ m, ‖cut m‖≤1) (flat : ∀m:ℤ,m.natAbs≤T → cut m=1) :
    errorEnergy A (window T) v r cut (fullEligible Q) ≤
      (4*Real.log (2*T:ℕ)/(Real.log 2*Q))*(2*((cell A v r).card:ℝ)*(1+Real.log (2*T:ℕ))) := by
  classical
  let M := primorial L
  let : NeZero M := ⟨primorial_ne_zero L⟩
  let W := cell (window T) v r
  have spec := window_spec T v r
  obtain ⟨tail,parts,energy⟩ := actual_layer (H:=2*T) A W v v r nz maxim qp tp
    (fun m hm => ⟨(spec m hm).1,(spec m hm).2.1⟩) few cut (fun m _ => amp m)
  have pp : powers (v-v)=1 := by simp [powers]
  have eq (m:ℤ) (hm:m∈W) : coeff A (fullEligible Q) m =
      (if m∈plusPacket A v v r then 1 else 0)+(if m∈minusPacket A v v r then 1 else 0)+tail m := by
    have h := BedertSelection.full_spectrum GreenBourgain.weight L Q lq v r A nz m (spec m hm).1 (spec m hm).2.2
    apply h.trans
    rw [←parts m hm]
    simp only [rawLayer,pp,Nat.cast_one,one_mul,fullEligible]
    apply sum_congr rfl; intro s hs
    rw [cell_eq]; rfl
  have top := plateau_head v r A nz sign T size cut flat
  change (∑ m∈W, ‖cut m*coeff A (fullEligible Q) m - (if m∈mirror A then 1 else 0)‖^2) ≤ _
  apply le_trans (le_of_eq (sum_congr rfl (fun m hm => ?_))) energy
  rw [eq m hm,mul_add,top m (spec m hm).2.2,add_sub_cancel_left]

/-- The full-sieve half of the two projected coefficient bounds, uniformly over
all maximizing cells, independently of the size of their valuation vectors. -/
theorem eventually_full : ∀ᶠ n : ℕ in Filter.atTop, ∀ A : Finset ℤ, 0∉A → (∀a∈A,-a∉A) →
    (∀a∈A, |a| ≤ (radius n:ℤ)) → ∀ v : Levels (smallPrimes n), ∀ r : Residue (smallPrimes n),
    (∀ s, (cell A v s).card ≤ (cell A v r).card) → ∀ cut : ℤ → ℂ,
    (∀ m, ‖cut m‖≤1) → (∀ m:ℤ,m.natAbs≤radius n → cut m=1) →
    errorEnergy A (window (radius n)) v r cut (fullEligible (bigPrimes n)) ≤ ((cell A v r).card:ℝ)/100 := by
  filter_upwards [GreenLayers.eventually_noise_energy 0] with n scales A nz sign size v r maxim cut amp flat
  obtain ⟨tp,qp,lq,few,es⟩ := scales
  obtain ⟨bound,small,_⟩ := es ((cell A v r).card:ℝ) (Nat.cast_nonneg _)
  have ns : ∀ a∈A,a≠0 := fun a ha h => nz (h ▸ ha)
  have radiusOK : ∀ a∈A, a.natAbs≤radius n := by
    intro a ha
    have h := size a ha
    rw [←Int.natCast_natAbs] at h
    exact_mod_cast h
  exact (full_actual lq qp tp few A ns sign radiusOK v r maxim cut amp flat).trans (bound.trans small)

end GreenDistribution
end

section
open Finset GreenLow Filter
open scoped Classical
namespace GreenDistribution

/-- The quantitative spectral alternative in Bedert §§7–8, for the
actual medium-prime and all-prime sieves of an integer model. -/
theorem projected_bounds : GreenLow.ProjectedBounds := by
  intro j
  have logT : Tendsto (fun n:ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_full,GreenLayers.eventually_noise_energy j,logT.eventually_ge_atTop 1]
    with n full scales logn A nz _ sign size
  intro L Q T v r maximum cut amp flat
  refine ⟨full A nz sign size v r maximum cut amp flat,?_⟩
  intro large predecessorsSmall
  let K := (cell A v r).card
  let z := Real.log n
  let d := Real.sqrt (K:ℝ)/z^2
  obtain ⟨hp,qp,_,few,es⟩ := scales
  obtain ⟨per,_,combined⟩ := es (K:ℝ) (Nat.cast_nonneg _)
  have zpos : 0<z := zero_lt_one.trans_le logn
  have zfour : 1≤z^4 := one_le_pow₀ logn
  have eq : d^2=(K:ℝ)/z^4 := by
    dsimp [d]; rw [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  have npos : 0<(cell A v r).card := by
    have one : (1:ℝ) ≤ (K:ℝ) := zfour.trans large
    exact_mod_cast (show (0:ℝ)<(K:ℝ) by linarith)
  have small (u:Levels L) (hu:u<v) (s:Residue L) : ((cell A u s).card:ℝ)≤d^2 := by
    rw [eq,le_div_iff₀ (pow_pos zpos 4),mul_comm]
    exact (predecessorsSmall u hu s).le
  have bin (u:Levels L) (hu:u≤v) (s:Residue L) : (cell A u s).card≤K := by
    rcases eq_or_lt_of_le hu with h|lt
    · subst u; exact maximum s
    · have step : ((cell A u s).card:ℝ)≤ z^4*((cell A u s).card:ℝ) := by
        simpa using (mul_le_mul_of_nonneg_right zfour (Nat.cast_nonneg (cell A u s).card))
      exact_mod_cast step.trans (predecessorsSmall u lt s).le
  have ns : ∀a∈A,a≠0 := fun a ha h => nz (h ▸ ha)
  have bounded : ∀a∈A,a.natAbs≤T := by
    intro a ha
    have h := size a ha
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  exact (medium_actual (K:=K) A v r ns sign bounded qp hp few (card_pos.mp npos) bin d
    (div_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) per small cut amp flat).trans combined

end GreenDistribution
end

/-- The bounded low-dimensional case of Bedert's theorem. -/
theorem GreenLow.low_child : OMA.R_Green1_green_1_R1.H2 :=
  GreenLow.low_of_projected_bounds GreenDistribution.projected_bounds
end

theorem OMA.solution : type_of% @Green1.green_1 := by
  exact OMA.R_Green1_green_1_R1.main GreenHigh.high_child GreenLow.low_child
