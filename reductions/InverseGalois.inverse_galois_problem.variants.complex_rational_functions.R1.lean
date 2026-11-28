import FormalConjectures.Wikipedia.InverseGalois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.Index
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.RegularWreathProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.PowerBasis
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.NormNum

/-!
# Finite monodromy over the complex rational function field

A connected covering built from two slit charts gives the fundamental group of
the plane with n punctures a free quotient of rank n. Its finite quotients
supply the topological monodromy for arbitrary finite groups. The outstanding
comparison at the generic point is required only for groups outside two
families realized here by explicit algebraic constructions.

* For abelian groups, adjoin independent radicals at distinct branch points.
  Expansion in formal power series proves that each radical has the required
  degree after the earlier ones have been adjoined.
* A faithful finite projective action gives a rational fixed field by Lüroth's
  theorem. Concrete matrices cover the dihedral groups, the octahedral group
  and the icosahedral group.
* A second route uses two generators and a marked cyclic quotient. A root
  of the rational parameter identifies the quotient curve's function field.
  The wreath-product construction recovers an arbitrary finite group.
* The analytic function field of the base sphere is rational. Meromorphy on
  the affine chart and at infinity characterizes functions that agree away
  from finitely many points with a unique rational function.

The final two steps state the topological and algebraic inputs separately.
The file includes a proof of the topological step.
-/

section

open InverseGalois

namespace ProjectiveGalois
universe u v

/-- Transport a concrete Galois realization along an isomorphism of base fields. -/
theorem realize_over_iso {K F L : Type u} [Field K] [Field F] [Field L] [Algebra F L]
    [IsGalois F L] {G : Type v} [Group G] (e : K ≃+* F) (aut : G ≃* (L ≃ₐ[F] L)) :
    IsRealizable K G := by
  let : Algebra K L := ((algebraMap F L).comp e.toRingHom).toAlgebra
  have base (x : K) : algebraMap K L x = algebraMap F L (e x) := rfl
  let up (σ : L ≃ₐ[F] L) : L ≃ₐ[K] L :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun x => σ.commutes (e x))
  let down (σ : L ≃ₐ[K] L) : L ≃ₐ[F] L :=
    AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun y => by
      change σ (algebraMap F L y)=algebraMap F L y
      simpa only [base, e.apply_symm_apply] using σ.commutes (e.symm y))
  let same : (L ≃ₐ[F] L) ≃* (L ≃ₐ[K] L) :=
    { toFun := up, invFun := down, left_inv := fun _ => rfl, right_inv := fun _ => rfl,
      map_mul' := fun _ _ => rfl }
  have galois : IsGalois K L := IsGalois.of_equiv_equiv (F:=F) (E:=L)
    (f := e.symm) (g := RingEquiv.refl L) (by ext y; simp [base])
  exact ⟨⟨⟨L,inferInstance,inferInstance,galois,aut.trans same⟩⟩⟩

/-- A faithful finite action realizes G over L when K ⊆ L is transcendental
and each nonconstant intermediate field is isomorphic to L. -/
theorem realize_action_luroth {K L : Type u} [Field K] [Field L] [Algebra K L]
    (transcendental : ¬ IsGalois K L)
    (rational : ∀ E : IntermediateField K L, E ≠ ⊥ → Nonempty (L ≃+* E))
    {G : Type v} [Group G] [Finite G] (action : G →* (L ≃ₐ[K] L))
    (faithful : Function.Injective action) : IsRealizable L G := by
  let : MulSemiringAction G L := MulSemiringAction.compHom L action
  let : FaithfulSMul G L := ⟨fun {_ _} h => faithful (AlgEquiv.ext h)⟩
  let : SMulCommClass G K L :=
    ⟨fun g c x => (action g).toLinearEquiv.map_smul c x⟩
  let E : IntermediateField K L := FixedPoints.intermediateField G
  have gf : IsGalois E L :=
    inferInstanceAs (IsGalois (FixedPoints.subfield G L) L)
  have ne : E ≠ ⊥ := by
    intro eq
    rw [eq] at gf
    exact transcendental ((isGalois_iff_isGalois_bot (F:=K) (E:=L)).mp gf)
  obtain ⟨e⟩ := rational E ne
  let := gf
  exact @realize_over_iso L E L _ _ _ _ gf G _ e
    (FixedPoints.toAlgAutMulEquiv G L : G ≃* (L ≃ₐ[E] L))

end ProjectiveGalois

open InverseGalois
namespace ProjectiveGalois
universe u v

/-- Artin's fixed-field theorem and Lüroth's theorem realize every finite group
admitting a faithful action on the projective line over a field K. -/
theorem realize_of_faithful_action {K : Type u} [Field K] {G : Type v} [Group G] [Finite G]
    (action : G →* (RatFunc K ≃ₐ[K] RatFunc K)) (faithful : Function.Injective action) :
    IsRealizable (RatFunc K) G := by
  refine realize_action_luroth (K:=K) (L:=RatFunc K) ?_ ?_ action faithful
  · intro h
    let : IsGalois K (RatFunc K) := h
    exact RatFunc.transcendental_X (IsGalois.integral K _).isAlgebraic
  · intro E nontrivial
    exact ⟨(RatFunc.Luroth.algEquiv nontrivial).toRingEquiv⟩

end ProjectiveGalois

namespace GaloisActions
open IntermediateField

theorem substitutions_of_generator {K F : Type*} [Field K] [Field F] [Algebra K F]
    (X : F) (X0 : X≠0) (htop : adjoin K {X} = ⊤) (degree : F → ℤ)
    (degR : ∀ a : K, a≠0 → degree (algebraMap K F a*X)=1)
    (degS : ∀ a : K, a≠0 → degree (algebraMap K F a/X) = -1)
    (transport : ∀ w : F, X ∈ adjoin K {w} →
      ∃ f : F ≃ₐ[K] adjoin K {w}, (f X : F)=w) :
    X≠0 ∧ (∀ f g : F ≃ₐ[K] F, f X=g X → f=g) ∧
      (∀ a b : K, a≠0 → b≠0 → algebraMap K F a * X ≠ algebraMap K F b / X) ∧
      ∀ a : K, a≠0 →
        (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a * X) ∧
        (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a / X) := by
  let C := algebraMap K F
  refine ⟨X0,?_,?_,?_⟩
  · intro f g agree
    apply AlgEquiv.ext
    intro z
    have hz : z ∈ adjoin K {X} := by rw [htop]; trivial
    exact adjoin_induction K (p:=fun w _ => f w=g w)
      (fun _ h => (Set.mem_singleton_iff.mp h) ▸ agree)
      (fun c => (f.commutes c).trans (g.commutes c).symm)
      (fun _ _ _ _ h k => by simp [h,k]) (fun _ _ h => by simp [h])
      (fun _ _ _ _ h k => by simp [h,k]) hz
  · intro a b ha hb eq
    have dd := congrArg degree eq
    change degree (C a*X)=degree (C b/X) at dd
    rw [degR a ha,degS b hb] at dd
    contradiction
  · intro a ha
    have ca : C a≠0 := (map_ne_zero _).mpr ha
    have mk (w : F) (gen : X ∈ adjoin K {w}) :
        ∃ f : F ≃ₐ[K] F, f X = w := by
      have top : adjoin K {w} = ⊤ := eq_top_iff.mpr (htop ▸ adjoin_simple_le_iff.mpr gen)
      obtain ⟨f,hf⟩ := transport w gen
      let iso := f.trans ((equivOfEq top).trans topEquiv)
      exact ⟨iso,hf⟩
    constructor
    · apply mk (C a*X)
      have hx := (adjoin K {C a*X}).div_mem (mem_adjoin_simple_self K (C a*X)) ((adjoin K {C a*X}).algebraMap_mem a)
      change (C a*X)/C a ∈ _ at hx
      rwa [mul_div_cancel_left₀ X ca] at hx
    · apply mk (C a/X)
      have hx := (adjoin K {C a/X}).div_mem ((adjoin K {C a/X}).algebraMap_mem a) (mem_adjoin_simple_self K (C a/X))
      change C a/(C a/X) ∈ _ at hx
      simpa only [div_div_eq_mul_div, mul_div_cancel_left₀ X ca] using hx

end GaloisActions

namespace GaloisActions

/-- Automorphisms scaling a generator and sending it to a scalar multiple of its
inverse give a faithful dihedral action. -/
theorem dihedral_of_substitutions {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (X : F) (X0 : X≠0)
    (determined : ∀ f g : F ≃ₐ[K] F, f X=g X → f=g)
    (different : ∀ a b : K, a≠0 → b≠0 → algebraMap K F a * X ≠ algebraMap K F b / X)
    (substitutions : ∀ a : K, a≠0 →
      (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a * X) ∧
      (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a / X))
    (χ : ZMod n → K) (inj : Function.Injective χ) (val0 : χ 0=1)
    (add : ∀ i j, χ (i+j)=χ i*χ j) (sub : ∀ i j, χ (i-j)=χ i/χ j)
    (nz : ∀ i, χ i≠0) : ∃ φ : DihedralGroup n →* (F ≃ₐ[K] F), Function.Injective φ := by
  classical
  choose R hR using fun i => (substitutions (χ i) (nz i)).1
  choose J hJ using fun i => (substitutions (χ i) (nz i)).2
  let act : DihedralGroup n → (F ≃ₐ[K] F) := fun g => match g with
    | .r i => R i
    | .sr i => J i
  have HR (i : ZMod n) : act (.r i) X = algebraMap K F (χ i) * X := hR i
  have HJ (i : ZMod n) : act (.sr i) X = algebraMap K F (χ i) / X := hJ i
  have constant (f : F ≃ₐ[K] F) (c : K) : f (algebraMap K F c)=algebraMap K F c := f.commutes c
  have c0 (i : ZMod n) : algebraMap K F (χ i)≠0 := (map_ne_zero _).mpr (nz i)
  let φ : DihedralGroup n →* (F ≃ₐ[K] F) := {
    toFun := act
    map_one' := determined _ _ (by change act (.r 0) X = X; rw [HR,val0,map_one,one_mul])
    map_mul' := by
      intro g h
      apply determined
      cases g with
      | r i =>
        cases h with
        | r j => simp only [DihedralGroup.r_mul_r,HR,AlgEquiv.mul_apply,map_mul,constant,add]; ring
        | sr j => simp only [DihedralGroup.r_mul_sr,HJ,HR,AlgEquiv.mul_apply,map_div₀,constant,sub]; field_simp [c0,X0]
      | sr i =>
        cases h with
        | r j => simp only [DihedralGroup.sr_mul_r,HJ,HR,AlgEquiv.mul_apply,map_mul,constant,add]; ring
        | sr j => simp only [DihedralGroup.sr_mul_sr,HR,HJ,AlgEquiv.mul_apply,map_div₀,constant,sub]; field_simp [c0,X0]
  }
  refine ⟨φ,?_⟩
  intro a b eq
  have ex : act a X = act b X := congrArg (fun f : F ≃ₐ[K] F => f X) eq
  have same {i j : ZMod n} (h : algebraMap K F (χ i)=algebraMap K F (χ j)) : i=j :=
    inj ((algebraMap K F).injective h)
  cases a with
  | r i =>
    cases b with
    | r j => rw [HR,HR] at ex; exact congrArg DihedralGroup.r (same (mul_right_cancel₀ X0 ex))
    | sr j => rw [HR,HJ] at ex; exact (different _ _ (nz i) (nz j) ex).elim
  | sr i =>
    cases b with
    | r j => rw [HJ,HR] at ex; exact (different _ _ (nz j) (nz i) ex.symm).elim
    | sr j => rw [HJ,HJ,div_eq_mul_inv,div_eq_mul_inv] at ex; exact congrArg DihedralGroup.sr (same (mul_right_cancel₀ (inv_ne_zero X0) ex))

end GaloisActions

namespace GaloisActions

/-- A primitive root supplies the faithful multiplicative character of Z/n
needed for the rotations of a regular n-gon. -/
theorem character_of_root {K : Type*} [Field K] {n : ℕ} {ζ : Kˣ} (root : IsPrimitiveRoot ζ n) :
    ∃ χ : ZMod n → K, Function.Injective χ ∧ χ 0=1 ∧
      (∀ i j, χ (i+j)=χ i*χ j) ∧ (∀ i j, χ (i-j)=χ i/χ j) ∧ ∀ i, χ i≠0 := by
  let e := root.zmodEquivZPowers
  let value : Additive (Subgroup.zpowers ζ) → K := fun z => ((z.toMul : Kˣ) : K)
  refine ⟨fun i => value (e i),?_,?_,?_,?_,?_⟩
  · intro i j eq
    exact e.injective (Subtype.ext (Units.ext eq))
  · exact congrArg value e.map_zero
  · intro i j
    exact congrArg value (e.map_add i j)
  · intro i j
    simp [value,sub_eq_add_neg,div_eq_mul_inv]
  · intro i
    exact (e i).toMul.val.ne_zero

theorem complex_character (n : ℕ) (nonzero : n≠0) :
    ∃ χ : ZMod n → ℂ, Function.Injective χ ∧ χ 0=1 ∧
      (∀ i j, χ (i+j)=χ i*χ j) ∧ (∀ i j, χ (i-j)=χ i/χ j) ∧ ∀ i, χ i≠0 :=
  character_of_root ((Complex.isPrimitiveRoot_exp n nonzero).isUnit_unit nonzero)

end GaloisActions

namespace GaloisActions
open IntermediateField

/-- Scaling and inversion of the indeterminate are rational-function field
automorphisms. A rotation and a reflection have different degrees at infinity. -/
theorem ratfunc_substitutions (K : Type*) [Field K] :
    let F := RatFunc K
    let X : F := RatFunc.X
    X≠0 ∧ (∀ f g : F ≃ₐ[K] F, f X=g X → f=g) ∧
      (∀ a b : K, a≠0 → b≠0 → algebraMap K F a * X ≠ algebraMap K F b / X) ∧
      ∀ a : K, a≠0 →
        (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a * X) ∧
        (∃ f : F ≃ₐ[K] F, f X=algebraMap K F a / X) := by
  dsimp only
  let F := RatFunc K
  let X : F := RatFunc.X
  let C := algebraMap K F
  have X0 : X≠0 := RatFunc.X_ne_zero
  have degC (a : K) : (C a).intDegree = 0 := RatFunc.intDegree_C a
  have degX : X.intDegree=1 := RatFunc.intDegree_X
  have degR (a : K) (ha : a≠0) : (C a*X).intDegree = 1 := by
    rw [RatFunc.intDegree_mul ((map_ne_zero _).mpr ha) X0,degC,degX,zero_add]
  have degS (a : K) (ha : a≠0) : (C a/X).intDegree = -1 := by
    rw [RatFunc.intDegree_div ((map_ne_zero _).mpr ha) X0,degC,degX,zero_sub]
  apply substitutions_of_generator X X0 RatFunc.adjoin_X RatFunc.intDegree degR degS
  intro w gen
  have tr : Transcendental K w := by
    intro hw
    let E := adjoin K {w}
    let : Algebra.IsAlgebraic K E := isAlgebraic_adjoin_simple hw.isIntegral
    have hx := Algebra.IsAlgebraic.isAlgebraic (R:=K) (⟨X,gen⟩ : E)
    exact RatFunc.transcendental_X (IntermediateField.isAlgebraic_iff.mp hx)
  exact ⟨RatFunc.algEquivOfTranscendental w tr, RatFunc.algEquivOfTranscendental_X w tr⟩

end GaloisActions

open InverseGalois

namespace GaloisActions

/-- Over a field containing a primitive n-th root of unity, the dihedral group
acts faithfully on the rational-function field by rotations and inversion. -/
theorem dihedral_action {K : Type*} [Field K] {n : ℕ} {ζ : Kˣ}
    (root : IsPrimitiveRoot ζ n) :
    ∃ φ : DihedralGroup n →* (RatFunc K ≃ₐ[K] RatFunc K), Function.Injective φ := by
  obtain ⟨X0,determined,different,substitutions⟩ := ratfunc_substitutions K
  obtain ⟨χ,inj,val0,add,sub,nz⟩ := character_of_root root
  exact dihedral_of_substitutions RatFunc.X X0 determined different substitutions χ inj val0 add sub nz

/-- This realization works over every rational-function field over a field
containing a primitive n-th root of unity. -/
theorem dihedral_of_root {K : Type*} [Field K] {n : ℕ} [NeZero n] {ζ : Kˣ}
    (root : IsPrimitiveRoot ζ n) : IsRealizable (RatFunc K) (DihedralGroup n) := by
  obtain ⟨φ,inj⟩ := dihedral_action root
  exact ProjectiveGalois.realize_of_faithful_action φ inj

/-- Every finite dihedral group is a Galois group over the rational function
field over the complex numbers. -/
theorem complex_dihedral (n : ℕ) [NeZero n] :
    IsRealizable (RatFunc ℂ) (DihedralGroup n) :=
  dihedral_of_root ((Complex.isPrimitiveRoot_exp n NeZero.out).isUnit_unit NeZero.out)

end GaloisActions

end

section

namespace InverseKummer
open Polynomial

/-- The binomial associated to a prime element is Eisenstein at that element. -/
theorem eisenstein_binomial {R : Type*} [CommRing R] [IsDomain R]
    {u : R} (prime : Prime u) {n : ℕ} (pos : 0 < n) :
    (X^n - C u).IsEisensteinAt (Ideal.span {u}) := by
  have monic := monic_X_pow_sub_C u pos.ne'
  have nottop := ((Ideal.span_singleton_prime prime.ne_zero).2 prime).ne_top
  apply monic.isEisensteinAt_of_mem_of_notMem nottop
  · intro k hk
    rw [natDegree_X_pow_sub_C] at hk
    rw [coeff_sub, coeff_X_pow, if_neg hk.ne, zero_sub, Ideal.neg_mem_iff]
    by_cases h : k = 0
    · subst k
      simp
    · simp [coeff_C, h]
  · rw [coeff_sub, coeff_X_pow, if_neg pos.ne, coeff_C_zero, zero_sub, Ideal.neg_mem_iff,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton, sq]
    intro bad
    have h : u ∣ 1 := (mul_dvd_mul_iff_left prime.ne_zero).mp (by simpa only [mul_one] using bad)
    exact prime.not_isUnit (isUnit_of_dvd_one h)

/-- A uniform irreducibility certificate over the rational function field.
The element t−a is given by its image under the fraction-field embedding. -/
theorem irreducible_shifted_binomial {K : Type*} [Field K] {n : ℕ} (pos : 0 < n) (a : K) :
    Irreducible (X^n - C (algebraMap (Polynomial K) (RatFunc K) (X-C a))) := by
  let u : Polynomial K := X - C a
  have prime : Prime u := prime_X_sub_C a
  have monic := monic_X_pow_sub_C u pos.ne'
  have irr := (eisenstein_binomial prime pos).irreducible
    ((Ideal.span_singleton_prime prime.ne_zero).2 prime) monic.isPrimitive
    (by simpa only [natDegree_X_pow_sub_C] using pos)
  simpa [u] using (monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K := RatFunc K)).mp irr

end InverseKummer

namespace InverseKummer
open Polynomial

/-- To prove a binomial irreducible over a splitting field, one may embed
the base in any field splitting the old polynomial but retaining irreducibility. -/
theorem irreducible_after_split {K F : Type*} [Field K] [Field F] (P : Polynomial K)
    (u : K) {n : ℕ} (pos : 0 < n) (e : K →+* F) (split : (P.map e).Splits)
    (localIrr : Irreducible (X^n - C (e u))) :
    Irreducible (X^n - C (algebraMap K P.SplittingField u)) := by
  let : Algebra K F := e.toAlgebra
  let f : P.SplittingField →ₐ[K] F := IsSplittingField.lift P.SplittingField P split
  apply (monic_X_pow_sub_C _ pos.ne').isPrimitive.irreducible_of_irreducible_map_of_injective
    (φ := f.toRingHom) f.injective
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  have image : f.toRingHom (algebraMap K P.SplittingField u) = e u := f.commutes u
  rwa [image]

end InverseKummer

namespace InverseKummer
open Polynomial

/-- Expansion at a finite point sends each t−a to z+(b−a), and embeds
the original function field into the fraction field of power series. -/
theorem local_coordinate {K : Type*} [Field K] (b : K) :
    ∃ e : RatFunc K →+* FractionRing (PowerSeries K), ∀ a : K,
      e (algebraMap (Polynomial K) (RatFunc K) (X-C a)) =
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.X + PowerSeries.C (b-a)) := by
  let F := FractionRing (PowerSeries K)
  let f : Polynomial K →+* F := (algebraMap (PowerSeries K) F).comp
    (Polynomial.coeToPowerSeries.ringHom.comp (Polynomial.taylorAlgHom b).toRingHom)
  have inj : Function.Injective f := (IsFractionRing.injective (PowerSeries K) F).comp
    ((Polynomial.coe_injective K).comp (Polynomial.taylor_injective b))
  refine ⟨IsFractionRing.lift inj, fun a => ?_⟩
  rw [IsFractionRing.lift_algebraMap]
  change algebraMap (PowerSeries K) F ((Polynomial.taylor b (X-C a) : Polynomial K) : PowerSeries K) = _
  rw [map_sub, taylor_X, taylor_C]
  simp only [Polynomial.coe_sub,Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C, map_sub]
  simp [F, map_add, map_sub, add_sub_assoc]

end InverseKummer

namespace InverseKummer
open PowerSeries

/-- Raising the binomial series of exponent r to n multiplies its exponent by n. -/
theorem power_binom {K : Type*} [Field K] [CharZero K] (n : ℕ) (r : ℚ) :
    binomialSeries K r ^ n = binomialSeries K ((n:ℚ)*r) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, binomialSeries_add]

/-- Every series X+c with c≠0 has an nth root in K⟦X⟧.  The construction
is b*(1+X/c)^(1/n), where b is an nth root of c in the coefficient field. -/
theorem unramified_root_of_pow {K : Type*} [Field K] [CharZero K]
    {n : ℕ} (pos : 0 < n) {c : K} (nc : c ≠ 0) (root : ∃ b:K, b^n=c) :
    ∃ y : PowerSeries K, y^n = PowerSeries.X + PowerSeries.C c := by
  obtain ⟨b,hb⟩ := root
  have hn : (n:ℚ) ≠ 0 := by exact_mod_cast pos.ne'
  have single : binomialSeries K ((n:ℚ)⁻¹) ^ n = 1 + PowerSeries.X := by
    rw [power_binom, mul_inv_cancel₀ hn]
    simpa using (binomialSeries_nat (A := K) (R := ℚ) 1)
  refine ⟨PowerSeries.C b * PowerSeries.rescale c⁻¹ (binomialSeries K ((n:ℚ)⁻¹)), ?_⟩
  rw [mul_pow, ← map_pow, hb, ← map_pow, single, map_add, map_one, rescale_X, mul_add, mul_one,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ nc, map_one, one_mul, add_comm]

end InverseKummer

namespace InverseKummer
open Polynomial

/-- At a fresh branch point, the other binomials split in the Laurent series
field, while the new binomial is Eisenstein at the power series variable. -/
theorem independent_prefix_of_pow {K : Type*} [Field K] [CharZero K]
    (n : ℕ → ℕ) (a : ℕ → K) (i : ℕ) (positive : ∀ j ≤ i, 0 < n j)
    (separate : ∀ j < i, a j ≠ a i)
    (roots : ∀ j < i, ∃ ζ : K, IsPrimitiveRoot ζ (n j))
    (powers : ∀ j < i, ∃ b:K, b^(n j) = a i-a j) :
    let u (j : ℕ) := algebraMap (Polynomial K) (RatFunc K) (X-C (a j))
    let P := ∏ j ∈ Finset.range i, (X^(n j)-C (u j))
    Irreducible (X^(n i)-C (algebraMap (RatFunc K) P.SplittingField (u i))) := by
  classical
  intro u P
  let S := PowerSeries K
  let F := FractionRing S
  obtain ⟨e, he⟩ := local_coordinate (a i)
  have splits : (P.map e).Splits := by
    dsimp only [P]
    rw [Polynomial.map_prod]
    apply Splits.prod
    intro j hj
    have hj' := Finset.mem_range.mp hj
    obtain ⟨ζ,hζ⟩ := roots j hj'
    obtain ⟨v,hv⟩ := unramified_root_of_pow (positive j hj'.le) (sub_ne_zero.mpr (separate j hj').symm) (powers j hj')
    have rootEq : (algebraMap S F v)^(n j) = e (u j) := by
      rw [← map_pow, hv]
      exact (he (a j)).symm
    rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
    exact X_pow_sub_C_splits_of_isPrimitiveRoot
      (hζ.map_of_injective (algebraMap K F).injective) rootEq
  have image : e (u i) = algebraMap S F PowerSeries.X := by
    exact (he (a i)).trans (by simp [S,F])
  have prime : Prime (PowerSeries.X : S) := PowerSeries.X_prime
  have hn := positive i le_rfl
  have monic := monic_X_pow_sub_C (PowerSeries.X : S) hn.ne'
  have irred := (eisenstein_binomial prime hn).irreducible
    ((Ideal.span_singleton_prime prime.ne_zero).2 prime) monic.isPrimitive
    (by simpa only [natDegree_X_pow_sub_C] using hn)
  have localIrr : Irreducible (X^(n i)-C (algebraMap S F PowerSeries.X)) := by
    simpa using (monic.isPrimitive.irreducible_iff_irreducible_map_fraction_map (K:=F)).mp irred
  apply irreducible_after_split P (u i) hn e splits
  rwa [image]

/-- Over an algebraically closed coefficient field all branch-unit roots exist. -/
theorem independent_prefix {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (n : ℕ → ℕ) (a : ℕ → K) (i : ℕ) (positive : ∀ j ≤ i, 0 < n j)
    (separate : ∀ j < i, a j ≠ a i)
    (roots : ∀ j < i, ∃ ζ : K, IsPrimitiveRoot ζ (n j)) :
    let u (j : ℕ) := algebraMap (Polynomial K) (RatFunc K) (X-C (a j))
    let P := ∏ j ∈ Finset.range i, (X^(n j)-C (u j))
    Irreducible (X^(n i)-C (algebraMap (RatFunc K) P.SplittingField (u i))) :=
  independent_prefix_of_pow n a i positive separate roots
    (fun j hj => IsAlgClosed.exists_pow_nat_eq _ (positive j hj.le))

end InverseKummer

namespace InverseKummer
open Polynomial

/-- A Kummer binomial irreducible over the preceding splitting field adds an
independent cyclic direct factor to the Galois group of the product. -/
theorem product_step {K : Type*} [Field K] [CharZero K]
    (P : K[X]) (P0 : P ≠ 0) {n : ℕ} (hn : 0 < n) {ζ : K}
    (prim : IsPrimitiveRoot ζ n) (u : K)
    (irr : Irreducible (X^n - C (algebraMap K P.SplittingField u))) :
    Nonempty ((P*(X^n-C u)).Gal ≃* P.Gal × Multiplicative (ZMod n)) := by
  classical
  let : NeZero n := ⟨hn.ne'⟩
  let Q : K[X] := X^n-C u
  let K₁ := P.SplittingField
  let E := (P*Q).SplittingField
  let Q₁ : K₁[X] := X^n - C (algebraMap K K₁ u)
  have Qi : Irreducible Q := by
    apply Polynomial.Monic.irreducible_of_irreducible_map (algebraMap K K₁) Q (monic_X_pow_sub_C u hn.ne')
    simpa [Q,K₁] using irr
  have pn : P*Q ≠ 0 := mul_ne_zero P0 Qi.ne_zero
  have spl : ((P*Q).map (algebraMap K E)).Splits := SplittingField.splits _
  let : Fact ((P.map (algebraMap K E)).Splits) := ⟨spl.of_dvd (map_ne_zero pn)
    ((map_dvd_map' _).mpr (dvd_mul_right P Q))⟩
  let : Algebra K₁ E := by dsimp only [K₁]; infer_instance
  have : IsScalarTower K K₁ E := by dsimp [K₁]; infer_instance
  have : FiniteDimensional K₁ E := .right K K₁ E
  have qspl : (Q.map (algebraMap K E)).Splits := spl.of_dvd (map_ne_zero pn)
    ((map_dvd_map' _).mpr (dvd_mul_left Q P))
  have q1spl : (Q₁.map (algebraMap K₁ E)).Splits := by
    simpa [Q₁,Q,IsScalarTower.algebraMap_apply K K₁ E] using qspl
  let inc := IsSplittingField.lift Q₁.SplittingField Q₁ q1spl
  have root₁ : (primitiveRoots n K₁).Nonempty :=
    ⟨_,(mem_primitiveRoots hn).2 (prim.map_of_injective (algebraMap K K₁).injective)⟩
  have bound : n ≤ Module.finrank K₁ E := by
    rw [← finrank_of_isSplittingField_X_pow_sub_C root₁ irr Q₁.SplittingField]
    exact LinearMap.finrank_le_finrank_of_injective (f:=inc.toLinearMap) inc.injective
  have : IsGalois K K₁ := ⟨⟩
  have : IsGalois K E := ⟨⟩
  let cyc : Q.Gal ≃* Multiplicative (ZMod n) := autEquivZmod Qi Q.SplittingField prim
  have qcard : Nat.card Q.Gal = n := (Nat.card_congr (cyc.toEquiv.trans Multiplicative.toAdd)).trans (Nat.card_zmod n)
  have hcard : Nat.card (P.Gal × Q.Gal) ≤ Nat.card (P*Q).Gal := by
    rw [Nat.card_prod,qcard]
    change Nat.card (K₁ ≃ₐ[K] K₁) * n ≤ Nat.card (E ≃ₐ[K] E)
    rw [IsGalois.card_aut_eq_finrank K K₁,IsGalois.card_aut_eq_finrank K E,← Module.finrank_mul_finrank K K₁ E]
    exact Nat.mul_le_mul_left _ bound
  exact ⟨(MulEquiv.ofBijective (Polynomial.Gal.restrictProd P Q)
    ((Polynomial.Gal.restrictProd_injective P Q).bijective_of_nat_card_le hcard)).trans
      ((MulEquiv.refl _).prodCongr cyc)⟩

end InverseKummer

namespace InverseKummer
open Polynomial Finset

/-- Joining an independent sequence of radical covers realizes the product of
its cyclic Galois groups. The test for the next binomial is in the splitting
field of the actual preceding product. -/
theorem product_family {K : Type*} [Field K] [CharZero K]
    (n : ℕ → ℕ) (u : ℕ → K) (m : ℕ)
    (pos : ∀ i < m, 0 < n i) (primitive : ∀ i < m, ∃ ζ : K, IsPrimitiveRoot ζ (n i))
    (irr : ∀ i < m, Irreducible (X^(n i) - C (algebraMap K
      (∏ j ∈ range i, (X^(n j)-C (u j) : K[X])).SplittingField (u i)))) :
    Nonempty ((∏ j∈range m, (X^(n j)-C (u j) : K[X])).Gal ≃*
      ((i : Fin m) → Multiplicative (ZMod (n i.val)))) := by
  classical
  induction m with
  | zero => simp only [range_zero,prod_empty]; exact ⟨MulEquiv.ofUnique⟩
  | succ m ih =>
    rcases ih (fun i h => pos i (Nat.lt_succ_of_lt h))
      (fun i h => primitive i (Nat.lt_succ_of_lt h)) (fun i h => irr i (Nat.lt_succ_of_lt h)) with ⟨prev⟩
    let P : K[X] := ∏ j∈range m, (X^(n j)-C (u j))
    have P0 : P≠0 := Finset.prod_ne_zero_iff.mpr fun j hj =>
      X_pow_sub_C_ne_zero (pos j ((mem_range.mp hj).trans (Nat.lt_succ_self m))) _
    obtain ⟨ζ, hz⟩ := primitive m (Nat.lt_succ_self m)
    obtain ⟨step⟩ := product_step P P0 (pos m (Nat.lt_succ_self m)) hz (u m) (irr m (Nat.lt_succ_self m))
    let A (j : ℕ) := Multiplicative (ZMod (n j))
    let assemble : ((j : Fin m) → A j.val) × A m ≃* ((j : Fin (m+1)) → A j.val) := {
      toEquiv := (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun i : Fin (m+1) => A i.val))
      map_mul' := by
        intro f g
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.snocEquiv]
    }
    rw [prod_range_succ]
    exact ⟨(step.trans (prev.prodCongr (MulEquiv.refl _))).trans assemble⟩

end InverseKummer

namespace InverseKummer
open Polynomial

/-- In characteristic zero, all root-of-unity orders occur in an algebraically
closed coefficient field, by separability of Xⁿ−1. -/
theorem closed_has_primitive (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (n : ℕ) (hn : 0 < n) : ∃ ζ : K, IsPrimitiveRoot ζ n := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let p : K[X] := X^n - C 1
  have h0 : p ≠ 0 := X_pow_sub_C_ne_zero hn 1
  let e : {x : K // x ∈ nthRoots n (1:K)} ≃ p.rootSet K :=
    Equiv.subtypeEquivRight (fun x => by
      rw [mem_nthRoots hn, mem_rootSet_of_ne h0]
      simp [p,sub_eq_zero])
  have finite := Polynomial.card_rootSet_eq_natDegree (K := K)
    (separable_X_pow_sub_C (1:K) (by exact_mod_cast hn.ne') one_ne_zero)
    (IsAlgClosed.splits_domain (f := algebraMap K K) p)
  apply card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
  rw [Nat.card_congr ((rootsOfUnityEquivNthRoots K n).trans e), Nat.card_eq_fintype_card]
  exact finite.trans natDegree_X_pow_sub_C

/-- Independent cyclic radicals over any algebraically closed coefficient
field of characteristic zero. -/
theorem radical_product_closed (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (n : ℕ → ℕ) (m : ℕ) (pos : ∀ j < m, 0 < n j) :
    ∃ P : Polynomial (RatFunc K),
      Nonempty (P.Gal ≃* ((i : Fin m) → Multiplicative (ZMod (n i.val)))) := by
  let u (j : ℕ) := algebraMap (Polynomial K) (RatFunc K) (X - C (j : K))
  refine ⟨_,product_family n u m pos (fun j hj => ?_) (fun i hi => ?_)⟩
  · obtain ⟨ζ,hζ⟩ := closed_has_primitive K _ (pos j hj)
    exact ⟨_,hζ.map_of_injective (algebraMap K (RatFunc K)).injective⟩
  · exact independent_prefix n (fun j => (j : K)) i (fun j hj => pos j (hj.trans_lt hi))
      (fun j hj => by exact_mod_cast hj.ne) (fun j hj => closed_has_primitive K _ (pos j (hj.trans hi)))

end InverseKummer

namespace InverseKummer
open Polynomial

/-- A family realizing every finite product of prescribed cyclic orders
suffices for every finite abelian group, including the trivial group. -/
theorem abelian_of_products {K : Type*} [Field K] [CharZero K]
    (radical_product : ∀ (n : ℕ→ℕ) (m : ℕ), (∀ j < m, 0 < n j) →
      ∃ P : Polynomial K, Nonempty (P.Gal ≃* ((i : Fin m)→Multiplicative (ZMod (n i.val)))))
    (G : Type*) [CommGroup G] [Fintype G] : InverseGalois.IsRealizable K G := by
  classical
  obtain ⟨ι,inst,k,big,⟨decomp⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let n (j : ℕ) := if h : j < m then k (e.symm ⟨j,h⟩) else 1
  have length_eq (i : Fin m) : n i.val=k (e.symm i) := by simp [n,i.isLt]
  obtain ⟨P,⟨gal⟩⟩ := radical_product n m (fun j h => (length_eq ⟨j,h⟩).symm ▸ (Nat.zero_lt_one.trans (big _)))
  let reindex : ((i : ι)→ Multiplicative (ZMod (k i))) ≃* ((i : Fin m)→ Multiplicative (ZMod (k (e.symm i)))) := {
    toEquiv := Equiv.piCongrLeft' _ e
    map_mul' := fun _ _ => rfl
  }
  let relabel : ((i : Fin m) → Multiplicative (ZMod (k (e.symm i)))) ≃* ((i : Fin m) → Multiplicative (ZMod (n i.val))) :=
    MulEquiv.piCongrRight fun i => by rw [length_eq]
  have galois : IsGalois K P.SplittingField := ⟨⟩
  exact ⟨⟨⟨P.SplittingField,inferInstance,inferInstance,galois,
    ((decomp.trans reindex).trans relabel).trans gal.symm⟩⟩⟩

end InverseKummer

namespace InverseKummer

/-- Every finite abelian group is realizable over K(t) for an algebraically
closed characteristic-zero field K. -/
theorem abelian_realizable_closed (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    (G : Type*) [CommGroup G] [Fintype G] : InverseGalois.IsRealizable (RatFunc K) G :=
  abelian_of_products (radical_product_closed K) G

end InverseKummer

end

section

namespace GaloisProjective

/-- A projective matrix representation acts faithfully on a rational generator.
The order of the matrices is reversed because substitution acts on functions. -/
theorem fractional_action {G K F : Type*} [Group G] [Field K] [Field F] [Algebra K F]
    (t : F) (determined : ∀ f g : F ≃ₐ[K] F, f t=g t → f=g)
    (coefficients : ∀ a b c : K, algebraMap K F a * t^2 + algebraMap K F b * t + algebraMap K F c = 0 → a=0 ∧ b=0 ∧ c=0)
    (substitute : ∀ a b c d : K, a*d-b*c≠0 → ∃ f : F ≃ₐ[K] F,
      f t = (algebraMap K F a*t+algebraMap K F b)/(algebraMap K F c*t+algebraMap K F d))
    (a b c d : G → K) (det : ∀ g, a g*d g-b g*c g≠0)
    (product : ∀ g h, ∃ r : K, r≠0 ∧ a (g*h)=r*(a h*a g+b h*c g) ∧ b (g*h)=r*(a h*b g+b h*d g) ∧
      c (g*h)=r*(c h*a g+d h*c g) ∧ d (g*h)=r*(c h*b g+d h*d g))
    (kernel : ∀ g, b g=0 → c g=0 → a g=d g → g=1) :
    ∃ φ : G →* (F ≃ₐ[K] F), Function.Injective φ := by
  classical
  let C := algebraMap K F
  let U (g : G) := C (a g)*t+C (b g)
  let V (g : G) := C (c g)*t+C (d g)
  choose act hact using fun g => substitute (a g) (b g) (c g) (d g) (det g)
  have eval (g : G) : act g t=U g/V g := hact g
  have denom (g : G) : V g ≠ 0 := by
    intro h
    have hc := (coefficients 0 (c g) (d g) (by simpa [C,V] using h)).2
    exact det g (by simp [hc.1,hc.2])
  have constant (g : G) (k : K) : act g (C k)=C k := (act g).commutes k
  have common (g : G) (A B : K) : C A * (U g / V g) + C B = (C A*U g+C B*V g)/V g := by
    field_simp [denom]
  have comp (g h : G) : act (g*h) = act g * act h := by
    apply determined
    obtain ⟨r,r0,ar,br,cr,dr⟩ := product g h
    have rr : C r ≠ 0 := (map_ne_zero _).mpr r0
    have up : U (g*h)=C r*(C (a h)*U g+C (b h)*V g) := by simp only [U,V,ar,br,map_add,map_mul]; ring
    have down : V (g*h)=C r*(C (c h)*U g+C (d h)*V g) := by simp only [U,V,cr,dr,map_add,map_mul]; ring
    rw [AlgEquiv.mul_apply,eval (g*h),eval h,map_div₀,up,down,mul_div_mul_left _ _ rr]
    have num : act g (U h) = C (a h)*(U g/V g)+C (b h) := by simp only [U,map_mul,map_add,constant,eval]
    have de : act g (V h) = C (c h)*(U g/V g)+C (d h) := by simp only [V,map_mul,map_add,constant,eval]
    rw [num,de,common,common,div_div_div_cancel_right₀ (denom g)]
  let φ : G →* (F ≃ₐ[K] F) := {
    toFun := act
    map_one' := by
      have h := (comp 1 1).symm
      exact mul_left_cancel (a:=act 1) (b:=act 1) (c:=1) (by simpa using h)
    map_mul' := comp
  }
  refine ⟨φ,(injective_iff_map_eq_one _).2 ?_⟩
  intro g hg
  have ht := congrArg (fun f : F ≃ₐ[K] F => f t) hg
  change act g t=t at ht
  rw [eval,div_eq_iff (denom g)] at ht
  have key := coefficients (c g) (d g - a g) (-(b g)) (by
    change C _ * t^2+C _*t+C _=0
    rw [map_sub,map_neg]
    change C (a g)*t+C (b g)=t*(C (c g)*t+C (d g)) at ht
    linear_combination -ht)
  exact kernel g (neg_eq_zero.mp key.2.2) key.1 (sub_eq_zero.mp key.2.1).symm

end GaloisProjective

namespace GaloisProjective
open IntermediateField

/-- Coefficients of a polynomial of degree at most two are determined by its
value at the rational-function indeterminate. -/
theorem quadratic_coefficients (K : Type*) [Field K] (a b c : K) :
    let t := (RatFunc.X : RatFunc K)
    let C := algebraMap K (RatFunc K)
    C a*t^2+C b*t+C c=0 → a=0 ∧ b=0 ∧ c=0 := by
  intro t C h
  let P := Polynomial.C a*Polynomial.X^2+Polynomial.C b*Polynomial.X+Polynomial.C c
  have eq : P=0 := (RatFunc.algebraMap_injective K) (by simpa [P,t,C,RatFunc.algebraMap_eq_C] using h)
  have co (i : ℕ) := congrArg (fun p : Polynomial K => p.coeff i) eq
  exact ⟨by simpa [P,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow] using co 2,
    by simpa [P,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow] using co 1,
    by simpa [P,Polynomial.coeff_add,Polynomial.coeff_C_mul,Polynomial.coeff_X_pow] using co 0⟩

/-- An invertible two-by-two matrix induces the indicated rational-function substitution. -/
theorem fractional_substitution {K : Type*} [Field K] (a b c d : K) (det : a*d-b*c≠0) :
    let X := (RatFunc.X : RatFunc K)
    let C := algebraMap K (RatFunc K)
    ∃ f : RatFunc K ≃ₐ[K] RatFunc K, f X=(C a*X+C b)/(C c*X+C d) := by
  intro X C
  let U := C a*X+C b
  let V := C c*X+C d
  have V0 : V≠0 := by
    intro h
    have hc := (quadratic_coefficients K 0 c d (by simpa [C,X,V] using h)).2
    exact det (by simp [hc.1,hc.2])
  let w := U/V
  have wr : w*V=U := div_mul_cancel₀ U V0
  have scalar : (C a-C c*w)*V = C (a*d-b*c) := by
    rw [sub_mul,mul_assoc,wr,map_sub,map_mul,map_mul]
    dsimp only [U,V]
    ring
  have dn : C a-C c*w≠0 := fun h => (map_ne_zero C).mpr det (by simpa [h] using scalar.symm)
  have inv : (C d*w-C b)/(C a-C c*w)=X := by
    apply (div_eq_iff dn).mpr
    apply mul_right_cancel₀ V0
    rw [sub_mul,mul_assoc,wr,mul_assoc,scalar,map_sub,map_mul,map_mul]
    dsimp only [U,V]
    ring
  let E := adjoin K {w}
  have wm : w∈E := mem_adjoin_simple_self K w
  have cm (i : K) : C i∈E := E.algebraMap_mem i
  have gen : X∈E := inv ▸ E.div_mem (E.sub_mem (E.mul_mem (cm d) wm) (cm b))
    (E.sub_mem (cm a) (E.mul_mem (cm c) wm))
  have tr : Transcendental K w := by
    intro hw
    let : Algebra.IsAlgebraic K E := isAlgebraic_adjoin_simple hw.isIntegral
    have hx := Algebra.IsAlgebraic.isAlgebraic (R:=K) (⟨X,gen⟩ : E)
    exact RatFunc.transcendental_X (IntermediateField.isAlgebraic_iff.mp hx)
  have top : E=⊤ := eq_top_iff.mpr (RatFunc.adjoin_X (K:=K) ▸ adjoin_simple_le_iff.mpr gen)
  exact ⟨(RatFunc.algEquivOfTranscendental w tr).trans ((equivOfEq top).trans topEquiv),
    RatFunc.algEquivOfTranscendental_X w tr⟩

/-- A projective representation with scalar kernel gives a faithful action
on the rational function field. The input matrices compose in their usual order. -/
theorem projective_action {G K : Type*} [Group G] [Field K]
    (a b c d : G→K) (det : ∀ g, a g*d g-b g*c g≠0)
    (product : ∀ g h, ∃ r : K, r≠0 ∧ a (g*h)=r*(a g*a h+b g*c h) ∧ b (g*h)=r*(a g*b h+b g*d h) ∧
      c (g*h)=r*(c g*a h+d g*c h) ∧ d (g*h)=r*(c g*b h+d g*d h))
    (kernel : ∀ g, b g=0 → c g=0 → a g=d g → g=1) :
    ∃ φ : G →* (RatFunc K ≃ₐ[K] RatFunc K), Function.Injective φ := by
  let t := (RatFunc.X : RatFunc K)
  have determined (f g : RatFunc K ≃ₐ[K] RatFunc K) (agree : f t=g t) : f=g := by
    apply AlgEquiv.ext
    intro z
    have hz : z ∈ adjoin K {t} := by change z ∈ adjoin K {(RatFunc.X : RatFunc K)}; rw [RatFunc.adjoin_X]; trivial
    exact adjoin_induction K (p:=fun w _ => f w=g w)
      (fun _ h => (Set.mem_singleton_iff.mp h) ▸ agree)
      (fun x => (f.commutes x).trans (g.commutes x).symm)
      (fun _ _ _ _ h k => by simp [h,k]) (fun _ _ h => by simp [h])
      (fun _ _ _ _ h k => by simp [h,k]) hz
  apply fractional_action t determined (quadratic_coefficients K) fractional_substitution
    (fun g : G => a g⁻¹) (fun g => b g⁻¹) (fun g => c g⁻¹) (fun g => d g⁻¹) (fun g => det g⁻¹)
  · intro g h
    simpa only [mul_inv_rev] using product h⁻¹ g⁻¹
  · intro g hb hc hd
    exact inv_eq_one.mp (kernel g⁻¹ hb hc hd)

end GaloisProjective

end

section

namespace GaloisProjective
open Matrix
open scoped MatrixGroups

/-- A choice of matrix representatives of a faithful subgroup of PGL₂
supplies the explicit coefficient laws for Möbius substitutions. -/
theorem action_of_projective_reps {G K : Type*} [Group G] [Field K]
    (M : G → GL (Fin 2) K)
    (comp : ∀ g h, ∃ u : Kˣ, (M g*M h)*GeneralLinearGroup.scalar (Fin 2) u=M (g*h))
    (faithful : ∀ g, (∃ u : Kˣ, M g=GeneralLinearGroup.scalar (Fin 2) u) → g=1) :
    ∃ φ : G →* (RatFunc K ≃ₐ[K] RatFunc K), Function.Injective φ := by
  apply projective_action (fun g => M g 0 0) (fun g => M g 0 1) (fun g => M g 1 0) (fun g => M g 1 1)
  · intro g
    simpa only [Matrix.det_fin_two] using (M g).det_ne_zero
  · intro g h
    obtain ⟨r,eq⟩ := comp g h
    have coeff (i j : Fin 2) : M (g*h) i j = (r:K)*(M g i 0*M h 0 j+M g i 1*M h 1 j) := by
      rw [←eq]
      change ((M g*M h).val * Matrix.diagonal (fun _ : Fin 2 => (r:K))) i j = _
      rw [← Matrix.smul_eq_mul_diagonal]
      simp only [Matrix.smul_apply,smul_eq_mul,Units.val_mul,Matrix.mul_apply,Fin.sum_univ_two]
    exact ⟨r,r.ne_zero,coeff 0 0,coeff 0 1,coeff 1 0,coeff 1 1⟩
  · intro g hb hc hd
    have hn : M g 0 0≠0 := by
      intro hz
      have nonzero := (M g).det_ne_zero
      rw [Matrix.det_fin_two] at nonzero
      exact nonzero (by simp [hb,hc,hz])
    let r : Kˣ := Units.mk0 _ hn
    apply faithful g
    refine ⟨r,Units.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,r,hb,hc,hd]

end GaloisProjective

namespace GaloisProjective
open Matrix
open scoped MatrixGroups

/-- PGL₂(K) acts faithfully by K-automorphisms on the rational function field. -/
theorem pgl2_action (K : Type*) [Field K] :
    ∃ φ : PGL(2,K) →* (RatFunc K ≃ₐ[K] RatFunc K), Function.Injective φ := by
  classical
  choose M rep using (ProjGenLinGroup.mk_surjective : ∀ g : PGL(2,K), ∃ A : GL (Fin 2) K, ProjGenLinGroup.mk A=g)
  apply action_of_projective_reps M
  · intro g h
    apply ProjGenLinGroup.mk_eq_mk_iff.mp
    rw [map_mul,rep,rep,rep]
  · intro g
    rintro ⟨u,h⟩
    rw [←rep g,h,ProjGenLinGroup.mk_scalar]

end GaloisProjective

namespace GaloisProjective
open scoped MatrixGroups

/-- A finite group with a faithful two-dimensional projective representation
is realizable over the rational function field, over the same base field. -/
theorem pgl2_realizable {G K : Type*} [Group G] [Finite G] [Field K]
    (ρ : G →* PGL(2,K)) (faithful : Function.Injective ρ) :
    InverseGalois.IsRealizable (RatFunc K) G := by
  obtain ⟨φ,inj⟩ := pgl2_action K
  exact ProjectiveGalois.realize_of_faithful_action (φ.comp ρ) (inj.comp faithful)

end GaloisProjective

end

section

namespace OctahedralRealization

set_option maxHeartbeats 3200000 in
/-- The Möbius transformations generated by z ↦ iz and z ↦ (z+i)/(z−i)
give a faithful projective matrix representation of S₄ on the sphere.
We label the four pairs of opposite faces of the octahedron. All finite
checks below are over pairs of integers and are verified by the kernel. -/
theorem matrix_data :
    ∃ a b c d : Equiv.Perm (Fin 4) → ℂ,
      (∀ g, a g*d g-b g*c g ≠ 0) ∧
      (∀ g h, ∃ r : ℂ, r ≠ 0 ∧
        a (g*h) = r*(a g*a h+b g*c h) ∧ b (g*h) = r*(a g*b h+b g*d h) ∧
        c (g*h) = r*(c g*a h+d g*c h) ∧ d (g*h) = r*(c g*b h+d g*d h)) ∧
      (∀ g, b g=0 → c g=0 → a g=d g → g=1) := by
  let read (table i width : ℕ) := (table >>> (i*width)) % (2^width)
  let rank (a b c : Fin 4) : Fin 24 := Fin.ofNat 24 (read 1472582897285356021002835605436087857881149829947992691537890474795089242693550341095424 (16*a.val+4*b.val+c.val) 5)
  let row (i : Fin 24) (k : Fin 4) : Fin 4 := Fin.ofNat 4 (read 669236436005411928080145373044091295208890640391302853860 (4*i.val+k.val) 2)
  let idx (g : Equiv.Perm (Fin 4)) := rank (g 0) (g 1) (g 2)
  let comp (i j : Fin 24) := rank (row i (row j 0)) (row i (row j 1)) (row i (row j 2))
  let M (i : Fin 24) (k : ℕ) : ℤ × ℤ :=
    let n := read 3121248534064312387378762838210613146664895807608397621848787680253290087262485966515556806584082442155171016832071 (4*i.val+k) 4
    ((n/3 : ℕ) - (1:ℤ),(n%3 : ℕ) - (1:ℤ))
  let scalar (i j : Fin 24) : ℤ × ℤ :=
    let n := read 656823222574163038941025681622252759542890833058340613728151764555688745610241609801912179032147240144946502018432382388788341983093447736143633532219117071398000003815622811176774517733443246347066500291253063441482340920175664299903954741417809294139524259380727274995021200995778272240420975546151861691938834083125912432093988842120588848112772472942641458758685490686192349502651282797793344684294856251994189284063412212303017998672772355709661201905806923107579459628395650936929397254091979786126193243789745645680508103023691653627002762868836961210820791387477206000227185680190480910139425533349980381868292471322879261863428870885437564589275150029966017773342261633204302112863176593042957604811239377832294945397389338437351147569111908793719084311699391940244969971723869917532252903451067147043908043718507723696953009917106211214109534593249153080022 (24*i.val+j.val) 5
    ((n/5 : ℕ) - (2:ℤ),(n%5 : ℕ) - (2:ℤ))
  let mul (x y : ℤ × ℤ) : ℤ × ℤ := (x.1*y.1-x.2*y.2,x.1*y.2+x.2*y.1)
  let sum (x y : ℤ × ℤ) : ℤ × ℤ := (x.1+y.1,x.2+y.2)
  have enum : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      row (rank a b c) 0 = a ∧ row (rank a b c) 1 = b ∧
      row (rank a b c) 2 = c ∧ row (rank a b c) 3 = d := by
    dsimp only [rank,row,read]
    decide +kernel
  have repr (g : Equiv.Perm (Fin 4)) (k : Fin 4) : row (idx g) k = g k := by
    obtain ⟨h0,h1,h2,h3⟩ := enum (g 0) (g 1) (g 2) (g 3) (g.injective.ne (by decide))
      (g.injective.ne (by decide)) (g.injective.ne (by decide)) (g.injective.ne (by decide))
      (g.injective.ne (by decide)) (g.injective.ne (by decide))
    fin_cases k <;> assumption
  have mult (g h : Equiv.Perm (Fin 4)) : idx (g*h)=comp (idx g) (idx h) := by
    simp only [idx,comp,Equiv.Perm.mul_apply] at ⊢
    change rank (g (h 0)) (g (h 1)) (g (h 2)) = rank (row (idx g) (row (idx h) 0))
      (row (idx g) (row (idx h) 1)) (row (idx g) (row (idx h) 2))
    simp only [repr]
  let left (i j : Fin 24) (k : ℕ) := mul (2,0) (M (comp i j) k)
  let right (i j : Fin 24) (a b c d : ℕ) :=
    mul (scalar i j) (sum (mul (M i a) (M j b)) (mul (M i c) (M j d)))
  have nonsing : ∀ i, mul (M i 0) (M i 3) ≠ mul (M i 1) (M i 2) := by
    dsimp only [M,mul,read]
    decide +kernel
  have identity : ∀ i, M i 1 = (0,0) → M i 2 = (0,0) → M i 0 = M i 3 →
      ∀ k, row i k = k := by
    dsimp only [row,M,read]
    decide +kernel
  have product : ∀ i j, scalar i j ≠ (0,0) ∧ left i j 0 = right i j 0 0 1 2 ∧
      left i j 1 = right i j 0 1 1 3 ∧ left i j 2 = right i j 2 0 3 2 ∧
      left i j 3 = right i j 2 1 3 3 := by
    intro i
    fin_cases i <;> dsimp only [left,right,mul,sum,scalar,comp,row,rank,M,read] <;> decide +kernel
  let coeff (g : Equiv.Perm (Fin 4)) := M (idx g)
  let scale (g h : Equiv.Perm (Fin 4)) := scalar (idx g) (idx h)
  let lhs (g h : Equiv.Perm (Fin 4)) (i : ℕ) := mul (2,0) (coeff (g*h) i)
  let rhs (g h : Equiv.Perm (Fin 4)) (i j k l : ℕ) :=
    mul (scale g h) (sum (mul (coeff g i) (coeff h j)) (mul (coeff g k) (coeff h l)))
  have cert :
      (∀ g, mul (coeff g 0) (coeff g 3) ≠ mul (coeff g 1) (coeff g 2)) ∧
      (∀ g h, scale g h ≠ (0,0) ∧ lhs g h 0 = rhs g h 0 0 1 2 ∧
        lhs g h 1 = rhs g h 0 1 1 3 ∧ lhs g h 2 = rhs g h 2 0 3 2 ∧
        lhs g h 3 = rhs g h 2 1 3 3) ∧
      (∀ g, coeff g 1=(0,0) → coeff g 2=(0,0) → coeff g 0=coeff g 3 → g=1) := by
    refine ⟨fun g => nonsing (idx g), ?_, ?_⟩
    · intro g h
      simpa only [scale,lhs,rhs,coeff,left,right,mult] using product (idx g) (idx h)
    · intro g b c t
      apply Equiv.ext
      intro k
      exact (repr g k).symm.trans (identity (idx g) b c t k)
  let ev (x : ℤ × ℤ) : ℂ := ⟨x.1,x.2⟩
  have inj : Function.Injective ev := by
    intro x y eq
    apply Prod.ext
    · exact_mod_cast (show (x.1 : ℝ) = y.1 from congrArg Complex.re eq)
    · exact_mod_cast (show (x.2 : ℝ) = y.2 from congrArg Complex.im eq)
  have ev0 : ev (0,0)=0 := by apply Complex.ext <;> norm_num [ev]
  have ev2 : ev (2,0)=2 := by apply Complex.ext <;> norm_num [ev]
  have hmul (x y : ℤ × ℤ) : ev (mul x y)=ev x * ev y := by
    apply Complex.ext <;> simp [ev,mul,Complex.mul_re,Complex.mul_im]
  have hsum (x y : ℤ × ℤ) : ev (sum x y)=ev x + ev y := by
    apply Complex.ext <;> simp [ev,sum]
  refine ⟨fun g => ev (coeff g 0),fun g => ev (coeff g 1),fun g => ev (coeff g 2),
    fun g => ev (coeff g 3),?_,?_,?_⟩
  · intro g
    apply sub_ne_zero.mpr
    simpa only [← hmul] using inj.ne (cert.1 g)
  · intro g h
    obtain ⟨nz,e0,e1,e2,e3⟩ := cert.2.1 g h
    refine ⟨ev (scale g h)/2,div_ne_zero (by simpa only [← ev0] using inj.ne nz) (by norm_num),?_⟩
    have transport (i j k l m : ℕ) (eq : lhs g h i = rhs g h j k l m) :
        ev (coeff (g*h) i) = ev (scale g h)/2 *
          (ev (coeff g j)*ev (coeff h k)+ev (coeff g l)*ev (coeff h m)) := by
      have h := congrArg ev eq
      simp only [lhs,rhs,hmul,hsum,ev2] at h
      linear_combination h / 2
    exact ⟨transport _ _ _ _ _ e0,transport _ _ _ _ _ e1,
      transport _ _ _ _ _ e2,transport _ _ _ _ _ e3⟩
  · intro g b c ad
    exact cert.2.2 g (inj (b.trans ev0.symm)) (inj (c.trans ev0.symm)) (inj ad)

end OctahedralRealization

end

section

namespace OctahedralRealization

/-- Every subgroup of the octahedral group acts faithfully on the rational
function field and is Galois over another rational function field. -/
theorem group_embedded_in_symmetric_four {G : Type*} [Group G] [Finite G]
    (e : G →* Equiv.Perm (Fin 4)) (injective : Function.Injective e) :
    InverseGalois.IsRealizable (RatFunc ℂ) G := by
  obtain ⟨a,b,c,d,det,product,kernel⟩ := matrix_data
  obtain ⟨action,faithful⟩ := GaloisProjective.projective_action a b c d det product kernel
  exact ProjectiveGalois.realize_of_faithful_action (action.comp e) (faithful.comp injective)

theorem symmetric_four : InverseGalois.IsRealizable (RatFunc ℂ) (Equiv.Perm (Fin 4)) :=
  group_embedded_in_symmetric_four (MonoidHom.id _) Function.injective_id

end OctahedralRealization

end

section

namespace GaloisIcosa

theorem cyclotomic_arithmetic :
  let W := (ℤ × ℤ) × (ℤ × ℤ)

  let zero : W := ((0,0),(0,0))
  let one : W := ((1,0),(0,0))
  let add (x y : W) : W := ((x.1.1 + y.1.1, x.1.2 + y.1.2), (x.2.1 + y.2.1, x.2.2 + y.2.2))
  let neg (x : W) : W := ((-x.1.1,-x.1.2),(-x.2.1,-x.2.2))

  let mul (x y : W) : W :=
    let d₀ := x.1.1*y.1.1
    let d₁ := x.1.2*y.1.1 + x.1.1*y.1.2
    let d₂ := x.2.1*y.1.1 + x.1.2*y.1.2 + x.1.1*y.2.1
    let d₃ := x.2.2*y.1.1 + x.2.1*y.1.2 + x.1.2*y.2.1 + x.1.1*y.2.2
    let d₄ := x.2.2*y.1.2 + x.2.1*y.2.1 + x.1.2*y.2.2
    let d₅ := x.2.2*y.2.1 + x.2.1*y.2.2
    let d₆ := x.2.2*y.2.2
    ((d₀-d₄+d₅,d₁-d₄+d₆),(d₂-d₄,d₃-d₄))
  ∃ ev : W→ℂ, Function.Injective ev ∧ ev zero=0 ∧ ev one=1 ∧
    (∀x y,ev (add x y)=ev x+ev y) ∧ (∀x,ev (neg x)= -ev x) ∧
    (∀x y,ev (mul x y)=ev x*ev y) := by
  intro W zero one add neg mul
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I/(5:ℕ))
  let ev (x : W) : ℂ := x.1.1 + x.1.2 * ζ + x.2.1 * ζ^2 + x.2.2 * ζ^3

  have primitive : IsPrimitiveRoot ζ 5 := Complex.isPrimitiveRoot_exp 5 (by decide)

  have ev_zero : ev zero = 0 := by simp [ev,zero]
  have ev_one : ev one = 1 := by simp [ev,one]
  have ev_add (x y : W) : ev (add x y) = ev x + ev y := by
    simp only [ev,add,Int.cast_add]
    ring
  have ev_neg (x : W) : ev (neg x) = -ev x := by
    simp only [ev,neg,Int.cast_neg]
    ring
  have ev_mul (x y : W) : ev (mul x y) = ev x * ev y := by
    have h4 : 1+ζ+ζ^2+ζ^3+ζ^4=0 := by
      simpa only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,pow_one] using
        primitive.geom_sum_eq_zero (by decide)
    have h5 : ζ^5=1 := primitive.pow_eq_one
    have h6 : ζ^6=ζ := by rw [show 6=5+1 by decide,pow_succ,h5,one_mul]
    simp only [ev,mul,Int.cast_add,Int.cast_sub,Int.cast_mul]
    linear_combination -(x.2.2*y.1.2+x.2.1*y.2.1+x.1.2*y.2.2 : ℂ)*h4 -
      (x.2.2*y.2.1+x.2.1*y.2.2 : ℂ)*h5 - (x.2.2*y.2.2 : ℂ)*h6
  have ev_injective_of_degree (deg : (minpoly ℚ ζ).natDegree=4) : Function.Injective ev := by
    have independent := linearIndependent_pow (K:=ℚ) ζ
    rw [deg] at independent
    rintro ⟨⟨a,b⟩,c,d⟩ ⟨⟨e,f⟩,g,h⟩ eq
    let w : Fin 4 → ℚ := ![((a-e:ℤ):ℚ), ((b-f:ℤ):ℚ), ((c-g:ℤ):ℚ), ((d-h:ℤ):ℚ)]
    have sum : ∑ i : Fin 4, w i • ζ^(i:ℕ) = 0 := by
      simp only [ev] at eq
      simp [w,Fin.sum_univ_succ,Algebra.smul_def]
      linear_combination eq
    have all := Fintype.linearIndependent_iff.mp independent w sum
    have p0 := all (0:Fin 4)
    have p1 := all (1:Fin 4)
    have p2 := all (2:Fin 4)
    have p3 := all (3:Fin 4)
    simp [w,sub_eq_zero] at p0 p1 p2 p3
    subst_vars
    rfl
  have ev_injective : Function.Injective ev := by
    apply ev_injective_of_degree
    rw [← Polynomial.cyclotomic_eq_minpoly_rat primitive (by decide), Polynomial.natDegree_cyclotomic]
    decide
  exact ⟨ev, ev_injective, ev_zero, ev_one, ev_add, ev_neg, ev_mul⟩

end GaloisIcosa

namespace GaloisIcosa

/-- A constructive numbering of A₅ by the orbit of the identity under a
five-cycle and a double transposition. Every number has an explicit word. -/
theorem labels :
    let next := (fun (i : Fin 60) (b : Bool) => (#[16,3,20,6,22,9,29,0,31,7,35,10,40,1,44,4,46,11,53,2,55,5,59,8,5,15,7,18,11,21,25,12,32,19,33,22,38,13,42,16,47,23,49,14,56,17,57,20,1,27,8,30,9,33,14,24,18,31,23,34,36,25,41,28,45,35,50,26,51,29,58,32,2,39,3,42,10,45,12,36,17,43,21,46,26,37,27,40,34,47,48,38,52,41,54,44,0,51,4,54,6,57,13,48,15,55,19,58,24,49,28,52,30,59,37,50,39,53,43,56] : Array (Fin 60))[2*i.val+b.toNat]!)
    ∃ ix : alternatingGroup (Fin 5) → Fin 60, ∃ gen : Bool → alternatingGroup (Fin 5),
      (∀ g, ∃ w : List Bool, (w.map gen).prod=g) ∧
      (∀ g b, ix (g*gen b)=next (ix g) b) ∧ ix 1=0 ∧
      (∀ b,ix (gen b)=if b then 3 else 16) ∧ (∀g,ix g=0 → g=1) := by
  intro next
  let R : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4
  let S : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 3 4
  have hr : R ∈ alternatingGroup (Fin 5) := by simp [R,Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap' ]
  have hs : S ∈ alternatingGroup (Fin 5) := by simp [S,Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_swap' ]
  let gen (b : Bool) : alternatingGroup (Fin 5) := if b then ⟨S,hs⟩ else ⟨R,hr⟩
  let perm (b : Bool) : Equiv.Perm (Fin 5) := if b then S else R
  have valGen (b : Bool) : (gen b).val = perm b := by cases b <;> rfl
  have project (w : List Bool) : ((w.map gen).prod).val=(w.map perm).prod := by
    induction w with
    | nil => rfl
    | cons b w ih => simp only [List.map_cons,List.prod_cons,Subgroup.coe_mul,valGen,ih]
  let rank (i j k : Fin 5) : Fin 60 := (#[0,0,0,0,0,0,0,0,1,2,0,3,0,4,5,0,6,7,0,8,0,9,10,11,0,0,0,12,13,14,0,0,0,0,0,15,0,0,16,17,18,0,19,0,20,21,0,22,23,0,0,24,0,25,26,27,0,0,28,29,0,0,0,0,0,30,31,0,0,32,33,34,0,35,0,0,36,37,0,38,39,0,40,0,41,42,43,0,0,44,0,0,0,0,0,45,46,47,0,0,0,48,49,50,0,51,0,52,53,0,54,55,0,56,0,57,58,59,0,0,0,0,0,0,0] : Array (Fin 60))[25*i.val+5*j.val+k.val]!
  let row (i : Fin 60) (k : Fin 5) : Fin 5 := (#[0,1,2,3,4,0,1,3,4,2,0,1,4,2,3,0,2,1,4,3,0,2,3,1,4,0,2,4,3,1,0,3,1,2,4,0,3,2,4,1,0,3,4,1,2,0,4,1,3,2,0,4,2,1,3,0,4,3,2,1,1,0,2,4,3,1,0,3,2,4,1,0,4,3,2,1,2,0,3,4,1,2,3,4,0,1,2,4,0,3,1,3,0,4,2,1,3,2,0,4,1,3,4,2,0,1,4,0,2,3,1,4,2,3,0,1,4,3,0,2,2,0,1,3,4,2,0,3,4,1,2,0,4,1,3,2,1,0,4,3,2,1,3,0,4,2,1,4,3,0,2,3,0,1,4,2,3,1,4,0,2,3,4,0,1,2,4,0,3,1,2,4,1,0,3,2,4,3,1,0,3,0,1,4,2,3,0,2,1,4,3,0,4,2,1,3,1,0,2,4,3,1,2,4,0,3,1,4,0,2,3,2,0,4,1,3,2,1,0,4,3,2,4,1,0,3,4,0,1,2,3,4,1,2,0,3,4,2,0,1,4,0,1,2,3,4,0,2,3,1,4,0,3,1,2,4,1,0,3,2,4,1,2,0,3,4,1,3,2,0,4,2,0,1,3,4,2,1,3,0,4,2,3,0,1,4,3,0,2,1,4,3,1,0,2,4,3,2,1,0] : Array (Fin 5))[5*i.val+k.val]!
  let ix (g : alternatingGroup (Fin 5)) := rank (g.val 0) (g.val 1) (g.val 2)
  let word (i : Fin 60) := (#[[],[true,false,false,false,true,false,true],[false,true,false,false,false,true],[true],[true,false,true,false,false,false,true],[false,false,false,true,false,true],[true,false,false,false,true,false],[true,false,true,false,false,false],[false,false,true,false,false,false,true,false,false],[false,true,false,false,false],[false,false,false,true,false],[false,false,true,false,false,false,true,false,false,true],[false,false,true,false,false,false],[true,false,true,false,false],[true,false,false,true,false,false,false,true,false],[false,false,true,false,false,false,true],[false],[false,true,false,false,false,true,false,true],[true,false,true,false,false,true],[false,true],[true,false,false,true],[false,false,false,true,false,false,false,true,false,false],[false,true,false,false,false,true,false],[true,false,false],[true,false,false,true,false,false,false],[false,false,true,false,false,false,true,false],[false,true,false,false],[true,false,false,true,false,false,false,true],[false,false,false,true,false,false,false],[true,false],[false,false,true,false,false,false,true,false,true],[false,false,false,true,false,false,false,true],[false,false],[false,true,false,false,true],[true,false,true],[false,false,true],[false,false,true,false,false,true],[false,true,false,true],[false,false,false,true],[false,false,true,false,false],[true,false,false,false,true,false,false],[false,false,false,true,false,false,false,true,false],[false,true,false],[true,false,false,false,true,false,false,true],[true,false,false,true,false,true],[false,false,false],[false,false,false,true,false,false,false,true,false,true],[true,false,false,true,false],[false,false,false,false],[true,false,false,true,false,false,true],[true,false,false,false,true],[true,false,true,false],[false,false,false,true,false,false,true],[false,false,true,false,true],[true,false,false,true,false,false],[false,false,false,true,false,false],[false,true,false,false,false,true,false,false],[true,false,false,false],[false,false,true,false],[false,true,false,false,false,true,false,false,true]] : Array (List Bool))[i.val]!
  let tag (i : Fin 60) := ((word i).map gen).prod
  have rep (i : Fin 60) (k : Fin 5) : (tag i).val k=row i k := by
    change ((word i).map gen).prod.val k = row i k
    rw [project]
    revert i k
    dsimp only [word,perm,R,S,row]
    decide +kernel
  have cancel : ∀ i : Fin 60, rank (row i 0) (row i 1) (row i 2)=i := by dsimp only [rank,row]; decide +kernel
  have taginv (i : Fin 60) : ix (tag i)=i := by simp only [ix,rep,cancel]
  have full : Function.Surjective tag := (Function.LeftInverse.injective taginv).bijective_of_nat_card_le (by
    rw [nat_card_alternatingGroup,Nat.card_fin,Nat.card_fin]; decide) |>.surjective
  refine ⟨ix,gen,?_,?_,?_,?_,?_⟩
  · intro g
    obtain ⟨i,rfl⟩ := full g
    exact ⟨word i,rfl⟩
  · intro g b
    obtain ⟨i,rfl⟩ := full g
    rw [taginv]
    change rank ((tag i).val ((gen b).val 0)) ((tag i).val ((gen b).val 1)) ((tag i).val ((gen b).val 2)) = _
    simp only [rep,valGen]
    revert i b
    dsimp only [rank,row,perm,R,S,next]
    decide +kernel
  · change rank 0 1 2=0
    decide +kernel
  · intro b
    simp only [ix,valGen]
    cases b <;> dsimp only [rank,perm,R,S] <;> decide +kernel
  · intro g h
    obtain ⟨i,rfl⟩ := full g
    rw [taginv] at h
    subst i
    rfl

end GaloisIcosa

namespace GaloisIcosa

/-- Projective multiplication needs checking only for multiplication on the
right by generators whose positive words exhaust the group. -/
theorem products_of_generators {G K : Type*} [Group G] [Field K] {ι : Type*}
    (gen : ι → G) (generate : ∀ g, ∃ w : List ι, (w.map gen).prod=g)
    (M : G → Matrix (Fin 2) (Fin 2) K) (unit : M 1=1)
    (step : ∀ g b, ∃ u : K, u≠0 ∧ M (g*gen b)=u • (M g*M (gen b))) :
    ∀ g h, ∃ u : K, u≠0 ∧ M (g*h)=u • (M g*M h) := by
  intro g h
  obtain ⟨w,rfl⟩ := generate h
  induction w generalizing g with
  | nil => exact ⟨1,one_ne_zero,by simp [unit]⟩
  | cons b w ih =>
    let t := (w.map gen).prod
    obtain ⟨p,p0,hp⟩ := step g b
    obtain ⟨q,q0,hq⟩ := ih (g*gen b)
    obtain ⟨r,r0,hr⟩ := ih (gen b)
    refine ⟨q*p/r,div_ne_zero (mul_ne_zero q0 p0) r0,?_⟩
    change M (g*(gen b*t))=(q*p/r) • (M g*M (gen b*t))
    change M ((g*gen b)*t)=q • (M (g*gen b)*M t) at hq
    change M (gen b*t)=r • (M (gen b)*M t) at hr
    rw [← mul_assoc,hq,hp,hr,smul_mul_assoc,mul_smul_comm,smul_smul,smul_smul,div_mul_cancel₀ _ r0,mul_assoc]

end GaloisIcosa

namespace GaloisIcosa

/-- The sixty icosahedral projective matrices over the fifth cyclotomic field.
Checking multiplication by both generators at each row gives the full table. -/
theorem matrix_data_from_arithmetic (arithmetic :
  let W := (ℤ × ℤ) × (ℤ × ℤ)
  let zero : W := ((0,0),(0,0))
  let one : W := ((1,0),(0,0))
  let add (x y : W) : W := ((x.1.1 + y.1.1, x.1.2 + y.1.2), (x.2.1 + y.2.1, x.2.2 + y.2.2))
  let neg (x : W) : W := ((-x.1.1,-x.1.2),(-x.2.1,-x.2.2))
  let mul (x y : W) : W :=
    let d₀ := x.1.1*y.1.1
    let d₁ := x.1.2*y.1.1 + x.1.1*y.1.2
    let d₂ := x.2.1*y.1.1 + x.1.2*y.1.2 + x.1.1*y.2.1
    let d₃ := x.2.2*y.1.1 + x.2.1*y.1.2 + x.1.2*y.2.1 + x.1.1*y.2.2
    let d₄ := x.2.2*y.1.2 + x.2.1*y.2.1 + x.1.2*y.2.2
    let d₅ := x.2.2*y.2.1 + x.2.1*y.2.2
    let d₆ := x.2.2*y.2.2
    ((d₀-d₄+d₅,d₁-d₄+d₆),(d₂-d₄,d₃-d₄))
  ∃ ev : W → ℂ, Function.Injective ev ∧ ev zero=0 ∧ ev one=1 ∧ (∀x y,ev (add x y)=ev x+ev y) ∧ (∀x,ev (neg x)= -ev x) ∧ (∀x y,ev (mul x y)=ev x*ev y)) :
    ∃ a b c d : alternatingGroup (Fin 5) → ℂ,
      (∀g,a g*d g-b g*c g≠0) ∧
      (∀g h,∃r:ℂ,r≠0 ∧ a (g*h)=r*(a g*a h+b g*c h) ∧ b (g*h)=r*(a g*b h+b g*d h) ∧
        c (g*h)=r*(c g*a h+d g*c h) ∧ d (g*h)=r*(c g*b h+d g*d h)) ∧
      (∀g,b g=0 → c g=0 → a g=d g → g=1) := by
  let W := (ℤ × ℤ) × (ℤ × ℤ)
  let zero : W := ((0,0),(0,0))
  let one : W := ((1,0),(0,0))
  let add (x y : W) : W := ((x.1.1 + y.1.1, x.1.2 + y.1.2), (x.2.1 + y.2.1, x.2.2 + y.2.2))
  let neg (x : W) : W := ((-x.1.1,-x.1.2),(-x.2.1,-x.2.2))
  let mul (x y : W) : W :=
    let d₀ := x.1.1*y.1.1
    let d₁ := x.1.2*y.1.1 + x.1.1*y.1.2
    let d₂ := x.2.1*y.1.1 + x.1.2*y.1.2 + x.1.1*y.2.1
    let d₃ := x.2.2*y.1.1 + x.2.1*y.1.2 + x.1.2*y.2.1 + x.1.1*y.2.2
    let d₄ := x.2.2*y.1.2 + x.2.1*y.2.1 + x.1.2*y.2.2
    let d₅ := x.2.2*y.2.1 + x.2.1*y.2.2
    let d₆ := x.2.2*y.2.2
    ((d₀-d₄+d₅,d₁-d₄+d₆),(d₂-d₄,d₃-d₄))
  change ∃ ev : W → ℂ, Function.Injective ev ∧ ev zero=0 ∧ ev one=1 ∧ (∀x y,ev (add x y)=ev x+ev y) ∧ (∀x,ev (neg x)= -ev x) ∧ (∀x y,ev (mul x y)=ev x*ev y) at arithmetic
  obtain ⟨ev,inj,ev_zero,ev_one,ev_add,_,ev_mul⟩ := arithmetic
  let next := (fun (i : Fin 60) (b : Bool) => (#[16,3,20,6,22,9,29,0,31,7,35,10,40,1,44,4,46,11,53,2,55,5,59,8,5,15,7,18,11,21,25,12,32,19,33,22,38,13,42,16,47,23,49,14,56,17,57,20,1,27,8,30,9,33,14,24,18,31,23,34,36,25,41,28,45,35,50,26,51,29,58,32,2,39,3,42,10,45,12,36,17,43,21,46,26,37,27,40,34,47,48,38,52,41,54,44,0,51,4,54,6,57,13,48,15,55,19,58,24,49,28,52,30,59,37,50,39,53,43,56] : Array (Fin 60))[2*i.val+b.toNat]!)
  let generator (b : Bool) : Fin 60 := if b then 3 else 16
  let m (i : Fin 60) (k : ℕ) : W := (#[((1,0),(0,0)),((0,0),(0,0)),((0,1),(1,0)),((1,1),(0,0)),((0,0),(-1,0)),((0,-1),(-1,-1)),((-1,-1),(-1,0)),((0,0),(0,-1)),((-1,0),(-1,-1)),((-1,0),(0,0)),((1,0),(1,0)),((-1,-1),(0,-1)),((1,1),(1,1)),((0,0),(1,1)),((0,1),(0,1)),((1,0),(0,1)),((0,-1),(0,0)),((-1,-1),(-1,-1)),((0,0),(0,1)),((0,0),(1,0)),((0,1),(0,0))] : Array W)[(#[0,1,1,0,0,2,3,4,0,5,6,7,0,8,8,9,0,3,2,4,0,10,11,12,0,6,5,7,0,11,10,12,0,13,13,9,0,14,15,16,0,15,14,16,1,0,9,1,0,14,11,9,0,15,10,9,1,0,12,1,0,5,13,4,0,1,1,17,0,2,5,16,0,10,14,7,0,8,15,12,0,3,3,16,0,13,2,12,0,6,6,4,0,11,8,7,0,13,3,7,0,6,13,16,0,11,15,4,1,0,7,1,0,14,14,12,0,15,8,12,0,2,6,9,0,5,2,16,0,1,1,18,0,3,5,9,0,10,10,4,0,8,11,7,0,3,6,12,0,10,8,16,0,8,14,4,0,11,11,16,0,13,5,4,0,6,2,9,0,15,15,7,1,0,4,1,0,14,10,7,0,1,1,19,0,2,13,12,0,5,3,9,0,1,1,20,0,2,2,7,0,5,5,12,0,8,10,16,0,3,13,7,0,10,15,9,0,6,3,12,0,11,14,9,0,13,6,16,0,14,8,4,0,15,11,4,1,0,16,1] : Array ℕ)[4*i.val+k]!]!
  let scale (i : Fin 60) (b : Bool) : W := (#[((1,0),(0,0)),((2,1),(1,1)),((1,0),(-1,0)),((3,0),(1,1)),((1,0),(0,-1)),((0,1),(-1,0)),((1,-1),(0,0)),((2,1),(0,2)),((-1,0),(-2,-2)),((1,-1),(1,-1)),((-1,-1),(-1,-2)),((-1,-1),(-1,-1)),((-1,0),(-1,-1))] : Array W)[(#[0,0,0,1,0,2,0,3,0,4,0,5,0,6,0,7,0,8,0,9,0,10,11,12,0,9,0,10,11,12,0,2,0,0,0,1,0,5,0,3,0,4,0,8,0,6,0,7,0,8,0,6,0,7,11,12,0,9,0,10,0,1,0,2,0,0,0,4,0,5,0,3,0,4,0,5,0,3,0,7,0,8,0,6,0,10,11,12,0,9,0,0,0,1,0,2,0,0,0,1,0,2,0,3,0,4,0,5,0,6,0,7,0,8,0,9,0,10,11,12] : Array ℕ)[2*i.val+b.toNat]!]!
  let sum (i : Fin 60) (b : Bool) (p q r s : ℕ) := add (mul (m i p) (m (generator b) q)) (mul (m i r) (m (generator b) s))
  let left (i : Fin 60) (b : Bool) (j : ℕ) := mul (scale i b) (m (next i b) j)
  have det : ∀ i, mul (m i 0) (m i 3) ≠ mul (m i 1) (m i 2) := by dsimp only [m]; decide +kernel
  have unit : m 0 0=one ∧ m 0 1=zero ∧ m 0 2=zero ∧ m 0 3=one := by dsimp only [m]; decide +kernel
  have ker : ∀ i, m i 1=zero → m i 2=zero → m i 0=m i 3 → i=0 := by dsimp only [m]; decide +kernel
  have roots : ∀ i b, scale i b≠zero ∧ left i b 0=sum i b 0 0 1 2 ∧
      left i b 1=sum i b 0 1 1 3 ∧ left i b 2=sum i b 2 0 3 2 ∧ left i b 3=sum i b 2 1 3 3 := by
    intro i
    fin_cases i <;> dsimp only [scale,left,sum,next,m,generator] <;> decide +kernel
  obtain ⟨ix,gen,generate,step,zeroIx,generatorIx,kerIx⟩ := labels
  let entry (g : alternatingGroup (Fin 5)) (i : ℕ) := ev (m (ix g) i)
  let A (g : alternatingGroup (Fin 5)) : Matrix (Fin 2) (Fin 2) ℂ := !![entry g 0,entry g 1;entry g 2,entry g 3]
  have a1 : A 1=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A,entry,zeroIx,unit.1,unit.2.1,unit.2.2.1,unit.2.2.2,ev_one,ev_zero]
  have asucc (g : alternatingGroup (Fin 5)) (b : Bool) : ∃ r : ℂ, r≠0 ∧ A (g*gen b)=r • (A g * A (gen b)) := by
    obtain ⟨s0,eq0,eq1,eq2,eq3⟩ := roots (ix g) b
    let s := ev (scale (ix g) b)
    have ne : s≠0 := by simpa only [s,← ev_zero] using inj.ne s0
    have transport (z p q r v : ℕ) (he : left (ix g) b z = sum (ix g) b p q r v) :
        entry (g*gen b) z = s⁻¹ * (entry g p*entry (gen b) q+entry g r*entry (gen b) v) := by
      have h := congrArg ev he
      simp only [left,sum,ev_mul,ev_add] at h
      dsimp only [entry]
      rw [step,generatorIx]
      change ev (m (next (ix g) b) z) = s⁻¹ * _
      rw [←h,←mul_assoc,inv_mul_cancel₀ ne,one_mul]
    refine ⟨s⁻¹,inv_ne_zero ne,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [A,Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,smul_eq_mul,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val',Matrix.of_apply]
    · exact transport _ _ _ _ _ eq0
    · exact transport _ _ _ _ _ eq1
    · exact transport _ _ _ _ _ eq2
    · exact transport _ _ _ _ _ eq3
  refine ⟨fun g => entry g 0,fun g => entry g 1,fun g => entry g 2,fun g => entry g 3,?_,?_,?_⟩
  · intro g
    apply sub_ne_zero.mpr
    simpa only [entry,←ev_mul] using inj.ne (det (ix g))
  · intro g h
    obtain ⟨r,nz,eq⟩ := products_of_generators gen generate A a1 asucc g h
    have co (i j : Fin 2) := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℂ => N i j) eq
    refine ⟨r,nz,?_,?_,?_,?_⟩
    · simpa [A,Matrix.mul_apply,Fin.sum_univ_two] using co 0 0
    · simpa [A,Matrix.mul_apply,Fin.sum_univ_two] using co 0 1
    · simpa [A,Matrix.mul_apply,Fin.sum_univ_two] using co 1 0
    · simpa [A,Matrix.mul_apply,Fin.sum_univ_two] using co 1 1
  · intro g hb hc hd
    exact kerIx g (ker _ (inj (hb.trans ev_zero.symm)) (inj (hc.trans ev_zero.symm)) (inj hd))

end GaloisIcosa

namespace GaloisIcosa

/-- The alternating group on five letters is realized over ℂ(t) by the
icosahedral projective transformations over the fifth cyclotomic field. -/
theorem icosahedral_realizable : InverseGalois.IsRealizable (RatFunc ℂ) (alternatingGroup (Fin 5)) := by
  obtain ⟨a,b,c,d,det,prod,ker⟩ := matrix_data_from_arithmetic cyclotomic_arithmetic
  obtain ⟨φ,faithful⟩ := GaloisProjective.projective_action a b c d det prod ker
  exact ProjectiveGalois.realize_of_faithful_action φ faithful

end GaloisIcosa

end

section

open Set Filter Topology

namespace GaloisSlits

/-- A horizontal segment in the open half plane followed by a vertical segment reaches any
point in the chart cut along parallel rays. -/
theorem chart_connected (D : Set ℝ) (s : ℝ) (hs : s ≠ 0) :
    IsPathConnected {z : ℂ | 0 < s * z.im ∨ z.re ∉ D} := by
  have ss : 0 < s*s := mul_self_pos.mpr hs
  refine ⟨⟨0,s⟩, Or.inl ss, ?_⟩
  intro z hz
  let w : ℂ := ⟨z.re,s⟩
  refine JoinedIn.trans (y:=w) (.of_segment_subset ?_) (.of_segment_subset ?_)
  · rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    left
    change 0 < s * (a • (⟨0,s⟩ : ℂ) + b • w).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, w]
    rw [← add_mul,hab,one_mul]
    exact ss
  · rintro _ ⟨a,b,ha,hb,hab,rfl⟩
    rcases hz with hi | hr
    · left
      simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero,w]
      have h1 := mul_nonneg ha ss.le
      have h2 := mul_nonneg hb hi.le
      rcases eq_or_lt_of_le ha with zero|pos
      · have eq : b=1 := by linarith
        simp [← zero,eq,hi]
      · nlinarith [mul_pos pos ss]
    · right
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, w]
      rw [← add_mul,hab,one_mul]
      exact hr

/-- The two horizontal half planes extend to slit charts having one overlap strip
for each real sample, including the leftmost strip containing the origin. -/
theorem slit_atlas (n : ℕ) {A : Type*} [TopologicalSpace A] (e : A) (a : Fin n → A) :
    let s : Set ℂ := range (fun i : Fin n => (i.val : ℂ) + 1)
    ∃ U V : Set ↥sᶜ, ∃ label : ↥sᶜ → A,
      IsOpen U ∧ IsOpen V ∧ (∀ x, x ∈ U ∨ x ∈ V) ∧
      IsPathConnected U ∧ IsPathConnected V ∧ ContinuousOn label (U ∩ V) ∧
      (∃ o ∈ U ∩ V, (o : ℂ) = 0 ∧ label o = e) ∧
      ∀ i : Fin n, ∃ x ∈ U ∩ V, label x = a i := by
  classical
  intro s
  let p (i : Fin n) : ℝ := i.val + 1
  let D : Set ℝ := range p
  let chart (v : ℝ) : Set ℂ := {z | 0 < v*z.im ∨ z.re ∉ D}
  have inside (v : ℝ) : chart v ⊆ sᶜ := by
    rintro z (hi|hr) ⟨i,rfl⟩
    · simp at hi
    · exact hr ⟨i,by simp [p]⟩
  let W (v : ℝ) : Set ↥sᶜ := Subtype.val ⁻¹' chart v
  have opened (v : ℝ) : IsOpen (W v) := by
    have dom : IsOpen Dᶜ := (finite_range p).isClosed.isOpen_compl
    exact ((isOpen_lt continuous_const (continuous_const.mul Complex.continuous_im)).union
      (dom.preimage Complex.continuous_re)).preimage continuous_subtype_val
  have connected (v : ℝ) (hv : v ≠ 0) : IsPathConnected (W v) :=
    (chart_connected D v hv).preimage_coe (inside v)
  let status (z : ↥sᶜ) (i : Fin n) : Prop := p i < z.val.re
  let decode (f : Fin n → Prop) : A :=
    if h : ∃ j : Fin n, ∀ k, f k ↔ k ≤ j then a h.choose else e
  let label (z : ↥sᶜ) : A := decode (status z)
  have overlap (z : ↥sᶜ) : z ∈ W 1 ∩ W (-1) ↔ z.val.re ∉ D := by
    change ((0 < 1*z.val.im ∨ z.val.re ∉ D) ∧
      (0 < (-1)*z.val.im ∨ z.val.re ∉ D)) ↔ _
    constructor
    · rintro ⟨hi|hr,lo|hr⟩ <;> first | exact hr | linarith
    · exact fun hr => ⟨Or.inr hr,Or.inr hr⟩
  refine ⟨W 1,W (-1),label,opened _,opened _,?_,connected _ one_ne_zero,
    connected _ (by norm_num),?_,?_,?_⟩
  · intro z
    by_cases hr : z.val.re ∈ D
    · have him : z.val.im ≠ 0 := by
        rintro hz
        obtain ⟨i,hi⟩ := hr
        apply z.property
        refine ⟨i,Complex.ext ?_ ?_⟩
        · simpa [p] using hi
        · simp [hz]
      rcases lt_or_gt_of_ne him with lo|hi
      · exact Or.inr (Or.inl (by linarith))
      · exact Or.inl (Or.inl (by simpa using hi))
    · exact Or.inl (Or.inr hr)
  · intro z hz
    have clear := (overlap z).mp hz
    have locally (i : Fin n) : ∀ᶠ y in 𝓝 z, status y i ↔ status z i := by
      have sep : p i ≠ z.val.re := fun eq => clear ⟨i,eq⟩
      have cont : Continuous (fun y : ↥sᶜ => y.val.re) :=
        Complex.continuous_re.comp continuous_subtype_val
      rcases lt_or_gt_of_ne sep with lo|hi
      · exact ((continuousAt_const.eventually_lt cont.continuousAt lo)).mono
          (fun _ hy => iff_of_true hy lo)
      · exact ((cont.continuousAt.eventually_lt continuousAt_const hi)).mono
          (fun _ hy => iff_of_false (not_lt_of_gt hy) (not_lt_of_gt hi))
    have fixed : ∀ᶠ y in 𝓝 z, label y = label z := by
      filter_upwards [Filter.eventually_all.mpr locally] with y hy
      exact congrArg decode (funext fun i => propext (hy i))
    exact (continuousAt_const.congr_of_eventuallyEq fixed).continuousWithinAt
  · have zeroClear : (0 : ℝ) ∉ D := by
      rintro ⟨i,h⟩
      change (i.val:ℝ)+1 = 0 at h
      linarith [Nat.cast_nonneg (α:=ℝ) i.val]
    have zeroIn : (0 : ℂ) ∈ sᶜ := inside 1 (Or.inr (by simpa using zeroClear))
    let o : ↥sᶜ := ⟨0,zeroIn⟩
    refine ⟨o,(overlap o).mpr (by simpa [o] using zeroClear),rfl,?_⟩
    have no : ¬ ∃ j, ∀ k, status o k ↔ k ≤ j := by
      rintro ⟨j,h⟩
      have hneg := (h j).mpr le_rfl
      change (j.val:ℝ)+1 < 0 at hneg
      linarith [Nat.cast_nonneg (α:=ℝ) j.val]
    exact dif_neg no
  · intro i
    let t : ℝ := p i + 1/2
    have sep (k : Fin n) : p k ≠ t := by
      intro eq
      by_cases h : k.val ≤ i.val
      · have hc : (k.val:ℝ) ≤ i.val := by exact_mod_cast h
        dsimp [p,t] at eq; linarith
      · have hc : (i.val:ℝ) + 1 ≤ k.val := by exact_mod_cast (show i.val+1 ≤ k.val by omega)
        dsimp [p,t] at eq; linarith
    have clear : t ∉ D := fun ⟨k,eq⟩ => sep k eq
    have insideT : ((t : ℝ) : ℂ) ∈ sᶜ := inside 1 (Or.inr (by simpa using clear))
    let z : ↥sᶜ := ⟨(t : ℂ),insideT⟩
    refine ⟨z,(overlap z).mpr (by simpa [z] using clear),?_⟩
    have cut (k : Fin n) : status z k ↔ k ≤ i := by
      change (k.val:ℝ)+1 < (i.val:ℝ)+1+1/2 ↔ k.val ≤ i.val
      constructor
      · intro hk
        by_contra h
        have hc : (i.val:ℝ) + 1 ≤ k.val := by exact_mod_cast (show i.val+1 ≤ k.val by omega)
        linarith
      · intro hk
        have hc : (k.val:ℝ) ≤ i.val := by exact_mod_cast hk
        linarith
    have h : ∃ j, ∀ k, status z k ↔ k ≤ j := ⟨i,cut⟩
    change (if h : ∃ j, ∀ k, status z k ↔ k ≤ j then a h.choose else e) = a i
    rw [dif_pos h]
    apply congrArg a
    exact le_antisymm ((cut _).mp ((h.choose_spec _).mpr le_rfl))
      ((h.choose_spec _).mp ((cut _).mpr le_rfl))

end GaloisSlits

open Set
namespace GaloisSlits

/-- Connecting two sheets at an overlap point realizes right multiplication
by the transition factor. Paths compose, and reversing paths realizes inverses. -/
theorem chart_sheets_connected {X G E : Type*} [TopologicalSpace X] [Group G]
    [TopologicalSpace E] (side : Bool → Set X) (label : X → G)
    (sheet : (i : Bool) → G → side i → E) (cont : ∀ i g, Continuous (sheet i g))
    (change : ∀ g x (u : x ∈ side false) (v : x ∈ side true),
      sheet false g ⟨x,u⟩ = sheet true (g*label x) ⟨x,v⟩)
    (full : ∀ y : E, ∃ i g x, sheet i g x = y)
    (pcU : IsPathConnected (side false)) (pcV : IsPathConnected (side true))
    (o : X) (ho : o ∈ side false ∩ side true) (neutral : label o = 1)
    (S : Set G) (gen : Subgroup.closure S = ⊤)
    (occurs : ∀ h ∈ S, ∃ x ∈ side false ∩ side true, label x = h) :
    PathConnectedSpace E := by
  let p (g : G) := sheet false g ⟨o,ho.1⟩
  have common (g : G) : p g = sheet true g ⟨o,ho.2⟩ := by
    simpa only [p,neutral,mul_one] using change g o ho.1 ho.2
  have travel (i : Bool) (g : G) (x y : side i) : Joined (sheet i g x) (sheet i g y) := by
    have conn : IsPathConnected (side i) := by cases i; exact pcU; exact pcV
    exact ((conn.joinedIn x.1 x.2 y.1 y.2).joined_subtype).map (cont i g)
  let H : Subgroup G :=
    { carrier := {h | ∀ g, Joined (p g) (p (g*h))}
      one_mem' := fun g => by simpa only [mul_one] using Joined.refl (p g)
      mul_mem' := by
        intro u v hu hv g
        simpa only [mul_assoc] using (hu g).trans (hv (g*u))
      inv_mem' := by
        intro u hu g
        simpa only [inv_mul_cancel_right] using (hu (g*u⁻¹)).symm }
  have hS : S ⊆ H := by
    intro h hh g
    obtain ⟨x,hx,hlabel⟩ := occurs h hh
    have alongU := travel false g ⟨o,ho.1⟩ ⟨x,hx.1⟩
    have atx := change g x hx.1 hx.2
    rw [hlabel] at atx
    rw [atx] at alongU
    have alongV := travel true (g*h) ⟨x,hx.2⟩ ⟨o,ho.2⟩
    exact (common (g*h)).symm ▸ alongU.trans alongV
  have all : (⊤ : Subgroup G) ≤ H := gen ▸ (Subgroup.closure_le H).mpr hS
  have whole (g : G) : Joined (p 1) (p g) := by
    have h : g ∈ H := all (Subgroup.mem_top g)
    simpa only [one_mul] using h 1
  have reach (y : E) : Joined (p 1) y := by
    obtain ⟨i,g,x,rfl⟩ := full y
    apply (whole g).trans
    cases i
    · exact travel false g ⟨o,ho.1⟩ x
    · rw [common]
      exact travel true g ⟨o,ho.2⟩ x
  exact ⟨⟨p 1⟩,fun x y => (reach x).symm.trans (reach y)⟩

end GaloisSlits


namespace PlaneClutch

open Set Filter Topology

/-- Clutch a regular covering from two open path-connected charts. A transition generator
connects any sheet to its right translate, so monodromy at every base point surjects. -/
theorem quotient_of_two_charts {X G : Type*} [TopologicalSpace X] [Group G]
    [TopologicalSpace G] [DiscreteTopology G] (U V : Set X) (label : X → G)
    (openU : IsOpen U) (openV : IsOpen V) (covers : ∀ x, x ∈ U ∨ x ∈ V)
    (locally : ContinuousOn label (U∩V)) (pcU : IsPathConnected U) (pcV : IsPathConnected V)
    (o : X) (ho : o ∈ U∩V) (neutral : label o = 1)
    (S : Set G) (gen : Subgroup.closure S = ⊤)
    (occurs : ∀ h ∈ S, ∃ x ∈ U∩V, label x = h) (base : X) :
    ∃ f : FundamentalGroup X base →* G, Function.Surjective f := by
  classical
  let side (i : Bool) : Set X := if i then V else U
  let trans (i j : Bool) (x : X) : G :=
    match i,j with
    | false,true => label x
    | true,false => (label x)⁻¹
    | _,_ => 1
  let core : FiberBundleCore Bool X G := by
    refine {
      baseSet := side
      isOpen_baseSet i := by cases i <;> simp [side,openU,openV]
      indexAt x := if x∈U then false else true
      mem_baseSet_at x := ?_
      coordChange i j x g := g*trans i j x
      coordChange_self := ?_
      coordChange_comp := ?_
      continuousOn_coordChange := ?_ }
    · split_ifs with h <;> simp [side,h,(covers x).resolve_left]
    · intro i x hx g; cases i <;> simp [trans]
    · intro i j
      have move : ContinuousOn (trans i j) (side i∩side j) := by
        cases i <;> cases j
        · exact continuous_const.continuousOn
        · exact locally
        · change ContinuousOn (Inv.inv ∘ label) (V∩U)
          rw [inter_comm]
          exact (continuous_of_discreteTopology (f:=Inv.inv)).comp_continuousOn locally
        · exact continuous_const.continuousOn
      have b := move.comp continuous_fst.continuousOn (fun p (h : p∈(side i∩side j) ×ˢ (univ : Set G)) => h.1)
      exact (continuous_of_discreteTopology (f:=fun p : G×G => p.1*p.2)).comp_continuousOn (continuous_snd.continuousOn.prodMk b)

    · intro i j k x hx g; cases i <;> cases j <;> cases k <;> simp [trans,mul_assoc]
  let E := core.TotalSpace

  let pt (x : X) (g : G) : E := ⟨x,g⟩

  let coord (e : E) : G := e.2

  let shift (g : G) (e : E) : E := pt e.1 (g*coord e)

  let : MulAction G E := {
    smul := shift
    one_smul e := by
      change pt e.1 (1*coord e)=e
      rw [one_mul]
    mul_smul g h e := by
      change pt e.1 ((g*h)*coord e)=pt e.1 (g*(h*coord e))
      rw [mul_assoc] }

  have chart_shift (i : Bool) (g : G) (e : E) : core.localTriv i (shift g e) =
      ((core.localTriv i e).1,g*(core.localTriv i e).2) := by
    change (e.1,(g*coord e)*trans (core.indexAt e.1) i e.1) =
      (e.1,g*(coord e*trans (core.indexAt e.1) i e.1))
    rw [mul_assoc]

  have continuous_shift (g : G) : Continuous (shift g) := by
    rw [continuous_iff_continuousAt]
    intro e
    let i := core.indexAt e.1
    let L := (core.localTriv i).toOpenPartialHomeomorph
    have he : e∈L.source := core.mem_baseSet_at e.1
    have pre : shift g ⁻¹' L.source∈𝓝 e := L.open_source.mem_nhds he
    apply (L.continuousAt_iff_continuousAt_comp_left pre).mpr
    have map : Continuous (fun q : X×G => (q.1,g*q.2)) :=
      continuous_fst.prodMk ((continuous_of_discreteTopology (f:=fun a : G => g*a)).comp continuous_snd)
    exact (map.continuousAt.comp (L.continuousAt he)).congr
      (Filter.Eventually.of_forall (fun z => (chart_shift i g z).symm))

  let sheet (i : Bool) (g : G) (x : side i) : E :=
    (core.localTriv i).toOpenPartialHomeomorph.symm (x.1,g)

  have sheet_continuous (i : Bool) (g : G) : Continuous (sheet i g) := by
    let L := (core.localTriv i).toOpenPartialHomeomorph
    exact L.continuousOn_symm.comp_continuous (continuous_subtype_val.prodMk continuous_const)
      (fun x => (core.localTriv i).mem_target.mpr x.2)

  have quotient_cover : IsQuotientCoveringMap core.proj G := {
    toIsQuotientMap := core.isOpenMap_proj.isQuotientMap core.continuous_proj
      (fun x => ⟨pt x 1,rfl⟩)
    continuous_const_smul g := continuous_shift g
    apply_eq_iff_mem_orbit := by
      rintro ⟨x,a⟩ ⟨y,b⟩
      let A : G := a
      let B : G := b
      change x=y ↔ ∃ g : G,pt y (g*B)=pt x A
      constructor
      · rintro rfl
        exact ⟨A*B⁻¹,by simp⟩
      · rintro ⟨g,eq⟩
        exact (congrArg Bundle.TotalSpace.proj eq).symm
    disjoint e := by
      let i := core.indexAt e.1
      let L := (core.localTriv i).toOpenPartialHomeomorph
      let S : Set E := L.source ∩ L ⁻¹' ((univ : Set X) ×ˢ {(L e).2})
      refine ⟨S,?_,?_⟩
      · have he : e∈L.source := core.mem_baseSet_at e.1
        have op := (isOpen_univ (X:=X)).prod (isOpen_discrete ({(L e).2}:Set G))
        have mem : (L e) ∈ ((univ : Set X) ×ˢ {(L e).2}) := ⟨mem_univ _,rfl⟩
        exact inter_mem (L.open_source.mem_nhds he) ((L.continuousAt he) (op.mem_nhds mem))
      · rintro g ⟨z,⟨w,hw,rfl⟩,hg⟩
        have left : (L w).2=(L e).2 := hw.2.2
        have right : (L (shift g w)).2=(L e).2 := hg.2.2
        have eq := congrArg Prod.snd (chart_shift i g w)
        change (L (shift g w)).2=g*(L w).2 at eq
        rw [right,left] at eq
        exact (mul_eq_right.mp eq.symm) }

  have sheet_change (i j : Bool) (g : G) (x : X) (hi : x∈side i) (hj : x∈side j) :
      sheet i g ⟨x,hi⟩ = sheet j (g*trans i j x) ⟨x,hj⟩ := by
    exact congrArg (pt x) ((core.coordChange_comp i j (core.indexAt x) x
      ⟨⟨hi,hj⟩,core.mem_baseSet_at x⟩ g).symm)

  have sheet_at (e : E) :
      sheet (core.indexAt e.1) (coord e) ⟨e.1,core.mem_baseSet_at e.1⟩=e := by
    change pt e.1 (core.coordChange (core.indexAt e.1) (core.indexAt e.1) e.1 (coord e))=e
    rw [core.coordChange_self _ _ (core.mem_baseSet_at _)]

  have : PathConnectedSpace E :=
    GaloisSlits.chart_sheets_connected side label sheet sheet_continuous
      (sheet_change false true) (fun y => ⟨_,_,_,sheet_at y⟩)
      pcU pcV o ho neutral S gen occurs
  let elder : core.proj ⁻¹' {base} := ⟨pt base 1,rfl⟩
  let eqv := (MulEquiv.inv' G).symm
  exact ⟨eqv.toMonoidHom.comp (quotient_cover.fundamentalGroupToMulOpposite elder),
    eqv.surjective.comp (quotient_cover.fundamentalGroupToMulOpposite_surjective elder)⟩

/-- The fundamental group of the plane with the first n positive integers
removed has the free group on n generators as a quotient. -/
theorem integral_punctures (n : ℕ) :
    let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val+1 : ℕ) : ℂ)}
    let base : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
    ∃ f : FundamentalGroup U base →* FreeGroup (Fin n), Function.Surjective f := by
  classical
  intro U base
  let G := FreeGroup (Fin n)
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  let D : Set ℂ := {z | ∀ i : Fin n, z ≠ ((i.val+1 : ℕ) : ℂ)}
  have sets : (Set.range (fun i : Fin n => (i.val:ℂ)+1))ᶜ = D := by
    ext x
    simp [D,Set.mem_compl_iff,eq_comm]
  have data := GaloisSlits.slit_atlas n (1 : G) (FreeGroup.of : Fin n → G)
  dsimp only at data
  rw [sets] at data
  obtain ⟨U₀,U₁,lab,o₀,o₁,cover,p₀,p₁,loc,⟨o,ho,_,id⟩,generators⟩ := data
  exact quotient_of_two_charts U₀ U₁ lab o₀ o₁ cover loc p₀ p₁ o ho id
    (Set.range (FreeGroup.of : Fin n → G)) (FreeGroup.closure_range_of _)
    (by rintro _ ⟨i,rfl⟩; exact generators i) base

end PlaneClutch

end

section

namespace InverseGalois
open IntermediateField

/-- The fixed field of the closed kernel realizes a quotient of a Galois group.
The quotient group may be presented in a different universe from the fields. -/
theorem realizable_of_closed_quotient {K L : Type u} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] {G : Type v} [Group G]
    (f : (L ≃ₐ[K] L) →* G) (onto : Function.Surjective f)
    (closed : IsClosed (f.ker : Set (L ≃ₐ[K] L))) :
    IsRealizable K G := by
  let H : ClosedSubgroup (L ≃ₐ[K] L) := ⟨f.ker, closed⟩
  let : H.toSubgroup.Normal := f.normal_ker
  exact ⟨⟨{
    L := fixedField H.toSubgroup
    to_field := inferInstance
    to_algebra := inferInstance
    to_isGalois := inferInstance
    iso := (QuotientGroup.quotientKerEquivOfSurjective f onto).symm.trans
      (InfiniteGalois.normalAutEquivQuotient H)
  }⟩⟩

/-- A continuous epimorphism from the absolute Galois group to a Hausdorff group
gives a realization over the original field. -/
theorem realizable_of_absolute_quotient {K : Type u} [Field K] [CharZero K]
    {G : Type v} [Group G] [TopologicalSpace G] [T1Space G]
    (f : Field.absoluteGaloisGroup K →* G) (continuous : Continuous f)
    (onto : Function.Surjective f) : IsRealizable K G := by
  apply realizable_of_closed_quotient (K := K) (L := AlgebraicClosure K) f onto
  exact (isClosed_singleton (X := G) (x := 1)).preimage continuous

end InverseGalois

end

section

namespace GaloisMonodromy
open CategoryTheory ProfiniteGrp
open ProfiniteGrp.ProfiniteCompletion

/-- A finite quotient of a discrete group is also a continuous quotient of its
profinite completion. Evaluating the inverse limit at the kernel gives the map. -/
theorem finite_quotient_of_completion {P : Type u} [Group P]
    {G : Type v} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
    (f : P →* G) (onto : Function.Surjective f) :
    ∃ h : completion (GrpCat.of P) →* G, Continuous h ∧ Function.Surjective h := by
  let N := FiniteIndexNormalSubgroup.ofSubgroup f.ker
  let projection := (limitCone (diagram (GrpCat.of P))).π.app N
  let e := QuotientGroup.quotientKerEquivOfSurjective f onto
  let g : completion (GrpCat.of P) →* G := e.toMonoidHom.comp projection.hom.toMonoidHom
  refine ⟨g, ?_, ?_⟩
  · let Q := (diagram (GrpCat.of P)).obj N
    have : Finite Q := Finite.of_equiv G e.symm.toEquiv
    have : DiscreteTopology Q := Finite.instDiscreteTopology
    exact (continuous_of_discreteTopology (f := fun z : Q => e z)).comp projection.hom.continuous
  · intro y
    obtain ⟨x,hx⟩ := onto y
    exact ⟨etaFn (GrpCat.of P) x, hx⟩

/-- Enumerating the group elements gives a concrete quotient of a finite-rank
free group even if the target group lives in a larger universe. -/
theorem finite_group_quotient (G : Type v) [Fintype G] [Group G] :
    ∃ f : FreeGroup (Fin (Fintype.card G)) →* G, Function.Surjective f :=
  ⟨FreeGroup.lift (Fintype.equivFin G).symm,
    FreeGroup.lift_surjective_of_surjective (Fintype.equivFin G).symm.surjective⟩

end GaloisMonodromy

namespace GaloisMonodromy
open InverseGalois ProfiniteGrp

/-- The topological and algebraic comparison argument for a punctured line.
A free quotient of sufficient rank and a profinite comparison epimorphism
are enough to construct the desired Galois extension as a fixed field. -/
theorem realizable_from_monodromy {K : Type u} [Field K] [CharZero K]
    {P : Type v} [Group P] {G : Type w} [Group G] [Fintype G]
    (loops : P →* FreeGroup (Fin (Fintype.card G))) (surj : Function.Surjective loops)
    (comparison : Field.absoluteGaloisGroup K →* ProfiniteCompletion.completion (GrpCat.of P))
    (cont : Continuous comparison) (cover : Function.Surjective comparison) :
    IsRealizable K G := by
  let : TopologicalSpace G := ⊥
  let : DiscreteTopology G := ⟨rfl⟩
  obtain ⟨f,onto⟩ := finite_group_quotient G
  obtain ⟨h,hc,ho⟩ := finite_quotient_of_completion (f.comp loops) (onto.comp surj)
  exact realizable_of_absolute_quotient (h.comp comparison) (hc.comp cont) (ho.comp cover)

/-- Fixing the punctures at the first n positive integers gives a specific
family of branch loci, with 0 as the common base point. -/
theorem punctured_line
    (topological : ∀ n : ℕ,
      let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val+1 : ℕ) : ℂ)}
      let base : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
      ∃ f : FundamentalGroup U base →* FreeGroup (Fin n), Function.Surjective f)
    (geometric : ∀ n : ℕ,
      let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val+1 : ℕ) : ℂ)}
      let base : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
      ∃ f : Field.absoluteGaloisGroup (RatFunc ℂ) →*
        ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup U base)),
        Continuous f ∧ Function.Surjective f) :
    type_of% @InverseGalois.inverse_galois_problem.variants.complex_rational_functions := by
  intro G fi grp
  obtain ⟨π,hπ⟩ := topological (Fintype.card G)
  obtain ⟨f,hc,hs⟩ := geometric (Fintype.card G)
  exact realizable_from_monodromy π hπ f hc hs

end GaloisMonodromy

namespace GaloisMonodromy
open InverseGalois ProfiniteGrp

/-- The only remaining input is the profinite geometric comparison for the explicit punctures. -/
theorem realization_of_plane_comparison
    (geometric : ∀ n : ℕ,
      let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val+1 : ℕ) : ℂ)}
      let base : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
      ∃ f : Field.absoluteGaloisGroup (RatFunc ℂ) →*
        ProfiniteCompletion.completion (GrpCat.of (FundamentalGroup U base)),
        Continuous f ∧ Function.Surjective f) :
    type_of% @InverseGalois.inverse_galois_problem.variants.complex_rational_functions :=
  punctured_line PlaneClutch.integral_punctures geometric

end GaloisMonodromy

end

section

namespace GaloisMonodromy
open RegularWreathProduct

/-- Recording an arbitrary list of group elements on a cyclic set gives a
two-generator finite monodromy group. Its cyclic quotient records rotation.
The kernel still maps onto every entry of the list. -/
theorem two_generator_kernel {G Q : Type*} [Group G] [Group Q] (c : Q)
    (generate : ∀ q : Q, ∃ i : ℤ, c ^ i = q) (row : Q → G) (cover : Function.Surjective row) :
    ∃ f : FreeGroup Bool →* (G ≀ᵣ Q),
      (RegularWreathProduct.rightHom.comp f =
        FreeGroup.lift (fun b : Bool => if b then 1 else c)) ∧
      ∃ h : (RegularWreathProduct.rightHom.comp f.range.subtype).ker →* G,
        Function.Surjective h := by
  let base : G ≀ᵣ Q := ⟨row, 1⟩
  let labels : Bool → G ≀ᵣ Q := fun b => if b then base else RegularWreathProduct.inl c
  let f := FreeGroup.lift labels
  let π : f.range →* Q := RegularWreathProduct.rightHom.comp f.range.subtype
  let h : π.ker →* G := {
    toFun := fun v => v.val.val.left 1
    map_one' := rfl
    map_mul' := by
      intro a b
      change (a.val.val * b.val.val).left 1 = a.val.val.left 1 * b.val.val.left 1
      have ax : a.val.val.right = 1 := a.property
      simp [ax]
  }
  refine ⟨f, ?_, h, ?_⟩
  · apply FreeGroup.ext_hom
    intro b
    cases b <;> simp [f,labels,base]
  · intro g
    obtain ⟨q,hq⟩ := cover g
    obtain ⟨i,hi⟩ := generate q
    have shift : RegularWreathProduct.inl q ∈ f.range := by
      refine ⟨FreeGroup.of false ^ i, ?_⟩
      simp [f,labels,← hi]
    have base_mem : base ∈ f.range := ⟨FreeGroup.of true, by simp [f,labels]⟩
    let w := (RegularWreathProduct.inl q : G ≀ᵣ Q)⁻¹ * base * RegularWreathProduct.inl q
    have wmem : w ∈ f.range := f.range.mul_mem (f.range.mul_mem (f.range.inv_mem shift) base_mem) shift
    have trivial : (⟨w,wmem⟩ : f.range) ∈ π.ker := by
      change w.right = 1
      simp [w,base]
    refine ⟨⟨⟨w,wmem⟩,trivial⟩, ?_⟩
    change w.left 1 = g
    simpa [w,base] using hq

end GaloisMonodromy

end

section

namespace MarkedGalois
open IntermediateField Polynomial

/-- An extension of the exact degree containing an nth root of the rational parameter
is itself a rational function field, with the chosen root as parameter. -/
theorem rational_of_marked_root {C F : Type*} [Field C] [Field F]
    [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
    [FiniteDimensional (RatFunc C) F] {n : ℕ} (pos : 0 < n) (s : F)
    (marked : s ^ n = algebraMap (RatFunc C) F RatFunc.X)
    (degree : Module.finrank (RatFunc C) F = n) :
    ∃ e : RatFunc C ≃ₐ[C] F, e RatFunc.X = s := by
  let K := RatFunc C
  have irr : Irreducible ((X : Polynomial K)^n - Polynomial.C RatFunc.X) := by
    simpa [K] using InverseKummer.irreducible_shifted_binomial pos (0 : C)
  have root : aeval s ((X : Polynomial K)^n - Polynomial.C RatFunc.X) = 0 := by
    simp [K,marked]
  have minp := minpoly.eq_of_irreducible_of_monic irr root (monic_X_pow_sub_C _ pos.ne')
  have rank : Module.finrank K K⟮s⟯ = Module.finrank K F := by
    rw [adjoin.finrank (Algebra.IsIntegral.isIntegral s), ← minp, natDegree_X_pow_sub_C]
    exact degree.symm
  have gen : K⟮s⟯ = (⊤ : IntermediateField K F) := by
    apply IntermediateField.eq_of_le_of_finrank_le le_top
    exact (topEquiv (F := K) (E := F)).toLinearEquiv.finrank_eq.le.trans rank.ge
  let L := C⟮s⟯
  have hs : s ∈ L := mem_adjoin_simple_self C s
  let base := IsScalarTower.toAlgHom C K F
  have incl : (⊤ : IntermediateField C K) ≤ L.comap base := by
    rw [← RatFunc.adjoin_X,adjoin_le_iff,Set.singleton_subset_iff]
    change algebraMap K F RatFunc.X ∈ L
    rw [← marked]
    exact pow_mem hs n
  have allc (r : K) : algebraMap K F r ∈ L := incl (show r ∈ ⊤ from trivial)
  have full : L = ⊤ := by
    apply top_unique
    intro y _
    have hy : y ∈ K⟮s⟯ := gen ▸ trivial
    exact adjoin_induction K (p := fun z _ => z ∈ L)
      (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hs) allc
      (fun _ _ _ _ => L.add_mem) (fun _ _ => L.inv_mem)
      (fun _ _ _ _ => L.mul_mem) hy
  have trans : Transcendental C s := by
    intro alg
    have bad := alg.pow n
    rw [marked] at bad
    exact RatFunc.transcendental_X ((isAlgebraic_algebraMap_iff (algebraMap K F).injective).mp bad)
  let e := (RatFunc.algEquivOfTranscendental s trans).trans
    ((equivOfEq full).trans topEquiv)
  refine ⟨e,?_⟩
  exact RatFunc.algEquivOfTranscendental_X _ _

end MarkedGalois

namespace MarkedGalois
open IntermediateField InverseGalois

/-- A marked quotient of a finite Galois cover has rational fixed field. All
quotients of its kernel therefore occur as Galois groups over the rational field. -/
theorem realize_quotient_of_marked_kernel {C E : Type u} [Field C] [Field E]
    [Algebra (RatFunc C) E] [FiniteDimensional (RatFunc C) E] [IsGalois (RatFunc C) E]
    {H Q G : Type*} [Group H] [Group Q] [Finite Q] [Group G]
    (e : H ≃* (E ≃ₐ[RatFunc C] E)) (rot : H →* Q) (onto : Function.Surjective rot)
    (lift : ∃ s : fixedField (rot.ker.map e.toMonoidHom),
      s ^ Nat.card Q = algebraMap (RatFunc C) _ RatFunc.X)
    (q : rot.ker →* G) (ontoq : Function.Surjective q) : IsRealizable (RatFunc C) G := by
  let B := rot.ker.map e.toMonoidHom
  let F := fixedField B
  have degree : Module.finrank (RatFunc C) F = Nat.card Q := by
    calc
      _ = (fixedField B).fixingSubgroup.index :=
        finrank_eq_fixingSubgroup_index E (fixedField B)
      _ = B.index := congrArg Subgroup.index (fixingSubgroup_fixedField B)
      _ = rot.ker.index := Subgroup.index_map_equiv rot.ker e
      _ = _ := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective rot onto).toEquiv
  let : Algebra C F := ((algebraMap (RatFunc C) F).comp (algebraMap C (RatFunc C))).toAlgebra
  let : IsScalarTower C (RatFunc C) F := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨s,hs⟩ := lift
  obtain ⟨φ,_⟩ := rational_of_marked_root (C := C) (F := F) Nat.card_pos s hs degree
  let deck : rot.ker ≃* (E ≃ₐ[F] E) := (e.subgroupMap rot.ker).trans (subgroupEquivAlgEquiv B)
  let π := q.comp deck.symm.toMonoidHom
  have surj : Function.Surjective π := ontoq.comp deck.symm.surjective
  let := π.normal_ker
  exact ProjectiveGalois.realize_over_iso φ.toRingEquiv
    ((QuotientGroup.quotientKerEquivOfSurjective π surj).symm.trans (IsGalois.normalAutEquivQuotient π.ker))

end MarkedGalois

namespace MarkedGalois
open IntermediateField InverseGalois
universe u v

/-- A finite three-point regular-cover theorem with its cyclic quotient marked
implies unrestricted inverse Galois over the rational function field. The
two branch generators project respectively to a generator and to the identity. -/
theorem amplify_marked_cyclic_quotients {C : Type u} [Field C] {G : Type v}
    [Fintype G] [Group G]
    (comparison : ∀ (H : Type v) [Group H] [Finite H] (f : FreeGroup Bool →* H),
      Function.Surjective f → ∀ (n : ℕ) [NeZero n] (c : Multiplicative (ZMod n)),
      Function.Surjective (fun i : ℤ => c ^ i) → ∀ rot : H →* Multiplicative (ZMod n),
      rot.comp f = FreeGroup.lift (fun b : Bool => if b then 1 else c) →
      ∃ (E : Type u) (_ : Field E) (_ : Algebra (RatFunc C) E)
        (_ : FiniteDimensional (RatFunc C) E) (_ : IsGalois (RatFunc C) E)
        (e : H ≃* (E ≃ₐ[RatFunc C] E)), ∃ s : fixedField (rot.ker.map e.toMonoidHom),
          s ^ n = algebraMap (RatFunc C) _ RatFunc.X) :
    IsRealizable (RatFunc C) G := by
  classical
  let n := Fintype.card G
  let _ : NeZero n := ⟨Fintype.card_ne_zero⟩
  let Q := Multiplicative (ZMod n)
  let index : Q ≃ G := (Multiplicative.toAdd.trans (ZMod.finEquiv n).toEquiv.symm).trans
    (Fintype.equivFin G).symm
  obtain ⟨c,gen⟩ := exists_zpow_surjective Q
  obtain ⟨f,labels,q,ontoq⟩ := GaloisMonodromy.two_generator_kernel c gen index index.surjective
  let rot := RegularWreathProduct.rightHom.comp f.range.subtype
  have lab : rot.comp f.rangeRestrict = FreeGroup.lift (fun b : Bool => if b then 1 else c) := labels
  have onto : Function.Surjective rot := by
    intro z
    obtain ⟨k,hk⟩ := gen z
    refine ⟨f.rangeRestrict (FreeGroup.of false ^ k),?_⟩
    change (rot.comp f.rangeRestrict) _ = _
    rw [lab]
    simpa using hk
  obtain ⟨E,field,alg,fd,gal,e,s,hs⟩ :=
    comparison f.range f.rangeRestrict f.rangeRestrict_surjective n c gen rot lab
  apply realize_quotient_of_marked_kernel e rot onto _ q ontoq
  refine ⟨s,?_⟩
  have card : Nat.card Q = n := by
    change Nat.card (ZMod n) = n
    simp
  rwa [card]

end MarkedGalois

namespace MarkedGalois
open IntermediateField InverseGalois

/-- Only degree-zero-universe covering data are needed even for finite groups
presented in an arbitrary universe. -/
theorem amplify_small_marked_covers {G : Type*} [Fintype G] [Group G]
    (comparison : ∀ (H : Type) [Group H] [Finite H] (f : FreeGroup Bool →* H),
      Function.Surjective f → ∀ (n : ℕ) [NeZero n] (c : Multiplicative (ZMod n)),
      Function.Surjective (fun i : ℤ => c ^ i) → ∀ rot : H →* Multiplicative (ZMod n),
      rot.comp f = FreeGroup.lift (fun b : Bool => if b then 1 else c) →
      ∃ (E : Type) (_ : Field E) (_ : Algebra (RatFunc ℂ) E)
        (_ : FiniteDimensional (RatFunc ℂ) E) (_ : IsGalois (RatFunc ℂ) E)
        (e : H ≃* (E ≃ₐ[RatFunc ℂ] E)), ∃ s : fixedField (rot.ker.map e.toMonoidHom),
          s ^ n = algebraMap (RatFunc ℂ) _ RatFunc.X) :
    IsRealizable (RatFunc ℂ) G := by
  let num := (Fintype.equivFin G).symm
  let : Group (Fin (Fintype.card G)) := num.group
  let : Mul (Fin (Fintype.card G)) := num.mul
  have real := amplify_marked_cyclic_quotients (C := ℂ) (G := Fin (Fintype.card G)) comparison
  obtain ⟨R⟩ := real.exists_realization
  exact ⟨⟨{ R with iso := num.mulEquiv.symm.trans R.iso }⟩⟩

end MarkedGalois

end

section

namespace GaloisMonodromy

/-- Point-separating functions turn a faithful permutation action into a faithful action
on the function field. Pulling back along the inverse gives the covariant action. -/
theorem faithful_inverse_pullback {K L D X Y : Type*} [Field K] [Field L] [Algebra K L]
    [Group D] [MulAction D X] [FaithfulSMul D X] (ev : L → X → Y)
    (extL : Function.Injective ev)
    (sep : ∀ {x y : X}, x ≠ y → ∃ f : L, ev f x ≠ ev f y)
    (pull : D → (L ≃+* L))
    (values : ∀ d f x, ev (pull d f) x = ev f (d • x))
    (constant : ∀ (d : D) (r : K) x, ev (algebraMap K L r) (d • x) = ev (algebraMap K L r) x) :
    ∃ φ : D →* (L ≃ₐ[K] L), Function.Injective φ ∧
      ∀ d f x, ev (φ d f) x = ev f (d⁻¹ • x) := by
  let act (d : D) : L ≃ₐ[K] L := AlgEquiv.ofRingEquiv (f := pull d⁻¹) (fun r =>
    extL (funext fun x => (values _ _ _).trans (constant _ _ _)))
  have law (d : D) (f : L) (x : X) : ev (act d f) x = ev f (d⁻¹ • x) := values _ _ _
  let φ : D →* (L ≃ₐ[K] L) := {
    toFun := act
    map_one' := AlgEquiv.ext fun f => extL (funext fun x => by simp [law])
    map_mul' := fun g h => AlgEquiv.ext fun f => extL (funext fun x => by
      change ev (act (g * h) f) x = ev (act g (act h f)) x
      simp only [law,mul_inv_rev,mul_smul])
  }
  refine ⟨φ,?_,law⟩
  intro a b eqn
  apply inv_injective
  refine eq_of_smul_eq_smul (fun x : X => ?_)
  by_contra h
  obtain ⟨f,hf⟩ := sep h
  apply hf
  rw [← law, ← law]
  exact congrArg (fun σ : L ≃ₐ[K] L => ev (σ f) x) eqn

/-- A regular action of the full field degree accounts for all automorphisms
and proves that the extension is Galois. -/
theorem galois_of_full_degree_action {K L D : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Group D] (φ : D →* (L ≃ₐ[K] L)) (inj : Function.Injective φ)
    (degree : Nat.card D = Module.finrank K L) :
    IsGalois K L ∧ ∃ e : D ≃* (L ≃ₐ[K] L), ∀ d, e d = φ d := by
  have bound : Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L :=
    (Nat.card_congr (algEquivEquivAlgHom K L).toEquiv).le.trans (card_algHom_le_finrank K L L)
  have eq := bound.antisymm (degree ▸ Nat.card_le_card_of_injective φ inj)
  exact ⟨IsGalois.of_card_aut_eq_finrank K L eq, MulEquiv.ofBijective φ
    ((Nat.bijective_iff_injective_and_card φ).2 ⟨inj,degree.trans eq.symm⟩), fun _ => rfl⟩

/-- A function on the covering surface which descends along the rotation kernel
supplies the marked root in its fixed field. -/
theorem marked_cover_of_inverse_pullback {K L D Q X Y : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Group D] [Group Q]
    [MulAction D X] [FaithfulSMul D X] (ev : L → X → Y) (extL : Function.Injective ev)
    (sep : ∀ {x y : X}, x ≠ y → ∃ f : L, ev f x ≠ ev f y)
    (pull : D → (L ≃+* L))
    (values : ∀ d f x, ev (pull d f) x = ev f (d • x))
    (constant : ∀ (d : D) (r : K) x, ev (algebraMap K L r) (d • x) = ev (algebraMap K L r) x)
    (degree : Nat.card D = Module.finrank K L) (rot : D →* Q) (t : K) (n : ℕ) (s : L)
    (root : s ^ n = algebraMap K L t)
    (invariant : ∀ d ∈ rot.ker, ∀ x : X, ev s (d • x) = ev s x) :
    IsGalois K L ∧ ∃ e : D ≃* (L ≃ₐ[K] L),
      ∃ m : IntermediateField.fixedField (rot.ker.map e.toMonoidHom),
        m ^ n = algebraMap K _ t := by
  obtain ⟨φ,inj,law⟩ := faithful_inverse_pullback ev extL sep pull values constant
  obtain ⟨gal,e,he⟩ := galois_of_full_degree_action φ inj degree
  refine ⟨gal,e,⟨s,?_⟩,Subtype.ext root⟩
  intro σ
  obtain ⟨d,hd,heq⟩ := σ.property
  change σ.val s = s
  rw [← heq]
  change e d s = s
  rw [he]
  exact extL (funext fun x => (law d s x).trans (invariant d⁻¹ (rot.ker.inv_mem hd) x))

end GaloisMonodromy

end

section

namespace GaloisMonodromy
open Filter Topology

/-- A holomorphic branch of a root on a punctured disc extends meromorphically
across the puncture whenever its positive integral power does. -/
theorem meromorphicAt_of_pow {f : ℂ → ℂ} {x : ℂ} {n : ℕ} (hn : 0 < n)
    (regular : ∀ᶠ z in 𝓝[≠] x, DifferentiableAt ℂ f z)
    (power : MeromorphicAt (fun z => f z ^ n) x) : MeromorphicAt f x := by
  obtain ⟨m,hm⟩ := power
  let g (z : ℂ) := (z - x) ^ (m+1) * f z
  have clear : m ≤ (m+1)*n := by
    calc m ≤ m+1 := Nat.le_succ m
         _ = (m+1)*1 := (Nat.mul_one _).symm
         _ ≤ _ := Nat.mul_le_mul_left _ hn
  have eqf : (fun z => g z ^ n) =
      fun z => (z-x)^((m+1)*n-m) * ((z-x)^m * f z ^ n) := by
    funext z
    rw [← mul_assoc,← pow_add,Nat.sub_add_cancel clear]
    simp [g,mul_pow,pow_mul]
  have hp : ContinuousAt (fun z => g z ^ n) x := by
    rw [eqf]
    exact (((continuousAt_id.sub continuousAt_const).pow _).mul hm.continuousAt)
  have zero : g x = 0 := by simp [g]
  have cg : ContinuousAt g x := by
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ,hδ,h⟩ := Metric.continuousAt_iff.mp hp (ε^n) (pow_pos hε n)
    refine ⟨δ,hδ,fun {z} hz => ?_⟩
    rw [zero,dist_zero_right]
    apply lt_of_pow_lt_pow_left₀ n hε.le
    simpa only [zero,zero_pow hn.ne',dist_zero_right,norm_pow] using h hz
  refine ⟨m+1,?_⟩
  change AnalyticAt ℂ g x
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ cg
  filter_upwards [regular] with z hz
  exact (((differentiableAt_id.sub_const x).pow _).mul hz)

/-- Locally away from zero, continuity chooses a unique branch of the
power map, so differentiability of that power implies differentiability of the root. -/
theorem differentiableAt_of_continuous_pow {f : ℂ → ℂ} {x : ℂ} {n : ℕ} (hn : 0 < n)
    (hf : ContinuousAt f x) (hx : f x ≠ 0) (hp : DifferentiableAt ℂ (fun z => f z ^ n) x) :
    DifferentiableAt ℂ f x := by
  let P (z : ℂ) := z ^ n
  let a := (n : ℂ) * f x ^ (n-1)
  have deriv : HasStrictDerivAt P a (f x) := hasStrictDerivAt_pow n (f x)
  have nz : a ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') (pow_ne_zero _ hx)
  let I := deriv.localInverse P a (f x) nz
  have dif : DifferentiableAt ℂ I (P (f x)) := (deriv.to_localInverse nz).hasDerivAt.differentiableAt
  apply (dif.comp x hp).congr_of_eventuallyEq
  exact (hf.tendsto.eventually (deriv.eventually_left_inverse nz)).mono (fun _ h => h.symm)

/-- A continuous root of a meromorphic function on a punctured neighbourhood
is meromorphic at its centre. The root may have any point value at the centre. -/
theorem meromorphicAt_of_continuous_pow {f : ℂ → ℂ} {x : ℂ} {n : ℕ} (hn : 0 < n)
    (continuous : ∀ᶠ z in 𝓝[≠] x, ContinuousAt f z)
    (power : MeromorphicAt (fun z => f z ^ n) x) : MeromorphicAt f x := by
  rcases power.eventually_eq_zero_or_eventually_ne_zero with vanishes | nonzero
  · apply (MeromorphicAt.const (0 : ℂ) x).congr
    filter_upwards [vanishes] with z hz
    exact (eq_zero_of_pow_eq_zero hz).symm
  · apply meromorphicAt_of_pow hn _ power
    filter_upwards [continuous,nonzero,power.eventually_analyticAt] with z h hz analytic
    exact differentiableAt_of_continuous_pow hn h (fun eq => hz (by rw [eq,zero_pow hn.ne']))
      analytic.differentiableAt

end GaloisMonodromy

end

section

open Set Filter Function
open scoped Topology

namespace GaloisMeromorphic

theorem affine_divisor_finite {f : ℂ → ℂ} (hf : Meromorphic f)
    (hi : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    (MeromorphicOn.divisor f univ).support.Finite := by
  let g : ℂ → ℂ := f ∘ Inv.inv
  have hg : Meromorphic g := by
    intro w
    by_cases hw : w = 0
    · subst w
      exact hi
    · exact (hf w⁻¹).comp_analyticAt (analyticAt_inv hw)
  let D := MeromorphicOn.divisor f univ
  let E := MeromorphicOn.divisor g univ
  have zero_near : ∀ᶠ w in 𝓝[≠] (0 : ℂ), E w = 0 := by
    have eq := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp E.eq_zero_codiscreteWithin 0 (mem_univ _)
    simpa only [compl_univ, union_empty, Pi.zero_apply, Filter.Eventually] using eq
  have invord (w : ℂ) (hw : w ≠ 0) : E w = D w⁻¹ := by
    rw [show E w = _ from (meromorphicOn_univ.2 hg).divisor_apply (mem_univ w),
      show D w⁻¹ = _ from (meromorphicOn_univ.2 hf).divisor_apply (mem_univ w⁻¹)]
    exact congrArg WithTop.untop₀ (meromorphicOrderAt_comp_of_deriv_ne_zero (f := f)
      (analyticAt_inv hw) (by simpa [deriv_inv] using hw))
  have away : ∀ᶠ z in cocompact ℂ, D z = 0 := by
    have h : ∀ᶠ w in 𝓝[≠] (0 : ℂ), D w⁻¹ = 0 := by
      filter_upwards [zero_near, self_mem_nhdsWithin] with w h hw
      exact (invord w hw).symm.trans h
    rw [← Metric.cobounded_eq_cocompact]
    simpa only [inv_inv] using tendsto_inv₀_cobounded'.eventually h
  obtain ⟨K, hK, cover⟩ := mem_cocompact'.mp away
  exact (Function.locallyFinsupp.locallyFiniteSupport D |>.finite_inter_support_of_isCompact hK).subset
    fun z hz => ⟨cover hz, hz⟩

theorem zero_or_finite_orders {f : ℂ → ℂ} (hf : Meromorphic f) :
    f =ᶠ[codiscreteWithin (univ : Set ℂ)] (0 : ℂ → ℂ) ∨
      ∀ z : (univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤ := by
  by_cases h : ∃ z : (univ : Set ℂ), meromorphicOrderAt f z ≠ ⊤
  · exact Or.inr (((meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall
      isConnected_univ).mp h)
  · left
    apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.mpr
    intro z _
    have hz : meromorphicOrderAt f z = ⊤ := not_ne_iff.mp (fun hn => h ⟨⟨z, mem_univ _⟩, hn⟩)
    simpa only [compl_univ, union_empty, Pi.zero_apply, Filter.Eventually] using meromorphicOrderAt_eq_top_iff.mp hz

end GaloisMeromorphic

open Filter Set Function Bornology
open scoped Topology

namespace GaloisMeromorphic

/-- Meromorphy in the reciprocal coordinate implies ordinary continuity outside a compact set. -/
theorem exterior_continuity {f : ℂ → ℂ} (hi : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    ∀ᶠ z in cocompact ℂ, ContinuousAt f z := by
  rw [← Metric.cobounded_eq_cocompact]
  filter_upwards [(tendsto_inv₀_cobounded' (α := ℂ)).eventually hi.eventually_analyticAt,
    (Bornology.le_cofinite ℂ) (eventually_cofinite_ne (0 : ℂ))] with z hz hn
  simpa [Function.comp_def] using hz.continuousAt.comp (continuousAt_inv₀ hn)

/-- Agreement off a closed discrete subset extends to agreement off a finite subset when
both functions are continuous outside some compact set. -/
theorem cofinite_of_codiscrete {f g : ℂ → ℂ} (h : f =ᶠ[codiscreteWithin univ] g)
    (hf : ∀ᶠ z in cocompact ℂ, ContinuousAt f z) (hg : ∀ᶠ z in cocompact ℂ, ContinuousAt g z) :
    f =ᶠ[cofinite] g := by
  let E := {z | f z = g z}
  have he : E ∈ codiscreteWithin univ := h
  have exterior : E ∈ cocompact ℂ := by
    filter_upwards [hf, hg] with z h₁ h₂
    have atz : f =ᶠ[𝓝[≠] z] g := by
      change E ∈ 𝓝[≠] z
      simpa only [compl_univ, union_empty] using (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp he z (mem_univ z))
    exact tendsto_nhds_unique_of_eventuallyEq (h₁.tendsto.mono_left nhdsWithin_le_nhds)
      (h₂.tendsto.mono_left nhdsWithin_le_nhds) atz
  obtain ⟨K, hK, hKE⟩ := Filter.mem_cocompact.mp exterior
  have fin := hK.finite_sdiff_of_mem_codiscreteWithin (codiscreteWithin_mono (subset_univ K) he)
  change Eᶜ.Finite
  exact fin.subset (fun z hz => ⟨by by_contra hh; exact hz (hKE hh), hz⟩)

/-- The affine divisor product is also meromorphic in the reciprocal coordinate. -/
theorem factor_at_infinity {d : ℂ → ℤ} (hd : d.HasFiniteSupport) :
    MeromorphicAt (fun w : ℂ => (∏ᶠ u : ℂ, (· - u) ^ d u : ℂ → ℂ) w⁻¹) 0 := by
  classical
  have hs : (fun u : ℂ => ((· - u) ^ d u : ℂ → ℂ)).mulSupport ⊆ hd.toFinset := by
    rw [Function.FactorizedRational.mulSupport]
    exact fun a ha => hd.mem_toFinset.mpr ha
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  simp only [Finset.prod_apply, Pi.pow_apply]
  apply MeromorphicAt.fun_prod
  intro u hu
  fun_prop

end GaloisMeromorphic

open Filter Bornology
open scoped Topology

namespace GaloisMeromorphic

/-- A nowhere-zero entire function meromorphic in the chart at infinity is constant. -/
theorem entire_unit_constant {g : ℂ → ℂ} (hg : Differentiable ℂ g) (nz : ∀ z, g z ≠ 0)
    (hi : MeromorphicAt (fun w : ℂ => g w⁻¹) 0) : ∃ c : ℂ, ∀ z, g z = c := by
  by_cases h : 0 ≤ meromorphicOrderAt (fun w : ℂ => g w⁻¹) 0
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hi h
    have lim : Tendsto g (cocompact ℂ) (𝓝 c) := by
      simpa [Function.comp_def, Metric.cobounded_eq_cocompact] using
        hc.comp (tendsto_inv₀_cobounded' (α := ℂ))
    exact ⟨c, fun z => hg.apply_eq_of_tendsto_cocompact z lim⟩
  · have pole := tendsto_cobounded_of_meromorphicOrderAt_neg (lt_of_not_ge h)
    have lim : Tendsto (fun z => (g z)⁻¹) (cocompact ℂ) (𝓝 0) := by
      simpa [Function.comp_def, Metric.cobounded_eq_cocompact] using
        (tendsto_inv₀_cobounded (α := ℂ)).comp (pole.comp (tendsto_inv₀_cobounded' (α := ℂ)))
    have dinv : Differentiable ℂ (fun z => (g z)⁻¹) := hg.inv nz
    exact False.elim ((inv_ne_zero (nz 0)) (dinv.apply_eq_of_tendsto_cocompact 0 lim))

end GaloisMeromorphic

namespace GaloisMeromorphic
open Polynomial Filter

/-- A finite factorized divisor is a polynomial quotient under the usual
pointwise convention for division at zero. -/
theorem factor_quotient (d : ℂ → ℤ) (hd : d.HasFiniteSupport) (c : ℂ) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ ∀ z : ℂ,
      c * ((∏ᶠ a : ℂ, (· - a) ^ d a) : ℂ → ℂ) z = P.eval z / Q.eval z := by
  classical
  let s := hd.toFinset
  let P := C c * ∏ a∈s, (X-C a)^(d a).toNat
  let Q := ∏ a∈s, (X-C a)^(-d a).toNat
  have split (x : ℂ) (i : ℤ) : x^i=x^i.toNat / x^(-i).toNat := by
    cases i with
    | ofNat k => simp
    | negSucc k => simp [zpow_negSucc]
  refine ⟨P,Q,Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _ (X_sub_C_ne_zero a)),?_⟩
  intro z
  have few : (fun a : ℂ => ((· - a) ^ d a : ℂ → ℂ)).mulSupport ⊆ ↑s := by
    rw [Function.FactorizedRational.mulSupport]
    intro a ha
    exact hd.mem_toFinset.mpr ha
  rw [finprod_eq_prod_of_mulSupport_subset _ few,Finset.prod_apply]
  simp only [P,Q,eval_mul,eval_C,eval_prod,eval_pow,eval_sub,eval_X,Pi.pow_apply]
  simp_rw [split (z-_) (d _)]
  rw [Finset.prod_div_distrib,mul_div_assoc]

/-- A quotient of polynomial evaluations agrees with one rational-function
evaluation away from the finitely many roots of its denominators. -/
theorem quotient_ratfunc (P Q : Polynomial ℂ) (hq : Q≠0) :
    ∃ r : RatFunc ℂ, ∀ᶠ z : ℂ in cofinite, P.eval z/Q.eval z=RatFunc.eval (RingHom.id ℂ) z r := by
  let r : RatFunc ℂ := algebraMap (Polynomial ℂ) _ P / algebraMap (Polynomial ℂ) _ Q
  have eq : r.num*Q=P*r.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).2 rfl
  have nonzeros (p : Polynomial ℂ) (p0 : p≠0) : ∀ᶠ z : ℂ in cofinite, p.eval z≠0 := by
    exact (p.finite_setOfPred_isRoot p0).compl_mem_cofinite
  refine ⟨r,?_⟩
  filter_upwards [nonzeros Q hq, nonzeros r.denom r.denom_ne_zero] with z Qz Dz
  have eqz := congrArg (fun p : Polynomial ℂ => p.eval z) eq
  simp only [eval_mul] at eqz
  change P.eval z / Q.eval z=r.num.eval z/r.denom.eval z
  exact (div_eq_div_iff Qz Dz).2 eqz.symm

end GaloisMeromorphic

open Filter Set Function Bornology
open scoped Topology

namespace GaloisMeromorphic

/-- A meromorphic function on the sphere, presented in its two affine coordinates,
agrees outside finitely many points with the quotient of two polynomials. -/
theorem sphere_polynomial_quotient {f : ℂ → ℂ} (hf : Meromorphic f)
    (hi : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧ f =ᶠ[cofinite] fun z => P.eval z / Q.eval z := by
  rcases zero_or_finite_orders hf with zero | finite
  · refine ⟨0, 1, one_ne_zero, ?_⟩
    have h := cofinite_of_codiscrete zero (exterior_continuity hi) (.of_forall fun _ => continuousAt_const)
    filter_upwards [h] with z hz
    simpa using hz
  let d := MeromorphicOn.divisor f univ
  let φ : ℂ → ℂ := ∏ᶠ u : ℂ, (· - u) ^ d u
  have hd : d.support.Finite := affine_divisor_finite hf hi
  obtain ⟨g, analytic, unit, eq⟩ := (meromorphicOn_univ.mpr hf).extract_zeros_poles finite hd
  have diff : Differentiable ℂ g := fun z => (analytic z (mem_univ z)).differentiableAt
  have extφ := exterior_continuity (factor_at_infinity (d := d) hd)
  have equality : f =ᶠ[cofinite] fun z => φ z * g z := by
    exact cofinite_of_codiscrete eq (exterior_continuity hi)
      (extφ.mono fun z hz => hz.mul (diff.continuous.continuousAt))
  have off : ∀ᶠ z in cofinite, z ∉ d.support := hd.compl_mem_cofinite
  have nzφ : ∀ᶠ z in cofinite, φ z ≠ 0 := off.mono (fun z hz =>
    Function.FactorizedRational.ne_zero (not_ne_iff.mp hz))
  have eqdiv : (fun z => f z / φ z) =ᶠ[cofinite] g := by
    filter_upwards [equality, nzφ] with z hz hn
    simp [hz, hn]
  have gi : MeromorphicAt (fun w : ℂ => g w⁻¹) 0 :=
    (hi.div (factor_at_infinity (d := d) hd)).congr
      (eqdiv.comp_tendsto (tendsto_inv₀_nhdsNE_zero.mono_right (Bornology.le_cofinite ℂ)))
  obtain ⟨c, hc⟩ := entire_unit_constant diff (fun z => unit ⟨z, mem_univ z⟩) gi
  obtain ⟨P, Q, hQ, eval⟩ := factor_quotient d hd c
  refine ⟨P, Q, hQ, equality.trans (.of_forall fun z => ?_)⟩
  change φ z * g z = P.eval z / Q.eval z
  rw [hc, mul_comm]
  exact eval z

/-- In rational function field notation, every meromorphic function on the sphere has a
representative in `ℂ(t)`. -/
theorem sphere_rational {f : ℂ → ℂ} (hf : Meromorphic f)
    (hi : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    ∃ r : RatFunc ℂ, f =ᶠ[cofinite] fun z => RatFunc.eval (RingHom.id ℂ) z r := by
  obtain ⟨P,Q,hQ,h⟩ := sphere_polynomial_quotient hf hi
  obtain ⟨r,hr⟩ := quotient_ratfunc P Q hQ
  exact ⟨r, h.trans hr⟩

end GaloisMeromorphic

namespace GaloisMeromorphic
open Filter Polynomial

/-- Over an infinite field, agreement of rational functions outside finitely many
points determines equality in the rational function field. -/
theorem ratfunc_eq_of_cofinite_eval {K : Type*} [Field K] [Infinite K] {r s : RatFunc K}
    (h : (fun z => RatFunc.eval (RingHom.id K) z r) =ᶠ[cofinite]
      (fun z => RatFunc.eval (RingHom.id K) z s)) : r = s := by
  let p := r.num * s.denom - s.num * r.denom
  have nonzeros (q : Polynomial K) (hq : q ≠ 0) : ∀ᶠ z : K in cofinite, q.eval z ≠ 0 :=
    (q.finite_setOfPred_isRoot hq).compl_mem_cofinite
  have zero : p = 0 := by
    by_contra hp
    obtain ⟨z, good⟩ := (nonzeros p hp |>.and ((nonzeros r.denom r.denom_ne_zero).and
      ((nonzeros s.denom s.denom_ne_zero).and h))).exists
    rcases good with ⟨np, nr, ns, e⟩
    change r.num.eval z / r.denom.eval z = s.num.eval z / s.denom.eval z at e
    apply np
    simpa only [p, eval_sub, eval_mul, sub_eq_zero] using (div_eq_div_iff nr ns).mp e
  exact ((RatFunc.num_mul_eq_mul_denom_iff s.denom_ne_zero).mp (sub_eq_zero.mp zero)).trans
    (RatFunc.num_div_denom s)

end GaloisMeromorphic

namespace GaloisMeromorphic
open Filter

/-- The spherical meromorphic germ determines a unique rational function. -/
theorem sphere_rational_unique {f : ℂ → ℂ} (hf : Meromorphic f)
    (hi : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    ∃! r : RatFunc ℂ, f =ᶠ[cofinite] fun z => RatFunc.eval (RingHom.id ℂ) z r := by
  obtain ⟨r, hr⟩ := sphere_rational hf hi
  exact ⟨r, hr, fun _ hs => ratfunc_eq_of_cofinite_eval (hs.symm.trans hr)⟩

end GaloisMeromorphic

open Filter Set Polynomial
open scoped Topology

namespace GaloisMeromorphic

/-- Polynomial evaluations preserve meromorphic germs, including at poles. -/
theorem polynomial_meromorphic {f : ℂ → ℂ} {z : ℂ} (h : MeromorphicAt f z) (P : Polynomial ℂ) :
    MeromorphicAt (fun w => P.eval (f w)) z := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using hp.fun_add hq
  | monomial n c => simpa only [Polynomial.eval_monomial] using
      (MeromorphicAt.const c z).fun_mul (h.fun_pow n)

/-- The function field of the Riemann sphere in the two standard coordinates.
Meromorphic functions represent a unique rational function modulo cofinite equality,
and any such representative is meromorphic. -/
theorem sphere_meromorphic_iff {f : ℂ → ℂ} :
    Meromorphic f ∧ MeromorphicAt (fun w : ℂ => f w⁻¹) 0 ↔
      ∃! r : RatFunc ℂ, f =ᶠ[cofinite] fun z => RatFunc.eval (RingHom.id ℂ) z r := by
  constructor
  · rintro ⟨hf, hi⟩
    obtain ⟨r, hr⟩ := sphere_rational hf hi
    exact ⟨r, hr, fun s hs => ratfunc_eq_of_cofinite_eval (hs.symm.trans hr)⟩
  · rintro ⟨r, hr, _⟩
    have mer {g : ℂ → ℂ} {w : ℂ} (hg : MeromorphicAt g w) :
        MeromorphicAt (fun x => RatFunc.eval (RingHom.id ℂ) (g x) r) w :=
      (polynomial_meromorphic hg r.num).fun_div (polynomial_meromorphic hg r.denom)
    constructor
    · intro z
      exact (mer (MeromorphicAt.id z)).congr (hr.symm.filter_mono (nhdsNE_le_cofinite z))
    · exact (mer ((MeromorphicAt.id (0 : ℂ)).inv)).congr (hr.symm.comp_tendsto
        (tendsto_inv₀_nhdsNE_zero.mono_right (Bornology.le_cofinite ℂ)))

end GaloisMeromorphic

end

section

namespace OMA.R_InverseGalois_inverse_galois_problem_variants_complex_rational_functions_R1

/-- Topological monodromy on the plane with n punctures. The slit-chart
construction above proves this step for every n. -/
def H1 : Prop :=
  ∀ n : ℕ,
    let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val + 1 : ℕ) : ℂ)}
    let b : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
    ∃ f : FundamentalGroup U b →* FreeGroup (Fin n), Function.Surjective f

/-- Finite-quotient form of Riemann existence at the generic point of the
punctured line. Kummer theory and faithful actions on the rational function
field already settle the abelian and projective quotients. -/
def H2 : Prop :=
  ∀ n : ℕ,
    let U := {z : ℂ // ∀ i : Fin n, z ≠ ((i.val + 1 : ℕ) : ℂ)}
    let b : U := ⟨0, fun i h => Nat.succ_ne_zero i.val (by exact_mod_cast h.symm)⟩
    let P := FundamentalGroup U b
    ∀ (N : Subgroup P) [N.Normal] [N.FiniteIndex],
      (¬ ∀ a b : P ⧸ N, a * b = b * a) →
      (¬ ∃ act : (P ⧸ N) →* (RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ), Function.Injective act) →
      ∃ f : Field.absoluteGaloisGroup (RatFunc ℂ) →* (P ⧸ N),
        Function.Surjective f ∧ IsClosed (f.ker : Set (Field.absoluteGaloisGroup (RatFunc ℂ)))

theorem topological_monodromy : H1 := PlaneClutch.integral_punctures

theorem main : H1 → H2 → type_of% @InverseGalois.inverse_galois_problem.variants.complex_rational_functions := by
  classical
  intro top geometric G fi grp
  obtain ⟨f, hf⟩ := top (Fintype.card G)
  let e : Fin (Fintype.card G) ≃ G := (Fintype.equivFin G).symm
  let h := (FreeGroup.lift (e : Fin (Fintype.card G) → G)).comp f
  have onto : Function.Surjective h :=
    (FreeGroup.lift_surjective_of_surjective e.surjective).comp hf
  let D := _ ⧸ h.ker
  let equiv : D ≃* G := QuotientGroup.quotientKerEquivOfSurjective h onto
  let : Fintype D := Fintype.ofEquiv G equiv.symm.toEquiv
  have result : InverseGalois.IsRealizable (RatFunc ℂ) D := by
    by_cases comm : ∀ a b : D, a * b = b * a
    · let group : Group D := inferInstance
      let : CommGroup D := { group with mul_comm := comm }
      exact InverseKummer.abelian_realizable_closed ℂ D
    by_cases proj : ∃ act : D →* (RatFunc ℂ ≃ₐ[ℂ] RatFunc ℂ), Function.Injective act
    · obtain ⟨act, faithful⟩ := proj
      exact ProjectiveGalois.realize_of_faithful_action act faithful
    obtain ⟨φ, surj, closed⟩ := geometric (Fintype.card G) h.ker comm proj
    exact InverseGalois.realizable_of_closed_quotient (K := RatFunc ℂ)
      (L := AlgebraicClosure (RatFunc ℂ)) φ surj closed
  obtain ⟨⟨r⟩⟩ := result
  exact ⟨⟨{ r with iso := equiv.symm.trans r.iso }⟩⟩

end OMA.R_InverseGalois_inverse_galois_problem_variants_complex_rational_functions_R1

end
