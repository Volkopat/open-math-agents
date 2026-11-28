import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R2
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Ext
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Function.Iterate
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Iterate
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-
The estimate below is the binary case of the generator-rank localization
in Su and Xia, Almost all finite groups are 2-groups of class two,
Proposition 3.5 (arXiv:2610.11092v1).

We count isomorphism classes of groups of order 2^m whose generator rank d
is outside the window in H4. A group contributes a normal subgroup generated
by lifts of a smallest commutator-spanning subspace of its ordinary
class-two quotient. Encoding the quotient and then the extension gives a
uniform bound for each triple (d, b, σ), where b is the dimension of the
commutator space and σ is the dimension of that subspace. Outside the
specified window the maximum of the resulting cubic exponent is strictly
smaller than 2/27. Summing over triples gives the required estimate even
before the condition on K is imposed.
-/

/- Erdos1160Tables -/
section
namespace Erdos1160.Tables
open CategoryTheory
def orderClasses (n : ℕ) : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  Quotient.mk _ '' {G : FiniteGrp.{0} | Nat.card G = n}
def GroupTable (n : ℕ) :=
  { t : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = t }
instance {n : ℕ} : Finite (GroupTable n) := by
  unfold GroupTable
  infer_instance
noncomputable abbrev model {n : ℕ} (t : GroupTable n) : FiniteGrp.{0} :=
  @FiniteGrp.of (Fin n) t.property.choose inferInstance
def product (G : FiniteGrp) (a b : G) : G := a * b
theorem model_mul {n : ℕ} (t : GroupTable n) (a b : Fin n) :
    product (model t) a b = t.val a b :=
  congrFun (congrFun t.property.choose_spec a) b
noncomputable def groupClass {n : ℕ} (t : GroupTable n) :
    Quotient (isIsomorphicSetoid FiniteGrp.{0}) :=
  Quotient.mk _ (model t)
theorem iso_of_mul_equiv {G H : FiniteGrp} (e : G ≃ H)
    (h : ∀ a b, e (product G a b) = product H (e a) (e b)) : Nonempty (G ≅ H) := by
  let f : G ≃* H := { e with map_mul' := h }
  exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩
theorem range_groupClass (n : ℕ) : Set.range (@groupClass n) = orderClasses n := by
  ext c
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨model t, Nat.card_fin n, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : GroupTable n := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    apply iso_of_mul_equiv e
    intro a b
    exact (congrArg (fun z => e z) (model_mul t a b)).trans (e.apply_symm_apply (e a * e b))
theorem orderClasses_finite (n : ℕ) : (orderClasses n).Finite := by
  rw [← range_groupClass]
  exact Set.finite_range _
end Erdos1160.Tables
end

/- LiftPresentations -/
section
namespace Erdos1160.CentralLifts
open scoped commutatorElement
variable {I J : Type} {p : ℕ}
abbrev Grp (R : J → FreeGroup I) := PresentedGroup (Set.range R)
def newRel (R : J → FreeGroup I) (c : J → Fin p) : Unit ⊕ (I ⊕ J) → FreeGroup (Option I)
  | .inl _ => FreeGroup.of none ^ p
  | .inr (.inl i) => ⁅FreeGroup.of (none : Option I), FreeGroup.of (some i)⁆
  | .inr (.inr j) => FreeGroup.map some (R j) * (FreeGroup.of none ^ (c j).val)⁻¹
abbrev Lift (R : J → FreeGroup I) (c : J → Fin p) := Grp (newRel R c)
def z (R : J → FreeGroup I) (c : J → Fin p) : Lift R c := PresentedGroup.of none
def old (R : J → FreeGroup I) (c : J → Fin p) (i : I) : Lift R c := PresentedGroup.of (some i)
theorem relation {A B : Type} (S : B → FreeGroup A) (j : B) :
    PresentedGroup.mk (Set.range S) (S j) = 1 :=
  PresentedGroup.one_of_mem ⟨j,rfl⟩
theorem z_pow (R : J → FreeGroup I) (c : J → Fin p) : z R c ^ p = 1 := by
  simpa only [newRel, map_pow, z, PresentedGroup.of] using relation (newRel R c) (.inl ())
theorem z_commutes_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    Commute (z R c) (old R c i) := by
  apply commutatorElement_eq_one_iff_commute.mp
  simpa only [newRel, map_commutatorElement, z, old, PresentedGroup.of] using
    relation (newRel R c) (.inr (.inl i))
theorem z_central (R : J → FreeGroup I) (c : J → Fin p) :
    z R c ∈ Subgroup.center (Lift R c) := by
  rw [Subgroup.center_eq_iInf (PresentedGroup.closure_range_of (Set.range (newRel R c)))]
  simp only [Subgroup.mem_iInf, Subgroup.mem_centralizer_singleton_iff]
  rintro _ ⟨_ | i,rfl⟩
  · rfl
  · exact (z_commutes_old R c i).eq
instance z_normal (R : J → FreeGroup I) (c : J → Fin p) :
    (Subgroup.zpowers (z R c)).Normal where
  conj_mem n hn g := by
    have hcenter : n ∈ Subgroup.center (Lift R c) := (Subgroup.zpowers_le.mpr (z_central R c)) hn
    have hc := Subgroup.mem_center_iff.mp hcenter g
    rwa [hc, mul_inv_cancel_right]
def inc (R : J → FreeGroup I) (c : J → Fin p) : FreeGroup I →* Lift R c :=
  (PresentedGroup.mk (Set.range (newRel R c))).comp (FreeGroup.map some)
theorem inc_rel (R : J → FreeGroup I) (c : J → Fin p) (j : J) :
    inc R c (R j) = z R c ^ (c j).val := by
  apply eq_of_mul_inv_eq_one
  simpa only [newRel, map_mul, map_inv, map_pow, inc, MonoidHom.comp_apply, z, PresentedGroup.of]
    using relation (newRel R c) (.inr (.inr j))
def quotientMap (R : J → FreeGroup I) (c : J → Fin p) :
    Grp R →* (Lift R c ⧸ Subgroup.zpowers (z R c)) :=
  QuotientGroup.lift _ ((QuotientGroup.mk' _).comp (inc R c)) (by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    change (QuotientGroup.mk' _) (inc R c (R j)) = 1
    rw [inc_rel, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
theorem quotientMap_old (R : J → FreeGroup I) (c : J → Fin p) (i : I) :
    quotientMap R c (PresentedGroup.of i) = (QuotientGroup.mk' _) (old R c i) := by rfl
theorem quotientMap_surjective (R : J → FreeGroup I) (c : J → Fin p) :
    Function.Surjective (quotientMap R c) := by
  intro y
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers (z R c)) y
  change (QuotientGroup.mk' _) x ∈ (quotientMap R c).range
  have h : (quotientMap R c).range.comap (QuotientGroup.mk' (Subgroup.zpowers (z R c))) = ⊤ := by
    apply top_unique
    rw [← PresentedGroup.closure_range_of (Set.range (newRel R c))]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨_ | i,rfl⟩
    · change (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) ∈ (quotientMap R c).range
      have hz : (QuotientGroup.mk' (Subgroup.zpowers (z R c))) (z R c) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)
      rw [hz]
      exact Subgroup.one_mem _
    · exact ⟨PresentedGroup.of i,quotientMap_old R c i⟩
  exact (show x ∈ (quotientMap R c).range.comap (QuotientGroup.mk' _) by rw [h]; trivial)
end Erdos1160.CentralLifts
end

/- RealizeLift -/
section
namespace Erdos1160.CentralLifts
open scoped commutatorElement
variable {I J : Type} {p : ℕ}
theorem normal_zpowers_of_central {G : Type} [Group G] (u : G) (hz : u ∈ Subgroup.center G) :
    (Subgroup.zpowers u).Normal where
  conj_mem n hn g := by
    have hc := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz) hn) g
    rwa [hc,mul_inv_cancel_right]
theorem card_quotient_prime {G : Type} [Group G] {u : G}
    [_n : (Subgroup.zpowers u).Normal] {p k : ℕ} (hp : 0 < p)
    (ho : orderOf u = p) (h : Nat.card G = p^(k+1)) :
    Nat.card (G ⧸ Subgroup.zpowers u) = p^k := by
  apply Nat.mul_left_cancel hp
  calc
    p * Nat.card (G ⧸ Subgroup.zpowers u) = Nat.card (Subgroup.zpowers u) * (Subgroup.zpowers u).index := by
      rw [Nat.card_zpowers, ho, Subgroup.index_eq_card]
    _ = Nat.card G := Subgroup.card_mul_index _
    _ = p*p^k := by rw [h, pow_succ, mul_comm]
end Erdos1160.CentralLifts
end

/- QuotientFiber -/
section
namespace Erdos1160.CentralLifts
open CategoryTheory
variable {p m : ℕ} {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q]
theorem central_prime_in_normal (hp : p.Prime) (hG : IsPGroup p G)
    (N : Subgroup G) [N.Normal] (hd : p ∣ Nat.card N) :
    ∃ u : G, u ∈ N ∧ u ∈ Subgroup.center G ∧ orderOf u = p := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hp' := hG.of_equiv ConjAct.toConjAct
  have hone : (1 : N) ∈ MulAction.fixedPoints (ConjAct G) N := fun _ => smul_one _
  obtain ⟨b,hb,hb1⟩ := hp'.exists_fixed_point_of_prime_dvd_card_of_fixed_point N hd hone
  let C := N ⊓ Subgroup.center G
  have hc : (b : G) ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro g
    have h := congrArg ((↑) : N → G) (hb (ConjAct.toConjAct g))
    change g * (b:G) * g⁻¹ = b at h
    exact mul_inv_eq_iff_eq_mul.mp h
  have hn : Nontrivial C := (Subgroup.nontrivial_iff_exists_ne_one C).mpr
    ⟨b,⟨b.property,hc⟩,fun e => hb1 (Subtype.ext e.symm)⟩
  obtain ⟨k,hk,hC⟩ := (hG.to_subgroup C).nontrivial_iff_card.mp hn
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := C) p (hC ▸ dvd_pow_self _ (Nat.ne_of_gt hk))
  exact ⟨u,u.property.1,u.property.2,(Subgroup.orderOf_coe u).trans hu⟩
omit [Finite G] [Finite Q] in
theorem ker_card_of_epi (hp : p.Prime) {e : ℕ} (hG : Nat.card G = p^(m+e))
    (hQ : Nat.card Q = p^m) (f : G →* Q) (hf : Function.Surjective f) :
    Nat.card f.ker = p^e := by
  apply Nat.mul_left_cancel (n := p^m) (pow_pos hp.pos _)
  calc
    p^m * Nat.card f.ker = f.ker.index * Nat.card f.ker := by
      rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f hf]
      simp [hQ]
    _ = Nat.card G := f.ker.index_mul_card
    _ = p^m * p^e := hG.trans (pow_add _ _ _)
end Erdos1160.CentralLifts
end

/- CollapseLift -/
section
namespace Erdos1160.CentralLifts
variable {I J : Type} {p : ℕ}
def substitute (w : FreeGroup I) : FreeGroup (Option I) →* FreeGroup I :=
  FreeGroup.lift (fun o => o.elim w FreeGroup.of)
def reducedRel (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Unit ⊕ (I ⊕ J) → FreeGroup I := fun r => substitute w (newRel R c r)
def contract (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Lift R c →* Grp (reducedRel R c w) :=
  PresentedGroup.map (substitute w) (by rintro _ ⟨r,rfl⟩; exact ⟨r,rfl⟩)
lemma contract_mk (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) (a : FreeGroup (Option I)) :
    contract R c w (PresentedGroup.mk _ a) = PresentedGroup.mk _ (substitute w a) := rfl
lemma contract_surj (R : J → FreeGroup I) (c : J → Fin p) (w : FreeGroup I) :
    Function.Surjective (contract R c w) := by
  have hinv : (substitute w).comp (FreeGroup.map some) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ (fun i => by simp [substitute])
  intro x
  obtain ⟨a,rfl⟩ := PresentedGroup.mk_surjective _ x
  refine ⟨PresentedGroup.mk _ (FreeGroup.map some a),?_⟩
  rw [contract_mk]
  exact congrArg (PresentedGroup.mk _) (DFunLike.congr_fun hinv a)
end Erdos1160.CentralLifts
end

/- TrimRelators -/
section
namespace Erdos1160.CentralLifts.Survival
abbrev Twist (r : ℕ) := {c : Fin r → Fin 2 // c ≠ 0}
theorem card_twist (r : ℕ) : Nat.card (Twist r) = 2^r-1 := by
  classical
  change Nat.card {c : Fin r → Fin 2 // ¬ c=0} = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp
theorem exists_one {r : ℕ} (c : Twist r) : ∃ j, (c.val j).val=1 := by
  by_contra! h
  apply c.property
  funext j
  apply Fin.ext
  change (c.val j).val=0
  have := h j
  have := (c.val j).isLt
  omega
noncomputable def pivot {r : ℕ} (c : Twist r) : Fin r := (exists_one c).choose
theorem pivot_eq {r : ℕ} (c : Twist r) : (c.val (pivot c)).val = 1 := (exists_one c).choose_spec
abbrev Kept (d : ℕ) {r : ℕ} (c : Twist r) := Unit ⊕ (Fin d ⊕ {j : Fin r // j ≠ pivot c})
theorem kept_card (d : ℕ) {r : ℕ} (c : Twist r) : Fintype.card (Kept d c) = r+d := by
  classical
  have h := (pivot c).isLt
  change Fintype.card (Unit ⊕ (Fin d ⊕ {j : Fin r // ¬j=pivot c}))=_
  rw [Fintype.card_sum,Fintype.card_sum,Fintype.card_subtype_compl]
  simp only [Fintype.card_unit,Fintype.card_fin,Fintype.card_subtype_eq]
  omega
def intoFull {d r : ℕ} (c : Twist r) : Kept d c → Unit ⊕ (Fin d ⊕ Fin r)
  | .inl u => .inl u
  | .inr (.inl i) => .inr (.inl i)
  | .inr (.inr j) => .inr (.inr j.val)
noncomputable def shortRel {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Fin (r+d) → FreeGroup (Fin d) := fun j =>
  reducedRel R c.val (R (pivot c)) (intoFull c ((Fintype.equivFinOfCardEq (kept_card d c)).symm j))
theorem pivot_relation {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    reducedRel R c.val (R (pivot c)) (.inr (.inr (pivot c))) = 1 := by
  have h : (substitute (R (pivot c))).comp (FreeGroup.map some) = MonoidHom.id _ :=
    FreeGroup.ext_hom _ _ (fun i => by simp [substitute])
  have inc (w : FreeGroup (Fin d)) : substitute (R (pivot c)) (FreeGroup.map some w)=w :=
    DFunLike.congr_fun h w
  simp only [reducedRel,newRel,pivot_eq,pow_one,map_mul,map_inv,inc]
  simp [substitute]
theorem closure_short {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Subgroup.normalClosure (Set.range (reducedRel R c.val (R (pivot c)))) =
      Subgroup.normalClosure (Set.range (shortRel R c)) := by
  let e := Fintype.equivFinOfCardEq (kept_card d c)
  have mem (j : Kept d c) : reducedRel R c.val (R (pivot c)) (intoFull c j) ∈
      Subgroup.normalClosure (Set.range (shortRel R c)) := by
    apply Subgroup.subset_normalClosure
    exact ⟨e j,by simp [shortRel,e]⟩
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    rcases j with u | (i | j)
    · exact mem (.inl u)
    · exact mem (.inr (.inl i))
    · by_cases he : j=pivot c
      · subst j; rw [pivot_relation]; exact Subgroup.one_mem _
      · exact mem (.inr (.inr ⟨j,he⟩))
  · apply Subgroup.normalClosure_mono
    rintro _ ⟨j,rfl⟩
    exact ⟨_,rfl⟩
noncomputable def shortIso {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Grp (reducedRel R c.val (R (pivot c))) ≃* Grp (shortRel R c) :=
  QuotientGroup.quotientMulEquivOfEq (closure_short R c)
noncomputable def contractShort {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Lift R c.val →* Grp (shortRel R c) := (shortIso R c).toMonoidHom.comp (contract R c.val (R (pivot c)))
theorem contractShort_surj {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) (c : Twist r) :
    Function.Surjective (contractShort R c) := (shortIso R c).surjective.comp (contract_surj R c.val (R (pivot c)))
end Erdos1160.CentralLifts.Survival
end

/- ScalarChild -/
section
namespace Erdos1160.CentralLifts.Survival
open scoped commutatorElement
variable {G H : Type} [Group G] [Group H] [Finite G] [Finite H] {d r : ℕ}
omit [Finite H] in
theorem onto_lifts {F : Type} [Group F] (q : G →* H) (hΦ : q.ker ≤ frattini G)
    (x : F →* G) (h : Function.Surjective (q.comp x)) : Function.Surjective x := by
  apply MonoidHom.range_eq_top.mp
  apply frattini_nongenerating
  apply top_unique
  intro g _
  obtain ⟨w,hw⟩ := h (q g)
  have hd : g*(x w)⁻¹ ∈ q.ker := by
    change q (g*(x w)⁻¹)=1
    rw [map_mul,map_inv,←show q (x w) = q g from hw,mul_inv_cancel]
  have h' := (x.range ⊔ frattini G).mul_mem (show g*(x w)⁻¹ ∈ x.range ⊔ frattini G from (show frattini G ≤ x.range ⊔ frattini G from le_sup_right) (hΦ hd))
    (show x w ∈ x.range ⊔ frattini G from (show x.range ≤ x.range ⊔ frattini G from le_sup_left) ⟨w,rfl⟩)
  simpa using h'
omit [Finite H] in



theorem child_cover_of_no_epi (R : Fin r → FreeGroup (Fin d)) (g : Grp R →* H)
    (hg : Function.Surjective g) (no_epi : ∀v : Grp R →* G,¬Function.Surjective v)
    (q : G →* H) (hq : Function.Surjective q) (hΦ : q.ker ≤ frattini G)
    (u : G) (ho : orderOf u=2) (hz : u ∈ Subgroup.center G) (hker : q.ker = Subgroup.zpowers u) :
    ∃ c : Twist r, ∃ v : Grp (shortRel R c) →* G, Function.Surjective v := by
  classical
  choose x hx using (fun i : Fin d => hq (g (PresentedGroup.of i)))
  let X := FreeGroup.lift x
  have hcomp : q.comp X = g.comp (PresentedGroup.mk (Set.range R)) :=
    FreeGroup.ext_hom _ _ (fun i => by simpa [X,PresentedGroup.of] using hx i)
  have hX : Function.Surjective X := onto_lifts q hΦ X (hcomp ▸ hg.comp (PresentedGroup.mk_surjective _))
  have hmem (j : Fin r) : X (R j) ∈ Subgroup.zpowers u := by
    rw [←hker,MonoidHom.mem_ker]
    change (q.comp X) (R j)=1
    rw [hcomp,MonoidHom.comp_apply,relation,map_one]
  have twist (j : Fin r) : ∃ a : Fin 2, X (R j)=u^a.val := by
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp ((isOfFinOrder_of_finite u).mem_zpowers_iff_mem_range_orderOf.mp (hmem j))
    exact ⟨⟨v,ho ▸ Finset.mem_range.mp hv⟩,he.symm⟩
  choose c hc using twist
  have hne : c≠0 := by
    intro h
    have hrels : ∀ w ∈ Set.range R, X w = 1 := by
      rintro w ⟨j,rfl⟩
      rw [hc,h]; exact pow_zero _
    let v : Grp R →* G := QuotientGroup.lift _ X (Subgroup.normalClosure_le_normal hrels)
    have hv : Function.Surjective v := by
      intro a
      obtain ⟨w,rfl⟩ := hX a
      exact ⟨PresentedGroup.mk _ w,rfl⟩
    exact no_epi v hv
  let t : Twist r := ⟨c,hne⟩
  have hw : X (R (pivot t)) = u := by rw [hc,show (c (pivot t)).val=1 from pivot_eq t,pow_one]
  let Y := X.comp (substitute (R (pivot t)))
  have hy : Y.comp (FreeGroup.map some) = X := FreeGroup.ext_hom _ _ (fun i => by simp [Y,X,substitute])
  have hy0 : Y (FreeGroup.of none)=u := by simpa [Y,substitute] using hw
  have hrels (j : Unit ⊕ (Fin d ⊕ Fin r)) : Y (newRel R c j)=1 := by
    rcases j with _ | (i | j)
    · simpa only [newRel,map_pow,hy0,←ho] using pow_orderOf_eq_one u
    · rw [newRel,map_commutatorElement,hy0,commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp hz _).symm
    · have hY : Y (FreeGroup.map some (R j)) = X (R j) := DFunLike.congr_fun hy (R j)
      rw [newRel,map_mul,map_inv,map_pow,hy0,hY,hc,mul_inv_cancel]
  have hrels' : ∀ w ∈ Set.range (shortRel R t), X w=1 := by
    rintro _ ⟨j,rfl⟩
    exact hrels _
  let v : Grp (shortRel R t) →* G := QuotientGroup.lift _ X (Subgroup.normalClosure_le_normal hrels')
  refine ⟨t,v,?_⟩
  intro a
  obtain ⟨w,rfl⟩ := hX a
  exact ⟨PresentedGroup.mk _ w,rfl⟩
end Erdos1160.CentralLifts.Survival
end

/- DescendantCount -/
section
namespace Erdos1160.CentralLifts.Survival
open CategoryTheory
def RelDim (d r : ℕ) : ℕ → ℕ
  | 0 => r
  | j+1 => RelDim d r j+d
def ChildCodes (d r : ℕ) : ℕ → Type
  | 0 => Unit
  | j+1 => ChildCodes d r j × Twist (RelDim d r j)
instance (d r j : ℕ) : Finite (ChildCodes d r j) := by
  induction j with
  | zero => exact inferInstanceAs (Finite Unit)
  | succ j ih => exact inferInstanceAs (Finite (ChildCodes d r j × Twist (RelDim d r j)))
theorem rel_dim (d r j : ℕ) : RelDim d r j=r+j*d := by
  induction j with
  | zero => simp [RelDim]
  | succ j ih => simp [RelDim,ih,Nat.succ_mul,Nat.add_assoc]
theorem exact_code_card (d r j : ℕ) :
    Nat.card (ChildCodes d r j) = ∏ i ∈ Finset.range j, (2^(r+i*d)-1) := by
  induction j with
  | zero => simp [ChildCodes]
  | succ j ih =>
    change Nat.card (ChildCodes d r j × Twist (RelDim d r j)) = _
    rw [Nat.card_prod,ih,card_twist,rel_dim,Finset.prod_range_succ]
noncomputable def run {d r : ℕ} (R : Fin r → FreeGroup (Fin d)) :
    {j : ℕ} → ChildCodes d r j → Fin (RelDim d r j) → FreeGroup (Fin d)
  | 0, _ => R
  | _+1,c => shortRel (run R c.1) c.2
variable {d r m : ℕ} {Q G : Type} [Group Q] [Group G] [Finite Q] [Finite G]
def frattiniClasses (m j : ℕ) (Q : Type) [Group Q] : Set (Quotient (isIsomorphicSetoid FiniteGrp.{0})) :=
  {x | ∃ G : FiniteGrp.{0}, Nat.card G=2^(m+j) ∧
    (∃ f : G →* Q, Function.Surjective f ∧ f.ker ≤ frattini G) ∧ Quotient.mk _ G=x}
end Erdos1160.CentralLifts.Survival
end

/- SharpSlots -/
section
namespace Erdos1160Growth.SharpFamily
theorem triangular_card (d : ℕ) :
    Nat.card ((i : Fin d) × Fin i.val) = d * (d - 1) / 2 := by
  rw [Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) d).trans (Finset.sum_range_id d)
end Erdos1160Growth.SharpFamily
end

/- JacobiCount -/
section
namespace Erdos1160.DeepJacobi
abbrev Bit := ZMod 2
variable {q n s : ℕ}
end Erdos1160.DeepJacobi
end

/- ClassThreeJacobi -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
def TripleCentral (G : Type*) [Group G] : Prop :=
  ∀ a b c : G, ⁅⁅a,b⁆,c⁆ ∈ Subgroup.center G
private lemma conj_center (a : G) {v : G} (hv : v ∈ Subgroup.center G) : a*v*a⁻¹=v := by
  rw [Subgroup.mem_center_iff.mp hv a, mul_inv_cancel_right]
private lemma discard_center_factor {v : G} (hv : v ∈ Subgroup.center G) (b c : G) :
    ⁅v*b,c⁆ = ⁅b,c⁆ := by
  have h₁ := (Subgroup.mem_center_iff.mp hv ⁅b,c⁆).symm
  have h₂ : Commute v c := (Subgroup.mem_center_iff.mp hv c).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h₁, mul_inv_cancel_right, h₂.commutator_eq, mul_one]
private lemma corrected_inner (H : TripleCentral G) (a b c : G) :
    ⁅⁅a⁻¹,b⁆,c⁆ = ⁅⁅b,a⁆,c⁆ := by
  have h : ⁅a⁻¹,⁅b,a⁆⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem (H b a a⁻¹)
  have he : a⁻¹*⁅b,a⁆*a = ⁅a⁻¹,⁅b,a⁆⁆ * ⁅b,a⁆ := by
    rw [commutatorElement_def (a⁻¹) ⁅b,a⁆]
    group
  rw [commutatorElement_inv_left,he,discard_center_factor h]
theorem triple_cycle (H : TripleCentral G) (x y z : G) :
    ⁅⁅x,y⁆,z⁆ * ⁅⁅z,x⁆,y⁆ * ⁅⁅y,z⁆,x⁆ = 1 := by
  have h := conj_commutatorElement_left_commutatorElement_mul y x z
  rw [corrected_inner H y x z, corrected_inner H z y x, corrected_inner H x z y] at h
  have hg : y*⁅⁅x,y⁆,z⁆*y⁻¹ * (z*⁅⁅y,z⁆,x⁆*z⁻¹) * (x*⁅⁅z,x⁆,y⁆*x⁻¹) = 1 := by
    simpa only [mul_assoc] using h
  rw [conj_center y (H x y z),conj_center z (H y z x),conj_center x (H z x y)] at hg
  have hc := Subgroup.mem_center_iff.mp (H y z x) ⁅⁅z,x⁆,y⁆
  simpa only [mul_assoc, hc] using hg
private theorem flip_triple (H : TripleCentral G) (a b c : G) :
    ⁅⁅b,a⁆,c⁆ = ⁅⁅a,b⁆,c⁆⁻¹ := by
  rw [← commutatorElement_inv a b, commutatorElement_inv_left]
  rw [← commutatorElement_inv ⁅a,b⁆ c]
  have h := (Subgroup.center G).inv_mem (H a b c)
  simpa using conj_center (⁅a,b⁆⁻¹) h
theorem triple_rearranged (H : TripleCentral G) (x y z : G) :
    ⁅⁅y,z⁆,x⁆ = ⁅⁅x,z⁆,y⁆ * ⁅⁅x,y⁆,z⁆⁻¹ := by
  have hc := triple_cycle H x y z
  rw [flip_triple H x z y] at hc
  exact (eq_inv_of_mul_eq_one_right hc).trans (by simp)
end Erdos1160.DeepJacobi
end

/- GroupBracketLoss -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {q n s : ℕ} {G : Type*} [Group G]
abbrev Third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2
def triple (x y z : G) : Third G :=
  ⟨⁅⁅x,y⁆,z⁆,Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)) (Subgroup.mem_top z)⟩
end Erdos1160.DeepJacobi
end

/- DetectedTriple -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
lemma lower_map_top {K : Type*} [Group K] (f : G →* K) (hf : Function.Surjective f) (n : ℕ) :
    ((⊤ : Subgroup G).lowerCentralSeries n).map f = (⊤ : Subgroup K).lowerCentralSeries n := by
  rw [Subgroup.map_lowerCentralSeries,← MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective f hf]
theorem third_le_of_triples (N : Subgroup G) [N.Normal] (h : ∀ x y z : G, ⁅⁅x,y⁆,z⁆ ∈ N) :
    Third G ≤ N := by
  let f := QuotientGroup.mk' N
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hd : ⁅(⊤ : Subgroup (G ⧸ N)),⊤⁆ ≤ Subgroup.center (G ⧸ N) := by
    refine Subgroup.commutator_le.mpr ?_
    intro x _ y _
    obtain ⟨a,rfl⟩ := hf x
    obtain ⟨b,rfl⟩ := hf y
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨c,rfl⟩ := hf z
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement f,← map_commutatorElement f]
    exact (QuotientGroup.eq_one_iff _).mpr (h _ _ _)
  have hz : Third (G ⧸ N) = ⊥ := Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr hd
  have hm : (Third G).map f = ⊥ := (lower_map_top f hf 2).trans hz
  exact (Subgroup.map_eq_bot_iff (Third G)).mp hm |>.trans (by rw [QuotientGroup.ker_mk'])
end Erdos1160.DeepJacobi
end

/- IntrinsicTensor -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
variable {G : Type*} [Group G]
abbrev Second (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 1
def thirdBracket (w : Second G) (x : G) : Third G :=
  ⟨⁅(w:G),x⁆,Subgroup.commutator_mem_commutator w.property (Subgroup.mem_top x)⟩
def secondBracket (x y : G) : Second G :=
  ⟨⁅x,y⁆,Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
private theorem conjugate_center {w : G} (h : w ∈ Subgroup.center G) (x : G) :
    x*w*x⁻¹ = w := by rw [Subgroup.mem_center_iff.mp h x,mul_inv_cancel_right]
lemma thirdBracket_left (hc : Third G ≤ Subgroup.center G) (a b : Second G) (x : G) :
    thirdBracket (a*b) x = thirdBracket a x * thirdBracket b x := by
  apply Subtype.ext
  change ⁅(a:G)*b,x⁆ = ⁅(a:G),x⁆ * ⁅(b:G),x⁆
  have hb : ⁅(b:G),x⁆ ∈ Subgroup.center G := hc (thirdBracket b x).property
  rw [commutatorElement_mul_left_eq_conj_mul,conjugate_center hb]
  exact Subgroup.mem_center_iff.mp (hc (thirdBracket a x).property) _
lemma thirdBracket_right (hc : Third G ≤ Subgroup.center G) (a : Second G) (x y : G) :
    thirdBracket a (x*y) = thirdBracket a x * thirdBracket a y := by
  apply Subtype.ext
  change ⁅(a:G),x*y⁆ = ⁅(a:G),x⁆ * ⁅(a:G),y⁆
  have hy : ⁅(a:G),y⁆ ∈ Subgroup.center G := hc (thirdBracket a y).property
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅(a:G),x⁆ x, mul_assoc ⁅(a:G),x⁆, conjugate_center hy]
def groupTensor (hc : Third G ≤ Subgroup.center G) (measure : Third G →* Multiplicative Bit) :
    Second G →* (G →* Multiplicative Bit) where
  toFun a :=
    { toFun x := measure (thirdBracket a x)
      map_one' := by rw [show thirdBracket a 1 = 1 by apply Subtype.ext; exact commutatorElement_one_right _]; exact measure.map_one
      map_mul' x y := by rw [thirdBracket_right hc,map_mul] }
  map_one' := by
    apply MonoidHom.ext
    intro x
    change measure (thirdBracket 1 x) = 1
    rw [show thirdBracket 1 x = 1 by apply Subtype.ext; exact commutatorElement_one_left _,map_one]
  map_mul' a b := by
    apply MonoidHom.ext
    intro x
    change measure (thirdBracket (a*b) x) = measure (thirdBracket a x)*measure (thirdBracket b x)
    rw [thirdBracket_left hc,map_mul]
end Erdos1160.DeepJacobi
end

/- FrattiniSquare -/
section
namespace Erdos1160Growth.LowerTriangularUpper
theorem coatom_index_prime_pow {G : Type*} [Group G] [Finite G] {p m : ℕ} [Fact p.Prime]
    (hc : Nat.card G = p^m) (H : Subgroup G) (hH : IsCoatom H) : H.index = p := by
  let hp := (Fact.out : p.Prime)
  have hg : IsPGroup p G := IsPGroup.of_card hc
  obtain ⟨h,hh⟩ := (hg.to_subgroup H).exists_card_eq
  have hlt : h < m := by
    have ht : Nat.card H < Nat.card G := lt_of_le_of_ne (H.card_le_card_group) (fun he => hH.1 (H.eq_top_of_card_eq he))
    rw [hh,hc] at ht
    exact lt_of_not_ge (fun hi => ht.not_ge (Nat.pow_le_pow_right hp.pos hi))
  obtain ⟨J,hJ,hle⟩ := Sylow.exists_subgroup_card_pow_succ (G := G)
    (hc ▸ pow_dvd_pow p (show h+1 ≤ m by omega)) hh
  have hne : H ≠ J := by
    intro he
    rw [← he,hh] at hJ
    exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self h)).ne hJ
  have htop := hH.2 J (lt_of_le_of_ne hle hne)
  have heq := H.index_mul_card
  rw [htop,Subgroup.card_top] at hJ
  rw [hJ,hh,pow_succ,Nat.mul_comm (p^h) p] at heq
  exact Nat.eq_of_mul_eq_mul_right (Nat.pow_pos hp.pos) heq
theorem squares_le_frattini {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G = 2^m) :
    Subgroup.closure (Set.range (fun z : G => z*z)) ≤ frattini G := by
  simp only [frattini,Order.radical,le_iInf_iff]
  intro H hH
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨z,rfl⟩
  exact H.mul_self_mem_of_index_two (coatom_index_prime_pow hc H hH) z
end Erdos1160Growth.LowerTriangularUpper
end

/- JacobiTerminal -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
abbrev C₂ := Multiplicative Bit
private noncomputable def descent {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) (g : X →* Z) (hk : f.ker ≤ g.ker) : Y →* Z :=
  f.liftOfSurjective hf ⟨g,hk⟩
private lemma descent_apply {X Y Z : Type*} [Group X] [Group Y] [Group Z]
    (f : X →* Y) (hf : Function.Surjective f) (g : X →* Z) (hk : f.ker ≤ g.ker) (x : X) :
    descent f hf g hk (f x)= g x := by
  have h := (f.liftOfSurjective hf).left_inv (⟨g,hk⟩ : {g : X →* Z // f.ker ≤ g.ker})
  exact congrArg (fun u : {g : X →* Z // f.ker ≤ g.ker} => u.val x) h
theorem descend_pair {U V Q R B : Type*} [Group U] [Group V] [Group Q] [Group R] [CommGroup B]
    (f : U →* Q) (hf : Function.Surjective f) (g : V →* R) (hg : Function.Surjective g)
    (a : U →* (V →* B)) (hk₁ : f.ker ≤ a.ker) (hk₂ : ∀u,g.ker ≤ (a u).ker) :
    ∃ t : Q →* (R →* B), ∀u v, t (f u) (g v) = a u v := by
  let row (u : U) := descent g hg (a u) (hk₂ u)
  have he (u : U) (v : V) : row u (g v)=a u v := descent_apply ..
  let t : U →* (R →* B) := {
    toFun := row
    map_one' := by
      apply MonoidHom.ext
      intro r
      obtain ⟨v,rfl⟩ := hg r
      rw [he,a.map_one]; rfl
    map_mul' u w := by
      apply MonoidHom.ext
      intro r
      obtain ⟨v,rfl⟩ := hg r
      change row (u*w) (g v) = row u (g v) * row w (g v)
      rw [he,he,he,a.map_mul]; rfl }
  have hk : f.ker ≤ t.ker := by
    intro u hu
    apply MonoidHom.ext
    intro r
    obtain ⟨v,rfl⟩ := hg r
    change row u (g v)=1
    rw [he,show a u=1 from hk₁ hu]; rfl
  refine ⟨descent f hf t hk,fun u v => ?_⟩
  rw [descent_apply]; exact he u v
variable {E Q : Type*} [Group E] [Group Q]
def secondMap (f : E →* Q) (hf : Function.Surjective f) : Second E →* Second Q :=
  (f.comp (Second E).subtype).codRestrict _ (fun w => (lower_map_top f hf 1).le (show f w.val ∈ (Second E).map f from ⟨w.val,w.property,rfl⟩))
lemma secondMap_surj (f : E →* Q) (hf : Function.Surjective f) :
    Function.Surjective (secondMap f hf) := by
  intro w
  have h : w.val ∈ (Second E).map f := (lower_map_top f hf 1).symm ▸ w.property
  obtain ⟨v,hv,he⟩ := h
  exact ⟨⟨v,hv⟩,Subtype.ext he⟩
lemma secondMap_bracket (f : E →* Q) (hf : Function.Surjective f) (x y : E) :
    secondMap f hf (secondBracket x y) = secondBracket (f x) (f y) :=
  Subtype.ext (map_commutatorElement f x y)
end Erdos1160.DeepJacobi
end

/- DerivedThird -/
section
namespace ThirdLowerCentral
abbrev third (G : Type*) [Group G] := (⊤ : Subgroup G).lowerCentralSeries 2
theorem trivial_iff {G : Type*} [Group G] :
    third G = ⊥ ↔ commutator G ≤ Subgroup.center G := by
  change ⁅commutator G,(⊤ : Subgroup G)⁆ = ⊥ ↔ _
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  simp [Subgroup.centralizer_univ]
theorem order_two_central {G : Type*} [Group G] (K : Subgroup G) [hn : K.Normal]
    (hc : Nat.card K = 2) : K ≤ Subgroup.center G := by
  intro x hx
  apply Subgroup.mem_center_iff.mpr
  intro y
  by_cases h : x=1
  · simp [h]
  let a : K := ⟨x,hx⟩
  let b : K := ⟨y*x*y⁻¹,hn.conj_mem _ hx y⟩
  have ha : a ≠ 1 := fun e => h (congrArg Subtype.val e)
  have hb : b ≠ 1 := by
    intro h'
    have he : y*x*y⁻¹=1 := congrArg Subtype.val h'
    have he' : (y*x*y⁻¹)*y = y := by rw [he, one_mul]
    exact h (by simpa using he')
  have hab := (Nat.card_eq_two_iff' (1 : K)).mp hc
  have eq : b=a := hab.unique hb ha
  have hh : y*x*y⁻¹=x := congrArg Subtype.val eq
  simpa using congrArg (· * y) hh
theorem quotient_has_class_two (G : Type*) [Group G] :
    commutator (G ⧸ third G) ≤ Subgroup.center (G ⧸ third G) := by
  apply trivial_iff.mp
  let q := QuotientGroup.mk' (third G)
  have onto : (⊤ : Subgroup G).map q = ⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have he := (⊤ : Subgroup G).map_lowerCentralSeries q 2
  rw [onto] at he
  change (⊤ : Subgroup (G ⧸ third G)).lowerCentralSeries 2 = ⊥
  rw [← he]
  exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
end ThirdLowerCentral
end

/- CentralBound -/
section
namespace CentralKernelCount
open scoped commutatorElement
def adjoin {G : Type*} [Group G] {d : ℕ} (N : Subgroup G) (x : Fin d → G) : Subgroup G :=
  N ⊔ Subgroup.closure (Set.range x)
theorem card_adjoin_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (N : Subgroup G) [N.Normal]
    (x : Fin d → G) (n : Fin d → ℕ) (hn : ∀ i, 0 < n i) (hsq : ∀ i, x i ^ n i ∈ N) (hcomm : ∀ i j, ⁅x i,x j⁆ ∈ N) :
    Nat.card (adjoin N x) ≤ (∏ i, n i) * Nat.card N := by
  classical
  let π := QuotientGroup.mk' N
  let S := adjoin N x
  let f := π.comp S.subtype
  let H (i : Fin d) := Subgroup.zpowers (π (x i))
  have van {g : G} (h : g ∈ N) : π g = 1 := (QuotientGroup.eq_one_iff _).mpr h
  have commute : Pairwise fun i j => ∀ z w : G ⧸ N, z ∈ H i → w ∈ H j → Commute z w := by
    intro i j _ z w hz hw
    obtain ⟨m,rfl⟩ := hz
    obtain ⟨n,rfl⟩ := hw
    have hc : Commute (π (x i)) (π (x j)) :=
      commutatorElement_eq_one_iff_mul_comm.mp <| (map_commutatorElement π _ _).symm.trans (van (hcomm i j))
    exact hc.zpow_zpow _ _
  let p := Subgroup.noncommPiCoprod commute
  have hSP : S ≤ p.range.comap π := by
    apply sup_le
    · intro z hz
      change π z ∈ p.range
      rw [van hz]
      exact p.range.one_mem
    · rw [Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      change π (x i) ∈ p.range
      rw [show p.range = ⨆ i, H i from Subgroup.noncommPiCoprod_range]
      exact (le_iSup H i) (Subgroup.mem_zpowers _)
  have hrange : f.range ≤ p.range := by
    rintro z ⟨w,rfl⟩
    exact hSP w.property
  have hp : Nat.card p.range ≤ ∏ i, n i := by
    apply (Nat.card_le_card_of_surjective _ p.rangeRestrict_surjective).trans
    rw [Nat.card_pi]
    apply Finset.prod_le_prod'
    intro i _
    change Nat.card (Subgroup.zpowers (π (x i))) ≤ n i
    rw [Nat.card_zpowers]
    apply Nat.le_of_dvd (hn i)
    exact orderOf_dvd_of_pow_eq_one <| (map_pow π _ _).symm.trans (van (hsq i))
  have hk : Nat.card f.ker ≤ Nat.card N := by
    let m (z : f.ker) : N := ⟨z.val.val,(QuotientGroup.eq_one_iff _).mp z.property⟩
    apply Nat.card_le_card_of_injective m
    intro z w hw
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun q : N => q.val) hw)
  change Nat.card S ≤ _
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  apply Nat.mul_le_mul _ hk
  exact (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hrange)).trans hp
end CentralKernelCount
end

/- PairedCentral -/
section
namespace CentralKernelCount
open scoped commutatorElement
theorem map_adjoin {G J : Type*} [Group G] [Group J] {d : ℕ}
    (N : Subgroup G) (x : Fin d → G) (f : G →* J) :
    (adjoin N x).map f = adjoin (N.map f) (fun i => f (x i)) := by
  rw [adjoin,adjoin,Subgroup.map_sup,MonoidHom.map_closure,← Set.range_comp]
  rfl
end CentralKernelCount
end

/- CentralCode -/
section
namespace CentralKernelCount
open scoped commutatorElement
abbrev PairSlot (d : ℕ) := (i : Fin d) × Fin i.val
def second {d : ℕ} (p : PairSlot d) : Fin d := ⟨p.2.val,p.2.isLt.trans p.1.isLt⟩
def word {G : Type*} [Group G] {t : ℕ} (y : Fin t → G) (w : List (Fin t)) := (w.map y).prod
end CentralKernelCount
end

/- CentralCoordinates -/
section
namespace CentralKernelCount
open scoped commutatorElement
abbrev BitGroup (d : ℕ) := Multiplicative (Fin d → ZMod 2)
def bit {d : ℕ} (i : Fin d) : BitGroup d := Multiplicative.ofAdd (Pi.single i 1)
theorem word_mem {G : Type*} [Group G] {t : ℕ}
    (S : Subgroup G) (y : Fin t → G) (hy : ∀ i, y i ∈ S) (l : List (Fin t)) : word y l ∈ S := by
  induction l with
  | nil => exact S.one_mem
  | cons i l h => exact S.mul_mem (hy i) h
theorem bits_word (d : ℕ) (w : BitGroup d) : ∃ l, word bit l = w := by
  change ∃ l, word bit l = Multiplicative.ofAdd w.toAdd
  induction w.toAdd using Pi.single_induction with
  | zero => exact ⟨[],rfl⟩
  | add x y hx hy =>
    obtain ⟨l,hl⟩ := hx
    obtain ⟨r,hr⟩ := hy
    use l++r
    simpa only [word,List.map_append,List.prod_append,ofAdd_add] using congrArg₂ (·*·) hl hr
  | single i c =>
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 by decide) c with rfl|rfl
    · exact ⟨[],by simp [word]⟩
    · exact ⟨[i],by simp [word,bit]⟩
end CentralKernelCount
end

/- LowerTriangularUpper -/
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
abbrev V (d : ℕ) := Fin d → ZMod 2
variable {d s : ℕ}
end Erdos1160Growth.LowerTriangularUpper
end

/- ElementaryCoords -/
section
namespace Erdos1160Growth.LowerTriangularUpper
lemma exist_elementary_coords {G : Type*} [Group G] [Finite G] {d : ℕ}
    (h : ∀ x : G, x*x=1) (hcard : Nat.card G = 2^d) :
    Nonempty (G ≃* Multiplicative (V d)) := by
  classical
  have hinv (x : G) : x⁻¹=x := inv_eq_of_mul_eq_one_left (h x)
  let _ : CommGroup G := { ‹Group G› with
    mul_comm := fun x y => by
      calc x*y = (x*y)⁻¹ := (hinv _).symm
           _ = y*x := by rw [mul_inv_rev,hinv,hinv] }
  let _ : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact h x.toMul)
  let _ : Fintype (Additive G) := Fintype.ofFinite _
  have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive G)
  rw [← Nat.card_eq_fintype_card, ZMod.card] at hc
  change Nat.card G = 2^Module.finrank (ZMod 2) (Additive G) at hc
  rw [hcard] at hc
  have hd : Module.finrank (ZMod 2) (Additive G) = d :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hc.symm
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hd).equivFun
  exact ⟨e.toAddEquiv.toMultiplicativeRight⟩
end Erdos1160Growth.LowerTriangularUpper
end

/- SquareCoreCount -/
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
def squareCore (E : Type*) [Group E] : Subgroup E :=
  Subgroup.closure (Set.range fun x : E => x*x)
end Erdos1160Growth.LowerTriangularUpper
end

/- FrattiniContainment -/
section
namespace Erdos1160Growth.LowerTriangularUpper
private lemma frattini_f2 : frattini (Multiplicative (ZMod 2)) = ⊥ := by
  let _ : Fact (Nat.card (Multiplicative (ZMod 2))).Prime := ⟨by
    change (Nat.card (ZMod 2)).Prime
    rw [Nat.card_zmod]
    decide⟩
  apply le_antisymm _ bot_le
  apply frattini_le_coatom
  refine ⟨bot_ne_top, ?_⟩
  intro H h
  exact H.eq_bot_or_eq_top_of_prime_card.resolve_left (ne_of_gt h)
instance squareCore_normal {E : Type*} [Group E] : (squareCore E).Normal := by
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro h _ _ ⟨g,rfl⟩
  apply Subgroup.subset_closure
  exact ⟨h*g*h⁻¹, by group⟩
theorem frattini_le_squareCore {E : Type*} [Group E] [Finite E] : frattini E ≤ squareCore E := by
  let K := squareCore E
  let π := QuotientGroup.mk' K
  have hq (x : E ⧸ K) : x*x=1 := by
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective K x
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨y,rfl⟩)
  have htwo : IsPGroup 2 (E ⧸ K) := fun x => ⟨1, by rw [pow_one,pow_two]; exact hq x⟩
  obtain ⟨n,hn⟩ := htwo.exists_card_eq
  obtain ⟨e⟩ := exist_elementary_coords hq hn
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply e.injective
  rw [map_one]
  have heval (i : Fin n) :
      ((e (π x)).toAdd i) = 0 := by
    let f : Multiplicative (V n) →* Multiplicative (ZMod 2) :=
      { toFun := fun v => Multiplicative.ofAdd (v.toAdd i)
        map_mul' := fun _ _ => rfl
        map_one' := rfl }
    have onto_f : Function.Surjective f := fun v => ⟨Multiplicative.ofAdd (fun _ => v.toAdd),rfl⟩
    let ψ := f.comp (e.toMonoidHom.comp π)
    have hφ : Function.Surjective ψ := onto_f.comp (e.surjective.comp (QuotientGroup.mk'_surjective K))
    have hmem := (frattini_le_comap_frattini_of_surjective hφ) hx
    change ψ x ∈ frattini (Multiplicative (ZMod 2)) at hmem
    rw [frattini_f2] at hmem
    exact congrArg Multiplicative.toAdd (Subgroup.mem_bot.mp hmem)
  exact congrArg Multiplicative.ofAdd (funext heval)
end Erdos1160Growth.LowerTriangularUpper
end

/- FrattiniCount -/
section
namespace Erdos1160Growth.LowerTriangularUpper
open CategoryTheory
theorem frattini_eq_squareCore {G : Type*} [Group G] [Finite G] {m : ℕ}
    (h : Nat.card G = 2^m) : frattini G = squareCore G :=
  le_antisymm frattini_le_squareCore (squares_le_frattini h)
end Erdos1160Growth.LowerTriangularUpper
end

/- PresentationCount -/
section
namespace Erdos1160.PresentationCount
open CategoryTheory
theorem card_le_of_fiber_bound {A B : Type*} [Finite A] [Finite B] (f : A → B)
    (M : ℕ) (h : ∀ b : B, Nat.card {a : A // f a = b} ≤ M) :
    Nat.card A ≤ Nat.card B * M := by
  classical
  let : Fintype B := Fintype.ofFinite B
  calc
    Nat.card A = ∑ b : B, Nat.card {a : A // f a = b} := by
      rw [← Nat.card_sigma]
      exact (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ ≤ ∑ _b : B, M := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * M := by simp [Nat.card_eq_fintype_card]
end Erdos1160.PresentationCount
end

/- CentralQuotient -/
section
namespace CentralKernelCount
open CategoryTheory Erdos1160Growth.LowerTriangularUpper
theorem squareCore_map {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (squareCore G).map f = squareCore H := by
  rw [squareCore,squareCore,MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨f g,(f.map_mul ..).symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨x,rfl⟩ := hf g
    exact ⟨x*x,⟨x,rfl⟩,f.map_mul ..⟩
end CentralKernelCount
end

/- TerminalTree -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
open Erdos1160Growth.LowerTriangularUpper CentralLifts
def binaryThird (G : Type*) [Group G] : Subgroup G :=
  Subgroup.closure (Set.range (fun x : squareCore G => x.val*x.val) ∪
    Set.range (fun z : squareCore G × G => ⁅z.1.val,z.2⁆))
variable {G Q : Type} [Group G] [Group Q] [Finite G] [Finite Q] {m : ℕ}
omit [Finite Q] in
theorem one_step_factor (hQ : Nat.card Q=2^m) (j : ℕ) (hG : Nat.card G=2^(m+(j+1)))
    (f : G →* Q) (hf : Function.Surjective f) :
    ∃ (Y : FiniteGrp.{0}) (q : G →* Y) (k : Y →* Q), Function.Surjective q ∧
      Function.Surjective k ∧ k.comp q=f ∧ Nat.card Y=2^(m+1) := by
  induction j generalizing G with
  | zero => exact ⟨FiniteGrp.of G,MonoidHom.id G,f,Function.surjective_id,hf,rfl,hG⟩
  | succ j ih =>
    have hcard := ker_card_of_epi Nat.prime_two hG hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hG) f.ker
      (hcard ▸ dvd_pow_self 2 (Nat.succ_ne_zero _))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let π := QuotientGroup.mk' N
    let F := QuotientGroup.lift N f (Subgroup.zpowers_le.mpr hu)
    have ontoF : Function.Surjective F := fun y => by
      obtain ⟨x,rfl⟩ := hf y
      exact ⟨π x,rfl⟩
    obtain ⟨Y,q,k,hq,hk,he,hY⟩ := ih (card_quotient_prime (by decide : 0 < 2) ho (k := m+(j+1)) hG) F ontoF
    exact ⟨Y,q.comp π,k,hq.comp (QuotientGroup.mk'_surjective N),hk,
      by rw [←MonoidHom.comp_assoc,he];rfl,hY⟩
end Erdos1160.DeepJacobi
end

/- VirtualBounds -/
section
namespace Erdos1160.CentralLifts.Survival
def QuotientCap (P : Type) [Group P] (N : ℕ) := ∀ (Y : Type) [Group Y] [Finite Y],
  IsPGroup 2 Y → ∀ f : P →* Y, Function.Surjective f → Nat.card Y ≤ N
variable {d r m N : ℕ} {P : Type} [Group P]
theorem cap_after_short (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) N) (c : Twist r) :
    QuotientCap (Grp (shortRel R c)) (N*2) := by
  intro Y _ _ hY h hh
  let f := h.comp (contractShort R c)
  have hf : Function.Surjective f := hh.comp (contractShort_surj R c)
  let u := f (z R c.val)
  have hu : u ∈ Subgroup.center Y := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := hf y
    exact (map_mul f _ _).symm.trans ((congrArg f (Subgroup.mem_center_iff.mp (z_central R c.val) w)).trans (map_mul f _ _))
  let Z := Subgroup.zpowers u
  let _ : Z.Normal := normal_zpowers_of_central u hu
  have hz : Nat.card Z ≤ 2 := by
    rw [show Nat.card Z=orderOf u by exact Nat.card_zpowers _]
    apply orderOf_le_of_pow_eq_one (by decide)
    exact (map_pow f _ _).symm.trans ((congrArg f (z_pow R c.val)).trans f.map_one)
  let L := Subgroup.zpowers (z R c.val)
  have hl : L ≤ Z.comap f := Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers _)
  let ψ := QuotientGroup.map L Z f hl
  have hp : Function.Surjective ψ := by
    intro w
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective Z w
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' L x,rfl⟩
  let π := ψ.comp (quotientMap R c.val)
  have hπ := hp.comp (quotientMap_surjective R c.val)
  have hQ := hR (Y ⧸ Z) (hY.to_quotient Z) π hπ
  rw [Z.card_eq_card_quotient_mul_card_subgroup]
  exact Nat.mul_le_mul hQ hz
theorem cap_run (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) N)
    (j : ℕ) (c : ChildCodes d r j) : QuotientCap (Grp (run R c)) (N*2^j) := by
  induction j with
  | zero => change QuotientCap (Grp R) (N*2^0); rw [pow_zero,mul_one];exact hR
  | succ j ih =>
    rw [pow_succ,←Nat.mul_assoc]
    exact cap_after_short _ (ih c.1) c.2
theorem max_quotients_iso {E F : Type} [Group E] [Group F] [Finite E] [Finite F]
    (cap : QuotientCap P (2^m)) (hE : Nat.card E=2^m) (hF : Nat.card F=2^m)
    (f : P →* E) (g : P →* F) (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Nonempty (E ≃* F) := by
  let D := (f.prod g).range
  have hp : IsPGroup 2 (E × F) := IsPGroup.of_card (show Nat.card (E × F)=2^(m+m) by
    rw [Nat.card_prod,hE,hF,pow_add])
  have hc : Nat.card D ≤ 2^m := cap D (hp.to_subgroup _) _ (f.prod g).rangeRestrict_surjective
  let fst := (MonoidHom.fst E F).comp D.subtype
  let snd := (MonoidHom.snd E F).comp D.subtype
  have hfst : Function.Surjective fst := by
    intro y;obtain ⟨x,rfl⟩ := hf y;exact ⟨(f.prod g).rangeRestrict x,rfl⟩
  have hsnd : Function.Surjective snd := by
    intro y;obtain ⟨x,rfl⟩ := hg y;exact ⟨(f.prod g).rangeRestrict x,rfl⟩
  have h1 : Nat.card D=Nat.card E := le_antisymm (hc.trans_eq hE.symm) (Nat.card_le_card_of_surjective fst hfst)
  have h2 : Nat.card D=Nat.card F := h1.trans (hE.trans hF.symm)
  let a := MulEquiv.ofBijective fst ((Nat.bijective_iff_surjective_and_card fst).2 ⟨hfst,h1⟩)
  let b := MulEquiv.ofBijective snd ((Nat.bijective_iff_surjective_and_card snd).2 ⟨hsnd,h2⟩)
  exact ⟨a.symm.trans b⟩
end Erdos1160.CentralLifts.Survival
end

/- RelationCharacters -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂ one_step_factor)
variable {F Q : Type} [Group F] [Group Q]
def conjugateRelation (π : F →* Q) (g : F) (r : π.ker) : π.ker :=
  ⟨g*r.val*g⁻¹,(inferInstance : π.ker.Normal).conj_mem _ r.property _⟩
def RelCharacters (π : F →* Q) : Subgroup (π.ker →* C₂) where
  carrier := {chi | ∀g r,chi (conjugateRelation π g r)=chi r}
  one_mem' := fun _ _ => rfl
  mul_mem' := by intro a b ha hb g r; change a _ * b _ = a r * b r; rw [ha g r,hb g r]
  inv_mem' := by intro a ha g r; change (a _)⁻¹ = (a r)⁻¹; rw [ha g r]
instance {π : F →* Q} [Group.FG F] [Finite Q] : Finite (RelCharacters π) := by
  have hf : Group.FG π.ker := inferInstance
  obtain ⟨ι,_,f,hf⟩ := Group.fg_iff_exists_freeGroup_hom_surjective_finite.mp hf
  let C (a : RelCharacters π) (i : ι) : C₂ := a.val (f (FreeGroup.of i))
  apply Finite.of_injective C
  intro a b he
  apply Subtype.ext
  have h : a.val.comp f=b.val.comp f := FreeGroup.ext_hom _ _ (fun i => congrFun he i)
  apply MonoidHom.ext
  intro r
  obtain ⟨v,rfl⟩ := hf r
  exact DFunLike.congr_fun h v
instance (π : F →* Q) : Module (ZMod 2) (Additive (RelCharacters π)) :=
  AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    apply Subtype.ext
    apply MonoidHom.ext
    intro r
    change x.toMul.val r * x.toMul.val r=1
    exact (show ∀v : C₂,v*v=1 by decide) _)
def relEval (π : F →* Q) (r : π.ker) : Additive (RelCharacters π) →ₗ[ZMod 2] ZMod 2 :=
  (show Additive (RelCharacters π) →+ ZMod 2 from
    { toFun := fun a => (a.toMul.val r).toAdd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }).toZModLinearMap 2
theorem relEval_separates (π : F →* Q) (a : Additive (RelCharacters π)) (h : ∀r,relEval π r a = 0) : a=0 := by
  change a.toMul=1
  apply Subtype.ext
  apply MonoidHom.ext
  intro r
  exact (show (a.toMul.val r).toAdd=0 from h r)
private theorem normal_image_character {Y : Type} [Group Y] [Finite Y] (hp : IsPGroup 2 Y)
    (N : Subgroup Y) [N.Normal] (hn : N≠⊥) : ∃ (B : N →* C₂),
      Function.Surjective B ∧ ∀ (g : Y) (r : N),B ⟨g*r.val*g⁻¹,(inferInstance : N.Normal).conj_mem _ r.property _⟩=B r := by
  classical
  obtain ⟨m,hm⟩ := hp.exists_card_eq
  obtain ⟨k,hk⟩ := (hp.to_quotient N).exists_card_eq
  have hlt : k < m := by
    have hq := N.card_eq_card_quotient_mul_card_subgroup
    rw [hm,hk] at hq
    have hcard : 1 < Nat.card N := by
      have : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hn
      exact Finite.one_lt_card
    exact lt_of_not_ge (fun hle => by
      have H := (Nat.pow_le_pow_right (by decide : 0 < 2) hle).trans_lt
        (show 2^k < 2^k*Nat.card N by simpa only [Nat.mul_one] using Nat.mul_lt_mul_of_pos_left hcard (Nat.two_pow_pos k))
      exact H.ne hq)
  let j := m-(k+1)
  have he : m=k+(j+1) := by dsimp [j];omega
  obtain ⟨U,q,b,hq,hb,eq,hU⟩ := one_step_factor hk j (hm.trans (congrArg (2^·) he))
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have hbc : Nat.card b.ker=2 := by simpa using ker_card_of_epi Nat.prime_two hU hk b hb
  have hz := ThirdLowerCentral.order_two_central b.ker hbc
  have hker (r : N) : q r.val ∈ b.ker := by
    change (b.comp q) r.val=1
    rw [eq]
    exact (QuotientGroup.eq_one_iff _).mpr r.property
  let f := (q.comp N.subtype).codRestrict b.ker hker
  have onto : Function.Surjective f := by
    intro r
    obtain ⟨g,hg⟩ := hq r.val
    have hg' : g ∈ N := (QuotientGroup.eq_one_iff _).mp (by
      change QuotientGroup.mk' N g=1;rw [←eq,MonoidHom.comp_apply,hg];exact r.property)
    exact ⟨⟨g,hg'⟩,Subtype.ext hg⟩
  let c : b.ker ≃* C₂ := mulEquivOfPrimeCardEq hbc (Nat.card_zmod 2)
  refine ⟨c.toMonoidHom.comp f,c.surjective.comp onto,?_⟩
  intro g r
  apply congrArg c
  apply Subtype.ext
  change q (g*r.val*g⁻¹)=q r.val
  rw [map_mul,map_mul,map_inv,Subgroup.mem_center_iff.mp (hz (hker r)) (q g),mul_inv_cancel_right]
theorem detecting_character (π : F →* Q) {Y : Type} [Group Y] [Finite Y] (hp : IsPGroup 2 Y)
    (f : F →* Y) (hf : Function.Surjective f) (bad : ¬π.ker ≤ f.ker) :
    ∃ a : RelCharacters π,a≠1 ∧ ∀r : π.ker, f r.val=1 → a.val r=1 := by
  let N := π.ker.map f
  let _ : N.Normal := Subgroup.Normal.map (inferInstance : π.ker.Normal) f hf
  have hn : N≠⊥ := by
    intro he
    apply bad
    intro x hx
    exact Subgroup.mem_bot.mp (he ▸ (show f x∈N from ⟨x,hx,rfl⟩))
  obtain ⟨χ,hχ,invχ⟩ := normal_image_character hp N hn
  let F₀ := (f.comp π.ker.subtype).codRestrict N (fun r => ⟨r.val,r.property,rfl⟩)
  have hF₀ : Function.Surjective F₀ := by
    rintro ⟨_,r,hr,rfl⟩
    exact ⟨⟨r,hr⟩,rfl⟩
  let a := χ.comp F₀
  have inv (g : F) (r : π.ker) : a (conjugateRelation π g r)=a r := by
    apply Eq.trans _ (invχ (f g) (F₀ r))
    apply congrArg χ
    apply Subtype.ext
    change f (g*r.val*g⁻¹)=f g*f r.val*(f g)⁻¹
    simp
  refine ⟨⟨a,inv⟩,?_,?_⟩
  · intro he
    obtain ⟨r,hr⟩ := (hχ.comp hF₀) (Multiplicative.ofAdd 1)
    have hz := congrArg (fun u : RelCharacters π => (u.val r).toAdd) he
    change (a r).toAdd=0 at hz
    change a r=Multiplicative.ofAdd 1 at hr
    rw [hr] at hz
    exact (by decide : (1 : ZMod 2) ≠0) hz
  · intro r hr
    have h : F₀ r=1 := Subtype.ext hr
    change χ (F₀ r)=1
    rw [h,χ.map_one]
end Erdos1160.CentralLifts.Survival
end

/- VirtualDescendants -/
section
namespace Erdos1160.CentralLifts.Survival
open CategoryTheory
variable {d r m : ℕ} {Q G : Type} [Group Q] [Group G] [Finite Q] [Finite G]
omit [Finite Q] in
theorem virtual_cover (R : Fin r → FreeGroup (Fin d)) (hR : QuotientCap (Grp R) (2^m))
    (q0 : Grp R →* Q) (hq0 : Function.Surjective q0) (hQ : Nat.card Q=2^m)
    (j : ℕ) (hG : Nat.card G=2^(m+j)) (f : G →* Q) (hf : Function.Surjective f)
    (hΦ : f.ker ≤ frattini G) :
    ∃ c : ChildCodes d r j, ∃ v : Grp (run R c) →* G, Function.Surjective v := by
  induction j generalizing G with
  | zero =>
    let e := MulEquiv.ofBijective f ((Nat.bijective_iff_surjective_and_card f).2 ⟨hf,hG.trans hQ.symm⟩)
    exact ⟨(),e.symm.toMonoidHom.comp q0,e.symm.surjective.comp hq0⟩
  | succ j ih =>
    have hsize := ker_card_of_epi Nat.prime_two hG hQ f hf
    obtain ⟨u,hu,hz,ho⟩ := central_prime_in_normal Nat.prime_two (IsPGroup.of_card hG) f.ker
      (hsize ▸ dvd_pow_self 2 (Nat.succ_ne_zero j))
    let N := Subgroup.zpowers u
    let _ : N.Normal := normal_zpowers_of_central u hz
    let π := QuotientGroup.mk' N
    have hπ := QuotientGroup.mk'_surjective N
    have hN : N ≤ f.ker := Subgroup.zpowers_le.mpr hu
    let F := QuotientGroup.lift N f hN
    have ontoF : Function.Surjective F := fun x => by
      obtain ⟨a,rfl⟩ := hf x
      exact ⟨π a,rfl⟩
    have frF : F.ker ≤ frattini (G ⧸ N) := by
      intro w hw
      obtain ⟨a,rfl⟩ := hπ w
      exact (frattini_le_comap_frattini_of_surjective hπ) (hΦ (show a∈f.ker from hw))
    have cardQ := card_quotient_prime (by decide : 0 < 2) ho (k := m+j) hG
    obtain ⟨c,g,hg⟩ := ih cardQ F ontoF frF
    have noepi (v : Grp (run R c) →* G) (hv : Function.Surjective v) : False := by
      have h := cap_run R hR j c G (IsPGroup.of_card hG) v hv
      rw [←pow_add,hG] at h
      exact (Nat.pow_lt_pow_right (by decide : 1 < 2) (show m+j < m+(j+1) by omega)).not_ge h
    have hk : π.ker ≤ frattini G := (QuotientGroup.ker_mk' N).le.trans (hN.trans hΦ)
    obtain ⟨t,w,hw⟩ := child_cover_of_no_epi (run R c) g hg noepi π hπ hk u ho hz (QuotientGroup.ker_mk' N)
    exact ⟨(c,t),w,hw⟩
omit [Finite Q] in


theorem virtual_frattini_count (R : Fin r → FreeGroup (Fin d)) (cap : QuotientCap (Grp R) (2^m))
    (q : Grp R →* Q) (hq : Function.Surjective q) (hQ : Nat.card Q=2^m) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(r+i*d)-1) := by
  classical
  let S := frattiniClasses m j Q
  have reps (x : S) : ∃ (Y : FiniteGrp.{0}) (c : ChildCodes d r j) (v : Grp (run R c) →* Y),
      Quotient.mk _ Y=x.val ∧ Nat.card Y=2^(m+j) ∧ Function.Surjective v := by
    obtain ⟨Y,hY,⟨f,hf,hk⟩,eq⟩ := x.property
    obtain ⟨c,v,hv⟩ := virtual_cover R cap q hq hQ j hY f hf hk
    exact ⟨Y,c,v,eq,hY,hv⟩
  choose Y c v eq hc hv using reps
  have hinj : Function.Injective c := by
    intro x y he
    have hy : ∃ f : Grp (run R (c x)) →* Y y, Function.Surjective f := he ▸ ⟨v y,hv y⟩
    obtain ⟨f,hf⟩ := hy
    have b := cap_run R cap j (c x)
    rw [←pow_add] at b
    obtain ⟨e⟩ := max_quotients_iso b (hc x) (hc y) (v x) f (hv x) hf
    apply Subtype.ext
    rw [←eq x,←eq y]
    apply Quotient.sound
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩
  exact (Nat.card_le_card_of_injective c hinj).trans (exact_code_card d r j).le
end Erdos1160.CentralLifts.Survival
end

/- SeparatingEvaluations -/
section
namespace OrbitUp
theorem exists_injective_evaluations {K A I : Type*} [Field K] [AddCommGroup A] [Module K A]
    [FiniteDimensional K A] (ev : I → Module.Dual K A)
    (separates : ∀ x : A, (∀ i, ev i x = 0) → x=0) :
    ∃ select : Fin (Module.finrank K A) → I,
      Function.Injective (fun x : A => fun j => ev (select j) x) := by
  classical
  let W := Submodule.span K (Set.range ev)
  have hz : W.dualCoannihilator = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply separates
    intro i
    exact (Submodule.mem_dualCoannihilator x).mp hx _ (Submodule.subset_span ⟨i,rfl⟩)
  have hr : Module.finrank K W = Module.finrank K A := by
    have eq := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hz] at eq
    simpa using eq
  obtain ⟨f,hf,hs,_⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range ev)
  choose j hj using hf
  let cast := finCongr hr
  refine ⟨fun k => j (cast.symm k), fun x y he => ?_⟩
  have hk : Submodule.span K (Set.range f) ≤ (Module.Dual.eval K A (x-y)).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    change f k (x-y) = 0
    rw [← hj k,map_sub,sub_eq_zero]
    have h := congrFun he (cast k)
    simpa only [cast.symm_apply_apply] using h
  apply sub_eq_zero.mp
  apply separates
  intro i
  apply hk
  rw [hs]
  exact Submodule.subset_span ⟨i,rfl⟩
end OrbitUp
end

/- MultiplicatorCount -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (C₂)
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
noncomputable def relRank (π : FreeGroup (Fin d) →* Q) :=
  Module.finrank (ZMod 2) (Additive (RelCharacters π))
theorem multiplicator_presentation (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π) :
    ∃ R : Fin (relRank π) → FreeGroup (Fin d), QuotientCap (Grp R) (Nat.card Q) ∧
      ∃ q : Grp R →* Q, Function.Surjective q := by
  classical
  obtain ⟨S,hS⟩ := OrbitUp.exists_injective_evaluations (relEval π) (relEval_separates π)
  let R : Fin (relRank π) → FreeGroup (Fin d) := fun j => (S j).val
  have hR : Subgroup.normalClosure (Set.range R) ≤ π.ker := by
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨j,rfl⟩
    exact (S j).property
  let q : Grp R →* Q := QuotientGroup.lift _ π hR
  have hq : Function.Surjective q := fun y => by
    obtain ⟨x,rfl⟩ := hπ y
    exact ⟨PresentedGroup.mk _ x,rfl⟩
  refine ⟨R,?_,q,hq⟩
  intro Y _ _ hp f hf
  let F := f.comp (PresentedGroup.mk (Set.range R))
  have hF : Function.Surjective F := hf.comp (PresentedGroup.mk_surjective _)
  have hker : π.ker ≤ F.ker := by
    by_contra bad
    obtain ⟨a,ha,hkill⟩ := detecting_character π hp F hF bad
    apply ha
    have H : (fun j => relEval π (S j) (Additive.ofMul a))=(fun j => relEval π (S j) 0) := by
      funext j
      apply congrArg Multiplicative.toAdd
      apply hkill
      change f (PresentedGroup.mk (Set.range R) (R j))=1
      exact (congrArg f (relation R j)).trans f.map_one
    exact hS H
  let ψ := π.liftOfSurjective hπ ⟨F,hker⟩
  have he := (π.liftOfSurjective hπ).left_inv (⟨F,hker⟩ : {u : FreeGroup (Fin d) →* Y // π.ker ≤ u.ker})
  have hy : Function.Surjective ψ := by
    intro y
    obtain ⟨x,rfl⟩ := hF y
    exact ⟨π x,congrArg (fun u : {u : FreeGroup (Fin d) →* Y // π.ker ≤ u.ker} => u.val x) he⟩
  exact Nat.card_le_card_of_surjective ψ hy
theorem multiplicator_fiber_product (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(relRank π+i*d)-1) := by
  obtain ⟨R,cap,q,hq⟩ := multiplicator_presentation π hπ
  exact virtual_frattini_count R (hQ ▸ cap) q hq hQ j
end Erdos1160.CentralLifts.Survival
end

/- CharacterDual -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
def JacobiDual (Q : Type*) [Group Q] : Subgroup (Second Q →* (Q →* C₂)) where
  carrier := {t | ∀ x y z : Q, t (secondBracket y z) x =
    t (secondBracket x z) y * (t (secondBracket x y) z)⁻¹}
  one_mem' := by intros _ _ _; change (1:C₂)=1*1⁻¹; simp
  mul_mem' := by
    intro a b ha hb x y z
    change a _ _*b _ _ = (a _ _*b _ _)*(a _ _*b _ _)⁻¹
    rw [ha x y z,hb x y z]
    simp only [mul_inv_rev,inv_inv]
    ac_rfl
  inv_mem' := by
    intro a ha x y z
    change (a _ _)⁻¹ = (a _ _)⁻¹*((a _ _)⁻¹)⁻¹
    rw [ha x y z]
    simp only [mul_inv_rev,inv_inv]
    ac_rfl
instance jacobiDualFinite (Q : Type*) [Group Q] [Finite Q] : Finite (JacobiDual Q) :=
  Finite.of_injective (fun t : JacobiDual Q => fun (w : Second Q) (x : Q) => t.val w x)
    (fun _ _ h => Subtype.ext (MonoidHom.ext fun w=>MonoidHom.ext fun x=>congrFun (congrFun h w) x))
variable {E Q : Type*} [Group E] [Group Q]
private theorem descent_character (f : E →* Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E)
    (mu : Third E →* C₂) :
    ∃ t : JacobiDual Q, ∀u v, t.val (secondMap f hf u) (f v) = mu (thirdBracket u v) := by
  let a := groupTensor hc mu
  have hzRight (w : Second E) : f.ker ≤ (a w).ker := by
    intro x hx
    change mu (thirdBracket w x)=1
    rw [show thirdBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp (hker hx) _)),map_one]
  have hzLeft : (secondMap f hf).ker ≤ a.ker := by
    intro w hw
    have hz : w.val ∈ Subgroup.center E := hker (show w.val ∈ f.ker from congrArg Subtype.val hw)
    apply MonoidHom.ext
    intro x
    change mu (thirdBracket w x)=1
    rw [show thirdBracket w x=1 from Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hz x).symm),map_one]
  obtain ⟨t,ht⟩ := descend_pair (secondMap f hf) (secondMap_surj f hf) f hf a hzLeft hzRight
  have hval (x y z : E) : t (secondBracket (f x) (f y)) (f z)=mu (triple x y z) := by
    rw [←secondMap_bracket f hf,ht];rfl
  refine ⟨⟨t,?_⟩,ht⟩
  intro x y z
  obtain ⟨x,rfl⟩ := hf x
  obtain ⟨y,rfl⟩ := hf y
  obtain ⟨z,rfl⟩ := hf z
  rw [hval,hval,hval,←map_inv,←map_mul]
  exact congrArg mu (Subtype.ext (triple_rearranged (fun a b c=>hc (triple a b c).property) x y z))
private theorem dual_ext {t u : JacobiDual Q} (f : E→*Q) (hf : Function.Surjective f)
    (h : ∀w x,t.val (secondMap f hf w) (f x)=u.val (secondMap f hf w) (f x)) : t=u := by
  apply Subtype.ext
  apply MonoidHom.ext
  intro w
  apply MonoidHom.ext
  intro x
  obtain ⟨w,rfl⟩ := secondMap_surj f hf w
  obtain ⟨x,rfl⟩ := hf x
  exact h w x
noncomputable def characterDual (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    (Third E →* C₂) →* JacobiDual Q where
  toFun mu := (descent_character f hf hker hc mu).choose
  map_one' := by
    apply dual_ext f hf
    intro w x
    exact (descent_character f hf hker hc 1).choose_spec w x
  map_mul' a b := by
    apply dual_ext f hf
    intro w x
    exact ((descent_character f hf hker hc (a*b)).choose_spec w x).trans (congrArg₂ (·*·)
      ((descent_character f hf hker hc a).choose_spec w x).symm
      ((descent_character f hf hker hc b).choose_spec w x).symm)
theorem characterDual_apply (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E)
    (mu : Third E →* C₂) (w : Second E) (x : E) :
    (characterDual f hf hker hc mu).val (secondMap f hf w) (f x) = mu (thirdBracket w x) :=
  (descent_character f hf hker hc mu).choose_spec _ _
theorem characterDual_injective (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    Function.Injective (characterDual f hf hker hc) := by
  intro a b h
  let K := a.eqLocus b
  let N := K.map (Third E).subtype
  have hcent : N ≤ Subgroup.center E := by rintro _ ⟨w,_,rfl⟩;exact hc w.property
  let _ : N.Normal := ⟨fun x hx y => by simpa [Subgroup.mem_center_iff.mp (hcent hx) y] using hx⟩
  have hg : Third E ≤ N := third_le_of_triples N (fun x y z=>by
    refine ⟨triple x y z,?_,rfl⟩
    change a (thirdBracket (secondBracket x y) z)=b (thirdBracket (secondBracket x y) z)
    rw [←characterDual_apply f hf hker hc,←characterDual_apply f hf hker hc,h])
  apply MonoidHom.ext
  intro w
  obtain ⟨u,hu,he⟩ := hg w.property
  have huw : u=w := Subtype.ext he
  exact huw ▸ (show a u=b u from hu)
theorem character_dual_card [Finite Q] (f : E→*Q) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center E) (hc : Third E ≤ Subgroup.center E) :
    Nat.card (Third E→* C₂) ≤ Nat.card (JacobiDual Q) :=
  Nat.card_le_card_of_injective _ (characterDual_injective f hf hker hc)
end Erdos1160.DeepJacobi
end

/- DualDimension -/
section
namespace Erdos1160.DeepJacobi
private theorem bit_mul_self (x : C₂) : x*x=1 := by
  change x.toAdd+x.toAdd=0
  exact (show ∀x : ZMod 2,x+x=0 by decide) _
instance jacobiDualModule (Q : Type*) [Group Q] : Module (ZMod 2) (Additive (JacobiDual Q)) :=
  AddCommGroup.zmodModule (fun u => by
    rw [two_nsmul]
    apply Subtype.ext
    apply MonoidHom.ext
    intro w
    apply MonoidHom.ext
    intro x
    apply bit_mul_self)
variable {E Q : Type*} [Group E] [Group Q]
theorem elementary_third_dimension [Finite E] [Finite Q]
    (f : E→*Q) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center E)
    (hc : Third E ≤ Subgroup.center E) {k : ℕ}
    (hs : ∀ w : Third E, w*w=1) (hsize : Nat.card (Third E)=2^k) :
    k ≤ Module.finrank (ZMod 2) (Additive (JacobiDual Q)) := by
  obtain ⟨i⟩ := Erdos1160Growth.LowerTriangularUpper.exist_elementary_coords hs hsize
  let dot (v : Fin k → ZMod 2) : Multiplicative (Fin k → ZMod 2) →* C₂ := {
    toFun := fun x => Multiplicative.ofAdd (∑j,v j*x.toAdd j)
    map_one' := by change (∑j,v j*0)=0; simp
    map_mul' := fun x y=>by
      change (∑j,v j*(x.toAdd j+y.toAdd j))=(∑j,v j*x.toAdd j)+(∑j,v j*y.toAdd j)
      simp [mul_add,Finset.sum_add_distrib] }
  let embed (v : Fin k → ZMod 2) : Third E →* C₂ := (dot v).comp i.toMonoidHom
  have ev (v : Fin k→ZMod 2) (j : Fin k) : embed v (i.symm (Multiplicative.ofAdd (Pi.single j 1))) =
      Multiplicative.ofAdd (v j) := by
    change (∑l : Fin k,v l * ((i (i.symm (Multiplicative.ofAdd (Pi.single j 1)))).toAdd l)) = _
    rw [i.apply_symm_apply]
    simp [Pi.single_apply, mul_ite]
    rfl
  have inj : Function.Injective embed := by
    intro v w h
    funext j
    have h' := congrArg (fun g : Third E →* C₂ => g (i.symm (Multiplicative.ofAdd (Pi.single j 1)))) h
    exact (ev v j).symm.trans (h'.trans (ev w j))
  let _ : Finite (Third E→*C₂) := Finite.of_injective (fun g : Third E→*C₂ => (g : Third E → C₂)) DFunLike.coe_injective
  have hcard : Nat.card (Fin k→ZMod 2) ≤ Nat.card (JacobiDual Q) := (Nat.card_le_card_of_injective _ inj).trans (character_dual_card f hf hker hc)
  let _ : Fintype (Additive (JacobiDual Q)) := Fintype.ofFinite _
  have hd := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive (JacobiDual Q))
  rw [←Nat.card_eq_fintype_card,ZMod.card] at hd
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [←hd]
  change 2^k ≤ Nat.card (JacobiDual Q)
  simpa only [Nat.card_fun,Nat.card_zmod,Nat.card_fin] using hcard
end Erdos1160.DeepJacobi
end

/- UniversalTwoCover -/
section
namespace Erdos1160.CentralLifts.Survival
variable {d : ℕ} {Q : Type} [Group Q] [Finite Q]
abbrev Adual (π : FreeGroup (Fin d) →* Q) := Module.Dual (ZMod 2) (Additive (RelCharacters π))
def evalHom (π : FreeGroup (Fin d) →* Q) : π.ker →* Multiplicative (Adual π) where
  toFun r := .ofAdd (relEval π r)
  map_one' := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    exact congrArg Multiplicative.toAdd (a.toMul.val.map_one)
  map_mul' r s := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    exact congrArg Multiplicative.toAdd (a.toMul.val.map_mul r s)
theorem eval_onto (π : FreeGroup (Fin d) →* Q) : Function.Surjective (evalHom π) := by
  let W : Submodule (ZMod 2) (Adual π) := {
    carrier := Set.range (relEval π)
    zero_mem' := ⟨1,congrArg Multiplicative.toAdd (evalHom π).map_one⟩
    add_mem' := by rintro _ _ ⟨r,rfl⟩ ⟨s,rfl⟩;exact ⟨r*s,congrArg Multiplicative.toAdd ((evalHom π).map_mul r s)⟩
    smul_mem' := by
      rintro k _ ⟨r,rfl⟩
      rcases (show ∀k:ZMod 2,k=0 ∨ k=1 by decide) k with rfl|rfl
      · rw [zero_smul];exact ⟨1,congrArg Multiplicative.toAdd (evalHom π).map_one⟩
      · rw [one_smul];exact ⟨r,rfl⟩ }
  have hz : W.dualCoannihilator=⊥ := by
    apply le_bot_iff.mp
    intro a ha
    apply relEval_separates π
    intro r
    exact (Submodule.mem_dualCoannihilator a).mp ha _ (show relEval π r∈W from ⟨r,rfl⟩)
  have htop : W=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hz] at h
    simpa using h
  intro b
  have hb : b.toAdd ∈ W := htop.ge Submodule.mem_top
  obtain ⟨r,hr⟩ := hb
  exact ⟨r,congrArg Multiplicative.ofAdd hr⟩
def universalKernel (π : FreeGroup (Fin d) →* Q) := (evalHom π).ker.map π.ker.subtype
instance (π : FreeGroup (Fin d) →* Q) : (universalKernel π).Normal where
  conj_mem := by
    rintro _ ⟨w,hw,rfl⟩ g
    refine ⟨conjugateRelation π g w,?_,rfl⟩
    change Multiplicative.ofAdd (relEval π (conjugateRelation π g w))=1
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro a
    have h := congrArg (fun v : Multiplicative (Adual π) => v.toAdd a)
      (show evalHom π w=1 from hw)
    exact (congrArg Multiplicative.toAdd (a.toMul.property g w)).trans h
abbrev Cover (π : FreeGroup (Fin d) →*Q) := FreeGroup (Fin d) ⧸ universalKernel π
def coverProjection (π : FreeGroup (Fin d) →*Q) : Cover π →*Q :=
  QuotientGroup.lift _ π (fun _ ⟨w,_,eq⟩ => eq ▸ w.property)
omit [Finite Q] in
lemma cover_onto (π : FreeGroup (Fin d) →*Q) (hπ : Function.Surjective π) :
    Function.Surjective (coverProjection π) := fun z => by
  obtain ⟨x,rfl⟩ := hπ z
  exact ⟨QuotientGroup.mk' _ x,rfl⟩
theorem cover_card (π : FreeGroup (Fin d) →*Q) (hπ : Function.Surjective π) :
    Nat.card (Cover π)=2^(relRank π)*Nat.card Q := by
  change Nat.card (FreeGroup (Fin d) ⧸ universalKernel π)=_
  rw [←Subgroup.index_eq_card,universalKernel,Subgroup.index_map_subtype,Subgroup.index_ker,Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (eval_onto π),MonoidHom.range_eq_top.mpr hπ,Subgroup.card_top,Subgroup.card_top]
  congr 1
  change Nat.card (Adual π)=_
  let _ : Finite (Adual π) := Finite.of_injective (fun f : Adual π => (f : _ → ZMod 2)) DFunLike.coe_injective
  let _ := Fintype.ofFinite (Adual π)
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := Adual π)
  rw [←Nat.card_eq_fintype_card,ZMod.card] at h
  simpa only [Adual,Subspace.dual_finrank_eq,relRank] using h
omit [Finite Q] in
theorem cover_central (π : FreeGroup (Fin d) →*Q) : (coverProjection π).ker ≤ Subgroup.center (Cover π) := by
  intro z hz
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (universalKernel π) z
  let w : π.ker := ⟨u,hz⟩
  apply Subgroup.mem_center_iff.mpr
  intro a
  obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (universalKernel π) a
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  apply (QuotientGroup.eq_one_iff _).mpr
  let g := conjugateRelation π v w * w⁻¹
  refine ⟨g,?_,rfl⟩
  change evalHom π g=1
  have h : evalHom π (conjugateRelation π v w)=evalHom π w := by
    apply Multiplicative.ofAdd.injective
    apply LinearMap.ext
    intro b
    exact congrArg Multiplicative.toAdd (b.toMul.property v w)
  rw [show g=conjugateRelation π v w*w⁻¹ from rfl,map_mul,map_inv,h,mul_inv_cancel]
omit [Finite Q] in
theorem cover_binary (π : FreeGroup (Fin d) →*Q) (v : (coverProjection π).ker) : v*v=1 := by
  apply Subtype.ext
  obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (universalKernel π) v.val
  have hz : π u=1 := by change coverProjection π (QuotientGroup.mk' (universalKernel π) u)=1;rw [hu];exact v.property
  change v.val*v.val=1
  rw [←hu,←map_mul]
  apply (QuotientGroup.eq_one_iff _).mpr
  let w : π.ker := ⟨u,hz⟩
  refine ⟨w*w,?_,rfl⟩
  change evalHom π (w*w)=1
  rw [map_mul]
  apply Multiplicative.ofAdd.injective
  apply LinearMap.ext
  intro a
  exact (show ∀x : ZMod 2,x+x=0 by decide) (relEval π w a)
end Erdos1160.CentralLifts.Survival
end

/- BinaryNucleus -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {d : ℕ} {Q : Type} [Group Q]
lemma derived_le_squares (U : Type*) [Group U] : Second U ≤ squareCore U := by
  apply Subgroup.commutator_le.mpr
  intro x _ y _
  have sq (z : U) : z*z∈squareCore U := Subgroup.subset_closure ⟨z,rfl⟩
  have he : ⁅x,y⁆=((x*x)*((x⁻¹*y)*(x⁻¹*y)))*(y⁻¹*y⁻¹) := by rw [commutatorElement_def];group
  rw [he]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (sq x) (sq (x⁻¹*y))) (sq y⁻¹)
end Erdos1160.CentralLifts.Survival
end

/- DerivedCriterion -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160.CentralLifts Erdos1160.CentralLifts.Survival
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {G Q : Type*} [Group G] [Group Q]
private def sq (D : Subgroup G) : Subgroup G :=
  Subgroup.closure (Set.range (fun x : D=>x.val*x.val))
private theorem sq_map (D : Subgroup G) (f : G→*Q) : (sq D).map f=sq (D.map f) := by
  rw [sq,MonoidHom.map_closure,sq]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨⟨f v.val,⟨v.val,v.property,rfl⟩⟩,(f.map_mul ..).symm⟩
  · rintro ⟨v,rfl⟩
    obtain ⟨y,hy,he⟩ := v.property
    exact ⟨y*y,⟨⟨y,hy⟩,rfl⟩,by rw [map_mul,he]⟩
private theorem sq_eq (D : Subgroup G) : (squareCore D).map D.subtype=sq D := by
  rw [squareCore,MonoidHom.map_closure,sq,←Set.range_comp]
  rfl
private theorem comm_mul_z {x z y : G} (hz : z∈Subgroup.center G) : ⁅x*z,y⁆=⁅x,y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz _).symm]
  simp
private theorem comm_z_mul {x z y : G} (hz : z∈Subgroup.center G) : ⁅x,y*z⁆=⁅x,y⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hz _)]
  simp
private theorem join_central (H N : Subgroup G) [N.Normal] (hz : N ≤ Subgroup.center G) :
    ⁅H⊔N,H⊔N⁆=⁅H,H⁆ := by
  refine le_antisymm (Subgroup.commutator_le.mpr ?_) (Subgroup.commutator_mono le_sup_left le_sup_left)
  intro x hx y hy
  obtain ⟨u,hu,v,hv,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨c,hc,b,hb,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  rw [comm_mul_z (hz hv),comm_z_mul (hz hb)]
  exact Subgroup.commutator_mem_commutator hu hc
private theorem central_step (H N : Subgroup G) [N.Normal] (hz : N ≤ Subgroup.center G)
    (htwo : ∀v∈N,v*v=1) (hD : commutator G≤ ⁅H,H⁆⊔N)
    (hgen : commutator G ≤ ⁅H,H⁆⊔ (⁅commutator G,⊤⁆ ⊔ sq (commutator G))) :
    commutator G≤⁅H,H⁆ := by
  let L := H⊔N
  letI : L.Normal := Subgroup.Normal.of_commutator_le G
    (hD.trans (sup_le_sup_right H.commutator_le_self N))
  letI : (⁅H,H⁆ : Subgroup G).Normal := (join_central H N hz) ▸ (inferInstance : (⁅L,L⁆ : Subgroup G).Normal)
  have hthird : ⁅commutator G,(⊤ : Subgroup G)⁆ ≤ ⁅H,H⁆ := by
    apply Subgroup.commutator_le.mpr
    intro x hx y _
    obtain ⟨u,hu,v,hv,rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hD hx)
    rw [comm_mul_z (hz hv)]
    exact Subgroup.commutator_top_right_le_iff.mpr inferInstance
      (Subgroup.commutator_mem_commutator hu (Subgroup.mem_top y))
  have hsquare : sq (commutator G)≤⁅H,H⁆ := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    obtain ⟨u,hu,v,hv,he⟩ := Subgroup.mem_sup_of_normal_right.mp (hD x.property)
    change x.val*x.val∈⁅H,H⁆
    rw [←he,←pow_two, (show Commute u v from Subgroup.mem_center_iff.mp (hz hv) _).mul_pow,
      pow_two v,htwo v hv,mul_one]
    exact Subgroup.pow_mem _ hu _
  exact hgen.trans (sup_le le_rfl (sup_le hthird hsquare))
private theorem derived_raw {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hc : Nat.card G=2^m) (H : Subgroup G)
    (hgen : commutator G ≤ ⁅H,H⁆⊔(⁅commutator G,⊤⁆⊔sq (commutator G))) :
    ⁅H,H⁆=commutator G := by
  induction m generalizing G with
  | zero =>
    let _ := (Nat.card_eq_one_iff_unique.mp (show Nat.card G=1 from hc)).1
    exact Subsingleton.elim _ _
  | succ m ih =>
    obtain ⟨j,hj,hcZ⟩ := IsPGroup.card_center_eq_prime_pow hc (Nat.succ_pos m)
    obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G:=Subgroup.center G) 2
      (hcZ ▸ dvd_pow_self _ (Nat.ne_of_gt hj))
    let u : G := t.val
    have hz : u ∈ Subgroup.center G := t.property
    have ho : orderOf u=2 := (Subgroup.orderOf_coe t).trans ht
    let N := Subgroup.zpowers u
    let _ : N.Normal := ⟨fun n hn g => by
      have h := Subgroup.mem_center_iff.mp ((Subgroup.zpowers_le.mpr hz) hn) g
      rwa [h,mul_inv_cancel_right]⟩
    let q := QuotientGroup.mk' N
    have top : (⊤ : Subgroup G).map q=⊤ := by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top];exact QuotientGroup.mk'_surjective _
    have der : (commutator G).map q=commutator (G⧸N) := by
      rw [commutator_def,Subgroup.map_commutator,top];rfl
    have lift := Subgroup.map_mono (f:=q) hgen
    simp only [Subgroup.map_sup,Subgroup.map_commutator,sq_map,der,top] at lift
    have hquot : Nat.card (G ⧸ N)=2^m := by
      have h := N.card_mul_index
      rw [Subgroup.index_eq_card,show Nat.card N=2 from (Nat.card_zpowers u).trans ho,
        hc,pow_succ'] at h
      omega
    have eq := ih hquot (H.map q) lift
    have le : (commutator G).map q ≤ (⁅H,H⁆ : Subgroup G).map q := by rw [der,Subgroup.map_commutator,eq]
    have hD := Subgroup.map_le_iff_le_comap.mp le
    rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at hD
    apply le_antisymm (Subgroup.commutator_mono le_top le_top)
    refine central_step H N (Subgroup.zpowers_le.mpr hz) ?_ hD hgen
    intro v hv
    let a : N := ⟨v,hv⟩
    have hcard : Nat.card N=2 := (Nat.card_zpowers u).trans ho
    have hh := pow_card_eq_one' (x:=a)
    rw [hcard,pow_two] at hh
    exact congrArg (fun w:N=>w.val) hh
theorem structural_derived {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    (H : Subgroup G) (hgen : commutator G ≤ (commutator H).map H.subtype ⊔
      (Third G ⊔ (squareCore (commutator G)).map (commutator G).subtype)) :
    (commutator H).map H.subtype=commutator G := by
  obtain ⟨m,hm⟩ := hG.exists_card_eq
  rw [Subgroup.map_subtype_commutator,sq_eq] at *
  exact derived_raw hm H hgen
end Erdos1160.Sims
end

/- StructuralThird -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi
theorem structural_third {G : Type*} [Group G] (H : Subgroup G)
    (hh : (commutator H).map H.subtype=commutator G) :
    (Third H).map H.subtype=Third G := by
  rw [Subgroup.map_subtype_commutator] at hh
  letI : H.Normal := Subgroup.Normal.of_commutator_le G (hh ▸ H.commutator_le_self)
  let K : Subgroup G := ⁅⁅H,H⁆,H⁆
  change ((⊤ : Subgroup H).lowerCentralSeries 2).map H.subtype=_
  rw [Subgroup.map_lowerCentralSeries,←MonoidHom.range_eq_map,H.range_subtype]
  change K=⁅commutator G,⊤⁆
  refine le_antisymm (Subgroup.commutator_mono hh.le le_top) ?_
  let q := QuotientGroup.mk' K
  let U := H.map q
  have qt : (⊤ : Subgroup G).map q=⊤ := by
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have nil : ⁅⁅U,U⁆,U⁆=⊥ := by
    change ⁅⁅H.map q,H.map q⁆,H.map q⁆=⊥
    rw [←Subgroup.map_commutator,←Subgroup.map_commutator]
    apply (Subgroup.map_eq_bot_iff _).mpr
    exact (QuotientGroup.ker_mk' K).ge
  have der : commutator (G⧸K)=⁅U,U⁆ := by
    have h := congrArg (Subgroup.map q) hh
    rwa [commutator_def,Subgroup.map_commutator,Subgroup.map_commutator,qt,eq_comm] at h
  have left : ⁅U,⊤⁆ ≤ ⁅U,U⁆ := (Subgroup.commutator_mono le_top le_rfl :
    ⁅U,⊤⁆ ≤ commutator (G⧸K)).trans der.le
  have right : ⁅⊤,U⁆≤⁅U,U⁆ := (Subgroup.commutator_comm ..).le.trans left
  have z : ⁅⁅U,U⁆,(⊤ : Subgroup (G⧸K))⁆=⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate
    (eq_bot_iff.mpr ((Subgroup.commutator_mono left le_rfl).trans nil.le))
    (eq_bot_iff.mpr ((Subgroup.commutator_mono right le_rfl).trans nil.le))
  apply (show ⁅commutator G,⊤⁆≤q.ker → ⁅commutator G,⊤⁆≤K from fun h=>h.trans (QuotientGroup.ker_mk' K).le)
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [←hh,Subgroup.map_commutator,Subgroup.map_commutator,qt]
  exact z
end Erdos1160.Sims
end

/- OrbitUp -/
section
namespace OrbitUp
open scoped BigOperators Matrix
abbrev K := ZMod 2
abbrev V (d : ℕ) := Fin d → K
def basis {d : ℕ} (i : Fin d) : V d := Pi.single i 1
end OrbitUp
end

/- RectangleRank -/
section
namespace OrbitUp
theorem count_small_rank_matrices (d t r : ℕ) :
    Nat.card {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r} ≤ 2^(r*(d+t)) := by
  classical
  let _ (p q : ℕ) : Finite (V p →ₗ[K] V q) :=
    Finite.of_equiv (Matrix (Fin q) (Fin p) K) LinearMap.toMatrix'.symm.toEquiv
  have card (p q : ℕ) : Nat.card (V p →ₗ[K] V q) = 2^(p*q) := by
    rw [Nat.card_congr (LinearMap.toMatrix' : (V p →ₗ[K] V q) ≃ₗ[K] Matrix (Fin q) (Fin p) K).toEquiv]
    change Nat.card (Fin q → Fin p → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_fin, Nat.card_zmod, pow_mul]
  let S := {A : Matrix (Fin d) (Fin t) K // A.rank ≤ r}
  let f (A : S) := A.val.mulVecLin
  have fac (A : S) : ∃ z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d), z.2.comp z.1 = f A := by
    have hdim : Module.finrank K (LinearMap.range (f A)) ≤ Module.finrank K (V r) := by
      rw [Module.finrank_fin_fun]; exact A.property
    obtain ⟨i, hi⟩ := finrank_le_iff_exists_linearMap.mp hdim
    obtain ⟨p, hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
    refine ⟨⟨i.comp (f A).rangeRestrict, (f A).range.subtype.comp p⟩, ?_⟩
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun hp ((f A).rangeRestrict x))
  let code (A : S) := (fac A).choose
  have hi : Function.Injective code := by
    intro A B h
    have he : f A = f B := (fac A).choose_spec.symm.trans
      ((congrArg (fun z : (V t →ₗ[K] V r) × (V r →ₗ[K] V d) => z.2.comp z.1) h).trans (fac B).choose_spec)
    apply Subtype.ext
    exact Matrix.toLin'.injective (by simpa only [Matrix.toLin'_apply'] using he)
  calc
    _ ≤ Nat.card ((V t →ₗ[K] V r) × (V r →ₗ[K] V d)) := Nat.card_le_card_of_injective code hi
    _ = _ := by rw [Nat.card_prod,card,card,←pow_add]; congr 1; ring
end OrbitUp
end

/- HyperplaneForms -/
section
namespace OrbitUp.BoundedMatrices
variable {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
private lemma binary_sum (x : K) : x+x=0 := (show ∀x:K,x+x=0 by decide) x
private lemma scalar_sym (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0) (x y : U) : A y x=A x y := by
  have eq := alt (x+y)
  simp only [map_add,LinearMap.add_apply,alt,zero_add,add_zero] at eq
  have check : ∀u v:K,u+v=0→u=v := by decide
  exact check _ _ eq
theorem hyperplane_formula (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0) (l : U→ₗ[K] K) (hl : l≠0)
    (null : ∀x y : U,l x=0→l y=0→A x y=0) (u v : U) (huv : A u v=1) (x : U) :
    l x=l u*A x v+l v*A u x := by
  have ex : ∃w,l w≠0 := by simpa only [ne_eq,LinearMap.ext_iff,LinearMap.zero_apply,not_forall] using hl
  obtain ⟨w,hw⟩ := ex
  have lw : l w=1 := by rcases (show ∀a:K,a=0 ∨ a=1 by decide) (l w) with h|h <;> tauto
  have kills (y : U) : l (y+l y • w)=0 := by simp [map_add,map_smul,lw,binary_sum]
  have det (x y : U) : A x y=l x*A w y+l y*A x w := by
    have h := null _ _ (kills x) (kills y)
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul,alt w,mul_zero,add_zero] at h
    have e : ∀a b c:K,a+b+c=0→a=b+c := by decide
    exact e _ _ _ h
  calc l x = l x * A u v := (mul_one _).symm.trans (congrArg (l x * ·) huv.symm)
       _ = l u*A x v+l v*A u x := by
         rw [det u v,det x v,det u x,scalar_sym A alt w x]
         ring_nf <;> simp [show (2:K)=0 by decide]
theorem alternating_hyperplanes (A : U→ₗ[K] U→ₗ[K] K) (alt : ∀u,A u u=0)
    (u v : U) (huv : A u v=1) :
    Nat.card {l : U→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→A x y=0}≤3 := by
  classical
  let T := {l : U→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→A x y=0}
  let P := {p : K×K // p≠0}
  let c (l:T) : P := ⟨(l.val u,l.val v),fun zero=>by
    have h := l.property.2 _ _ (congrArg Prod.fst zero) (congrArg Prod.snd zero)
    exact one_ne_zero (huv.symm.trans h)⟩
  have inj : Function.Injective c := by
    intro a b eq
    apply Subtype.ext;apply LinearMap.ext;intro x
    rw [hyperplane_formula A alt _ a.property.1 a.property.2 u v huv x,
        hyperplane_formula A alt _ b.property.1 b.property.2 u v huv x]
    rw [show a.val u=b.val u from congrArg (fun p:P=>p.val.1) eq,
        show a.val v=b.val v from congrArg (fun p:P=>p.val.2) eq]
  have h := Nat.card_le_card_of_injective c inj
  exact h.trans (by rw [Nat.card_eq_fintype_card]; decide)
end OrbitUp.BoundedMatrices
end

/- MinimalPolar -/
section
namespace OrbitUp.BoundedMatrices
variable {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
def valuesOn (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) : Submodule K W :=
  Submodule.span K (Set.range (fun z : S×S=>β z.1.val z.2.val))
private def tested (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) (z : W→ₗ[K] K) : S→ₗ[K] S→ₗ[K] K where
  toFun x := z.comp ((β x.val).comp S.subtype)
  map_add' a b := by ext y;change z (β (a.val+b.val) y.val)=_;simp
  map_smul' a b := by ext y;change z (β (a • b.val) y.val)=_;simp
private theorem dual_card_ne (W : Type) [AddCommGroup W] [Module K W] [Finite W] :
    Nat.card {z : W→ₗ[K] K // z≠0}=2^Module.finrank K W-1 := by
  classical
  letI : Finite (W→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI := Fintype.ofFinite (W→ₗ[K] K)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl,
    ←Nat.card_eq_fintype_card,Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod,Subspace.dual_finrank_eq]
  simp
theorem minimal_commutator_span [Finite U] [Finite W] (β : U→ₗ[K] U→ₗ[K] W)
    (alt : ∀u,β u u=0) (spans : valuesOn β ⊤=⊤) :
    ∃S : Submodule K U,valuesOn β S=⊤ ∧ Module.finrank K S ≤ Module.finrank K W+1 := by
  classical
  let P (n : ℕ) := ∃ S : Submodule K U, valuesOn β S=⊤ ∧ Module.finrank K S=n
  have ex : ∃n,P n := ⟨_,⊤,spans,rfl⟩
  obtain ⟨S,hS,rank⟩ := Nat.find_spec ex
  refine ⟨S,hS,?_⟩
  letI : Finite (S→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (W→ₗ[K] K) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  let A := {a : S→ₗ[K] K // a≠0}
  let B := {b : W→ₗ[K] K // b≠0}
  have pick (l : A) : ∃z:B, ∀x y:S,l.val x=0→l.val y=0→tested β S z.val x y=0 := by
    let H := l.val.ker
    let D := H.map S.subtype
    have sm : Module.finrank K D < Module.finrank K S := by
      rw [←(Submodule.equivMapOfInjective S.subtype S.subtype_injective H).finrank_eq]
      have proper : H<⊤ := lt_top_iff_ne_top.mpr (fun h=>l.property (LinearMap.ker_eq_top.mp h))
      exact (Submodule.finrank_lt_finrank_of_lt proper).trans_eq (finrank_top K S)
    have miss : valuesOn β D ≠ ⊤ := fun e=>by
      have low := Nat.find_min' ex (show P (Module.finrank K D) from ⟨D,e,rfl⟩)
      omega
    obtain ⟨z,hz,hker⟩ := (valuesOn β D).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr miss)
    refine ⟨⟨z,hz⟩,fun x y hx hy=>?_⟩
    exact hker (Submodule.subset_span ⟨(⟨x.val,⟨x,hx,rfl⟩⟩,⟨y.val,⟨y,hy,rfl⟩⟩),rfl⟩)
  choose select hselect using pick
  have pairs (z : B) : ∃u v:S,tested β S z.val u v=1 := by
    by_contra! hn
    have hv : ∀u v:S,z.val (β u.val v.val)=0 := fun u v=>by
      rcases (show ∀a:K,a=0 ∨ a=1 by decide) (z.val (β u.val v.val)) with h|h
      · exact h
      · exact False.elim (hn u v h)
    have hz : valuesOn β S ≤ z.val.ker := Submodule.span_le.mpr (by rintro _ ⟨⟨x,y⟩,rfl⟩;exact hv x y)
    rw [hS] at hz
    exact z.property (LinearMap.ker_eq_top.mp (top_le_iff.mp hz))
  have count := Erdos1160.PresentationCount.card_le_of_fiber_bound select 3 (by
    intro z
    obtain ⟨u,v,huv⟩ := pairs z
    let T := {l : S→ₗ[K] K // l≠0 ∧ ∀x y,l x=0→l y=0→tested β S z.val x y=0}
    let m (x : {l : A // select l=z}) : T := ⟨x.val.val,x.val.property,by have h := hselect x.val;rw [x.property] at h;exact h⟩
    have low := Nat.card_le_card_of_injective m (fun x y eq=>Subtype.ext (Subtype.ext (congrArg (fun a:T=>a.val) eq)))
    exact low.trans (alternating_hyperplanes (tested β S z.val) (fun x=>by change z.val (β x.val x.val)=0;rw [alt,map_zero]) u v huv))
  change Nat.card {l : S→ₗ[K] K // l≠0}≤Nat.card {z : W→ₗ[K] K // z≠0}*3 at count
  rw [dual_card_ne,dual_card_ne] at count
  by_contra! g
  have cmp := Nat.pow_le_pow_right (n:=2) (by decide) (show Module.finrank K W+2 ≤ Module.finrank K S by omega)
  rw [pow_add] at cmp
  have := Nat.two_pow_pos (Module.finrank K W)
  omega
end OrbitUp.BoundedMatrices
end

/- SampleBilinear -/
section
namespace OrbitUp.MinSpan
variable {d h k : ℕ}
abbrev Sample (d h : ℕ) := Fin h→V d
noncomputable def sampleRows (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) : Submodule K (Module.Dual K (V d)) :=
  Submodule.span K (Set.range (fun i=>A (x i)))
theorem sample_card (d h : ℕ) : Nat.card (Sample d h)=2^(d*h) := by
  simp only [Sample,V,Nat.card_fun,Nat.card_fin,Nat.card_zmod,pow_mul]
private theorem rank_span_in_image (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) :
    Module.finrank K (Submodule.span K (Set.range (fun i=>A.rangeRestrict (x i))))=Module.finrank K (sampleRows A x) := by
  let T := Submodule.span K (Set.range (fun i=>A.rangeRestrict (x i)))
  have eq : T.map A.range.subtype=sampleRows A x := by
    simp only [T,Submodule.map_span,←Set.range_comp]
    rfl
  exact (Submodule.equivMapOfInjective A.range.subtype A.range.subtype_injective T).finrank_eq.trans (congrArg (fun S : Submodule K (Module.Dual K (V d))=>Module.finrank K S) eq)
theorem low_samples (A : V d→ₗ[K] Module.Dual K (V d)) (h k : ℕ) :
    let r:=Module.finrank K A.range
    Nat.card {x : Sample d h // Module.finrank K (sampleRows A x) ≤ k} ≤
      2^(k*(r+h)+(Module.finrank K A.ker)*h) := by
  classical
  let R := A.range
  let X := {x : Sample d h // Module.finrank K (sampleRows A x) ≤ k}
  let C := (V k→ₗ[K] R) × Sample k h × (Fin h→A.ker)
  let lift : R→V d := Function.surjInv A.surjective_rangeRestrict
  have liftOk (w : R) : A (lift w)=w.val := congrArg Subtype.val (Function.rightInverse_surjInv A.surjective_rangeRestrict w)
  have fac (x : X) : ∃p:C,∀i,x.val i=lift (p.1 (p.2.1 i))+(p.2.2 i).val := by
    let T := Submodule.span K (Set.range (fun i=>A.rangeRestrict (x.val i)))
    have dim : Module.finrank K T ≤ Module.finrank K (V k) := by
      rw [Module.finrank_fin_fun];exact (rank_span_in_image A x.val).le.trans x.property
    obtain ⟨f,hf⟩ := finrank_le_iff_exists_linearMap.mp dim
    obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
    let xi (i : Fin h) : T := ⟨A.rangeRestrict (x.val i),Submodule.subset_span ⟨i,rfl⟩⟩
    have ok (i) : T.subtype (g (f (xi i))) = A.rangeRestrict (x.val i) := congrArg Subtype.val (DFunLike.congr_fun hg (xi i))
    let z (i) : A.ker := ⟨x.val i-lift (A.rangeRestrict (x.val i)),by rw [LinearMap.mem_ker,map_sub,liftOk,sub_eq_zero];rfl⟩
    exact ⟨(T.subtype.comp g,fun i=>f (xi i),z),fun i=>by simp only [LinearMap.comp_apply,ok,z];abel⟩
  choose c hc using fac
  have inj : Function.Injective c := by
    intro x y e
    exact Subtype.ext (funext fun i=>(hc x i).trans ((congrArg (fun p:C=>lift (p.1 (p.2.1 i))+(p.2.2 i).val) e).trans (hc y i).symm))
  letI : Finite (Module.Dual K (V d)) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (V k→ₗ[K] R) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have bd := Nat.card_le_card_of_injective c inj
  have cover : Nat.card C=2^(k*(Module.finrank K R+h)+Module.finrank K A.ker*h) := by
    simp only [C,Nat.card_prod,sample_card,Nat.card_fun,Nat.card_fin,Module.natCard_eq_pow_finrank (K:=K) (V:=A.ker),Module.natCard_eq_pow_finrank (K:=K) (V:=V k→ₗ[K] R),Nat.card_zmod,
      Module.finrank_linearMap,Module.finrank_fin_fun,←pow_mul,←pow_add]
    congr 1;ring
  exact bd.trans cover.le
theorem high_fiber (A : V d→ₗ[K] Module.Dual K (V d)) (x : Sample d h) (high : k ≤ Module.finrank K (sampleRows A x)) :
    Nat.card {y:Sample d h // ∀i j,A (x i) (y j)=0}≤2^((d-k)*h) := by
  classical
  let T := sampleRows A x
  let C := T.dualCoannihilator
  let X := {y:Sample d h // ∀i j,A (x i) (y j)=0}
  let into (y:X) (j : Fin h) : C := ⟨y.val j,by
    rw [Submodule.mem_dualCoannihilator]
    intro l hl
    let g := Module.Dual.eval K (V d) (y.val j)
    have le : T ≤ g.ker := Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩;exact y.property i j)
    exact le hl⟩
  have inj : Function.Injective into := fun x y e=>Subtype.ext (funext (fun j=>congrArg Subtype.val (congrFun e j)))
  have cap := Subspace.finrank_add_finrank_dualCoannihilator_eq T
  rw [Module.finrank_fin_fun] at cap
  change Module.finrank K T+Module.finrank K C=d at cap
  change k ≤ Module.finrank K T at high
  have bd := Nat.card_le_card_of_injective into inj
  rw [Nat.card_fun,Nat.card_fin,Module.natCard_eq_pow_finrank (K:=K) (V:=C),Nat.card_zmod,←pow_mul] at bd
  exact bd.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right h (by omega)))
end OrbitUp.MinSpan
end

/- SimultaneousSample -/
section
namespace OrbitUp.MinSpan
open scoped BigOperators
abbrev SamplePair (d k : ℕ) := Sample d (2*k) × Sample d (2*k)
def vanishes {d k : ℕ} (A : V d→ₗ[K] Module.Dual K (V d)) (z : SamplePair d k) : Prop := ∀i j,A (z.1 i) (z.2 j)=0
private theorem finiteUnion {X I : Type} [Finite X] [Fintype I] (p : I→X→Prop) :
    Nat.card {x:X // ∃i,p i x}≤∑i : I,Nat.card {x:X // p i x} := by
  classical
  choose f hf using fun x:{x:X // ∃i,p i x}=>x.property
  let g (x : {x:X // ∃i,p i x}) : (i : I) × {x:X // p i x} := ⟨f x,x.val,hf x⟩
  have inj : Function.Injective g := fun x y e=>Subtype.ext (congrArg (fun z : (i : I) × {x:X // p i x}=>z.2.val) e)
  exact (Nat.card_le_card_of_injective g inj).trans_eq Nat.card_sigma
theorem pair_sample_bound {d k : ℕ} (A : V d→ₗ[K] Module.Dual K (V d))
    (big : 4*k ≤ Module.finrank K A.range) :
    Nat.card {z:SamplePair d k // vanishes A z}*2^(2*k*k) ≤ 2*Nat.card (SamplePair d k) := by
  classical
  let h := 2*k
  let r := Module.finrank K A.range
  let n := Module.finrank K A.ker
  have size : r+n=d := (LinearMap.finrank_range_add_finrank_ker A).trans (Module.finrank_fin_fun K)
  let low (x : Sample d h) := Module.finrank K (sampleRows A x) ≤ k
  let L := {x : Sample d h // low x}
  let H := {x : Sample d h // ¬low x}
  let Z := {z : SamplePair d k // vanishes A z}
  let Y (x : H) := {y : Sample d h // ∀i j,A (x.val i) (y j)=0}
  let C := (L × Sample d h) ⊕ ((x : H) × Y x)
  let enc (z:Z) : C := if m:low z.val.1 then .inl (⟨z.val.1,m⟩,z.val.2)
    else .inr ⟨⟨z.val.1,m⟩,⟨z.val.2,z.property⟩⟩
  let dec : C→SamplePair d k := Sum.elim (fun x=>(x.1.val,x.2)) (fun x=>(x.1.val,x.2.val))
  have left (z : Z) : dec (enc z)=z.val := by by_cases m:low z.val.1 <;> simp [enc,dec,m]
  have cut := Nat.card_le_card_of_injective enc (fun x y e=>Subtype.ext ((left x).symm.trans ((congrArg dec e).trans (left y))))
  have hlow : Nat.card L ≤ 2^(k*(r+h)+n*h) := low_samples A h k
  letI := Fintype.ofFinite H
  have hi : Nat.card ((x : H) × Y x) ≤ 2^(d*h)*2^((d-k)*h) := by
    rw [Nat.card_sigma]
    calc _ ≤ ∑_x : H,2^((d-k)*h) := Finset.sum_le_sum (fun x _=>high_fiber A x.val (by have := x.property;unfold low at this;omega))
         _ = Nat.card H*2^((d-k)*h) := by simp [←Nat.card_eq_fintype_card]
         _ ≤ _ := Nat.mul_le_mul_right _ ((Nat.card_le_card_of_injective (fun x:H=>x.val) Subtype.val_injective).trans_eq (sample_card d h))
  change Nat.card Z*_≤_
  apply (Nat.mul_le_mul_right _ cut).trans
  change (Nat.card ((L × Sample d h) ⊕ ((x:H)×Y x)))*_≤_
  rw [Nat.card_sum,Nat.card_prod,sample_card,Nat.add_mul]
  change _ ≤ 2*(Nat.card (Sample d h × Sample d h))
  rw [Nat.card_prod,sample_card]
  conv_rhs => rw [two_mul]
  apply Nat.add_le_add
  · grw [hlow]
    rw [←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change 4*k ≤ r at big
    dsimp [h];nlinarith only [Nat.mul_le_mul_right k big,congrArg (·*(2*k)) size]
  · grw [hi]
    rw [←pow_add,←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have kLe : k ≤ d := by change 4*k ≤ r at big;omega
    have e := Nat.sub_add_cancel kLe
    dsimp [h];nlinarith only [congrArg (·*(2*k)) e]
theorem simultaneous_nonvanish {d k b : ℕ} {I : Type} [Fintype I]
    (A : I→V d→ₗ[K] Module.Dual K (V d)) (hI : Nat.card I ≤ 2^b) (budget : b+1 < 2*k*k) :
    ∃z : SamplePair d k,∀i,4*k ≤ Module.finrank K (A i).range→¬vanishes (A i) z := by
  classical
  let H := {i : I // 4*k ≤ Module.finrank K (A i).range}
  let X := SamplePair d k
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>pair_sample_bound (A (i:H).val) i.property)
  rw [←Finset.sum_mul] at sum
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,smul_eq_mul] at sum
  by_contra! fail
  have hit (x:X) : ∃i:H,vanishes (A i.val) x := by obtain ⟨i,hi,h⟩ := fail x;exact ⟨⟨i,hi⟩,h⟩
  have card := finiteUnion (X:=X) (fun i:H=>vanishes (k:=k) (A i.val))
  have all : Nat.card X ≤ Nat.card {x:X // ∃i:H,vanishes (A i.val) x} :=
    Nat.card_le_card_of_injective (fun x:X=>⟨x,hit x⟩) (fun _ _ e=>congrArg Subtype.val e)
  have lim := (Nat.mul_le_mul_right _ (all.trans card)).trans sum
  change Nat.card X*2^(2*k*k) ≤ Nat.card H*(2*Nat.card X) at lim
  have hc : Nat.card H ≤ 2^b := (Nat.card_le_card_of_injective (fun x:H=>x.val) Subtype.val_injective).trans hI
  have avoid : 2^b*2 < 2^(2*k*k) := by rw [←pow_succ];exact Nat.pow_lt_pow_right (by decide) budget
  have := Nat.mul_lt_mul_of_pos_right ((Nat.mul_le_mul_right _ hc).trans_lt avoid) (Nat.card_pos (α:=X))
  nlinarith only [lim,this]
end OrbitUp.MinSpan
end

/- AlternatingMinSpan -/
section
namespace OrbitUp.MinSpan
open BoundedMatrices
abbrev Tensor (d b : ℕ) := V d→ₗ[K] V d→ₗ[K] V b
def minimalAlternating (d b σ : ℕ) := {β : Tensor d b //
    (∀x,β x x=0) ∧ valuesOn β ⊤=⊤ ∧ (∃S,valuesOn β S=⊤ ∧ Module.finrank K S=σ) ∧
    ∀S,valuesOn β S=⊤→σ ≤ Module.finrank K S}
def push {U W Z : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z] (f : W→ₗ[K] Z) (β : U→ₗ[K] U→ₗ[K] W) : U→ₗ[K] U→ₗ[K] Z where
  toFun x := f.comp (β x)
  map_add' x y := LinearMap.ext (fun z=>by change f (β (x+y) z)=_;rw [map_add,LinearMap.add_apply,map_add];rfl)
  map_smul' c x := LinearMap.ext (fun z=>by change f (β (c • x) z)=_;rw [map_smul,LinearMap.smul_apply,map_smul];rfl)
theorem push_values {U W Z : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    [AddCommGroup Z] [Module K Z] (f : W→ₗ[K] Z) (β : U→ₗ[K] U→ₗ[K] W) (S : Submodule K U) :
    valuesOn (push f β) S=(valuesOn β S).map f := by
  simp only [valuesOn,Submodule.map_span,←Set.range_comp];rfl
theorem values_mono {U W : Type} [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W]
    (β : U→ₗ[K] U→ₗ[K] W) {S T : Submodule K U} (h : S ≤ T) : valuesOn β S ≤ valuesOn β T := by
  apply Submodule.span_mono
  rintro _ ⟨⟨x,y⟩,rfl⟩
  exact ⟨(⟨x.val,h x.property⟩,⟨y.val,h y.property⟩),rfl⟩
theorem complete_sample {d b σ : ℕ} (β : minimalAlternating d b σ) (S : Submodule K (V d)) :
    σ ≤ Module.finrank K S+Module.finrank K (valuesOn β.val S).dualAnnihilator+1 := by
  classical
  let T := valuesOn β.val S
  let q := T.mkQ
  let A := push q β.val
  have ha (x) : A x x=0 := by change q (β.val x x)=0;rw [β.property.1,map_zero]
  have full : valuesOn A ⊤=⊤ := by
    rw [push_values,β.property.2.1,Submodule.map_top,LinearMap.range_eq_top]
    exact T.mkQ_surjective
  letI : Finite (V b ⧸ T) := Finite.of_surjective _ T.mkQ_surjective
  obtain ⟨U,hu,dim⟩ := minimal_commutator_span A ha full
  let P := valuesOn β.val (S⊔U)
  have whole : P=⊤ := by
    have incl : T ≤ P := values_mono _ le_sup_left
    have un : (valuesOn β.val U).map q=⊤ := (push_values q β.val U).symm.trans hu
    have im : P.map q=⊤ := top_unique (un.ge.trans (Submodule.map_mono (values_mono _ le_sup_right)))
    have pre := congrArg (Submodule.comap q) im
    rwa [Submodule.comap_map_eq,Submodule.ker_mkQ,sup_eq_left.mpr incl,Submodule.comap_top] at pre
  have min := β.property.2.2.2 _ whole
  have plus := Submodule.finrank_sup_add_finrank_inf_eq S U
  have quo : Module.finrank K (V b ⧸ T)=Module.finrank K T.dualAnnihilator := (Subspace.quotEquivAnnihilator T).finrank_eq
  change Module.finrank K U ≤ Module.finrank K (V b ⧸ T)+1 at dim
  rw [quo] at dim
  change σ ≤ Module.finrank K S+Module.finrank K T.dualAnnihilator+1
  omega
theorem many_low_rank_components {d b σ k : ℕ} (β : minimalAlternating d b σ)
    (budget : b+1 < 2*k*k) :
    ∃ T : Submodule K (Module.Dual K (V b)),
      σ ≤ 4*k+Module.finrank K T+1 ∧ ∀f∈T,Module.finrank K (push f β.val).range < 4*k := by
  classical
  letI : Finite (Module.Dual K (V b)) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI := Fintype.ofFinite (Module.Dual K (V b))
  have card : Nat.card (Module.Dual K (V b))=2^b := by rw [Module.natCard_eq_pow_finrank (K:=K),Subspace.dual_finrank_eq,Module.finrank_fin_fun,Nat.card_zmod]
  obtain ⟨z,hz⟩ := simultaneous_nonvanish (d:=d) (fun f:Module.Dual K (V b)=>push f β.val) card.le budget
  let S₁ := Submodule.span K (Set.range z.1)
  let S₂ := Submodule.span K (Set.range z.2)
  let S := S₁⊔S₂
  let T := valuesOn β.val S
  have h₁ : Module.finrank K S₁ ≤ 2*k := (finrank_range_le_card _).trans_eq (Fintype.card_fin _)
  have h₂ : Module.finrank K S₂ ≤ 2*k := (finrank_range_le_card _).trans_eq (Fintype.card_fin _)
  have hS : Module.finrank K S ≤ 4*k := by have h := Submodule.finrank_sup_add_finrank_inf_eq S₁ S₂;change Module.finrank K (S₁⊔S₂ : Submodule K (V d)) ≤ 4*k;omega
  have complete := complete_sample β S
  change σ ≤ Module.finrank K S+Module.finrank K T.dualAnnihilator+1 at complete
  refine ⟨T.dualAnnihilator,by change σ ≤ 4*k+Module.finrank K T.dualAnnihilator+1;omega,fun f hf=>?_⟩
  by_contra! big
  apply hz f big
  intro i j
  change f (β.val (z.1 i) (z.2 j))=0
  apply (T.mem_dualAnnihilator f).mp hf
  exact Submodule.subset_span ⟨(⟨z.1 i,(show S₁ ≤ S from le_sup_left) (Submodule.subset_span ⟨i,rfl⟩)⟩,
    ⟨z.2 j,(show S₂ ≤ S from le_sup_right) (Submodule.subset_span ⟨j,rfl⟩)⟩),rfl⟩
end OrbitUp.MinSpan
end

/- CommutatorHead -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
def commutatorTail (G : Type*) [Group G] : Subgroup G :=
  Third G ⊔ (squareCore (commutator G)).map (commutator G).subtype
variable {G J : Type*} [Group G] [Group J]
theorem commutatorTail_le_derived (G : Type*) [Group G] : commutatorTail G ≤ commutator G := by
  refine sup_le ?_ ?_
  · exact Subgroup.commutator_le_left (commutator G) ⊤
  · rintro _ ⟨w,_,rfl⟩;exact w.property
theorem commutatorTail_map_of_parts (f : G→*J) (h₂ : (commutator G).map f=commutator J)
    (h₃ : (Third G).map f=Third J) : (commutatorTail G).map f=commutatorTail J := by
  let a := (f.comp (commutator G).subtype).codRestrict (commutator J) (fun w=>h₂ ▸
    (show f w.val∈(commutator G).map f from ⟨w.val,w.property,rfl⟩))
  have onto : Function.Surjective a := by
    intro w
    obtain ⟨v,hv,he⟩ := h₂.ge w.property
    exact ⟨⟨v,hv⟩,Subtype.ext he⟩
  rw [commutatorTail,commutatorTail,Subgroup.map_sup,h₃,Subgroup.map_map,←CentralKernelCount.squareCore_map a onto,Subgroup.map_map]
  rfl
theorem commutatorTail_map (f : G→*J) (hf : Function.Surjective f) :
    (commutatorTail G).map f=commutatorTail J :=
  commutatorTail_map_of_parts f (lower_map_top f hf 1) (lower_map_top f hf 2)
instance (G : Type*) [Group G] : (commutatorTail G).Characteristic :=
  Subgroup.characteristic_iff_map_le.mpr fun e=>(commutatorTail_map e.toMonoidHom e.surjective).le
theorem subgroup_tail_eq (H : Subgroup G) (hh : (commutator H).map H.subtype=commutator G) :
    (commutatorTail H).map H.subtype=commutatorTail G :=
  commutatorTail_map_of_parts _ hh (structural_third H hh)
theorem head_conditions (G : Type*) [Group G] :
    let Q := G ⧸ commutatorTail G
    Second Q ≤ Subgroup.center Q ∧ ∀w:Second Q,w*w=1 := by
  let q := QuotientGroup.mk' (commutatorTail G)
  have sq := QuotientGroup.mk'_surjective (commutatorTail G)
  have van : (commutatorTail G).map q=⊥ := (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' _).ge
  rw [commutatorTail_map q sq] at van
  refine ⟨?_,?_⟩
  · intro w hw
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp (van ▸
      ((show Third _ ≤ commutatorTail (G⧸commutatorTail G) from le_sup_left) (show ⁅w,x⁆∈Third (G⧸commutatorTail G) from Subgroup.commutator_mem_commutator hw (Subgroup.mem_top x)) :
        ⁅w,x⁆∈commutatorTail (G⧸commutatorTail G))))).symm
  · intro w
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [←van]
    apply (show (squareCore (Second (G⧸commutatorTail G))).map (Second _).subtype ≤ commutatorTail _ from le_sup_right)
    exact ⟨w*w,Subgroup.subset_closure ⟨w,rfl⟩,rfl⟩
end Erdos1160.Sims
end

/- ThirdComparison -/
section
namespace CentralKernelCount
open scoped commutatorElement
theorem paired_of_order {E F : Type*} [Group E] [Group F] [Finite E] [Finite F] {d : ℕ}
    (T : Subgroup (E×F)) (x : Fin d → E×F)
    (genE : adjoin (T.map (MonoidHom.fst E F)) (fun i => (x i).1)=⊤)
    (genF : adjoin (T.map (MonoidHom.snd E F)) (fun i => (x i).2)=⊤)
    (ce : Nat.card (adjoin T x) ≤ Nat.card E) (cf : Nat.card (adjoin T x) ≤ Nat.card F) :
    Nonempty (E ≃* F) := by
  let S := adjoin T x
  let a := (MonoidHom.fst E F).comp S.subtype
  let b := (MonoidHom.snd E F).comp S.subtype
  have sa : Function.Surjective a := by
    intro y
    change y∈a.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genE ▸ (show y∈(⊤ : Subgroup E) from trivial)
  have sb : Function.Surjective b := by
    intro y
    change y∈b.range
    rw [MonoidHom.range_comp,Subgroup.range_subtype,map_adjoin]
    exact genF ▸ (show y∈(⊤ : Subgroup F) from trivial)
  exact ⟨(MulEquiv.ofBijective a (sa.bijective_of_nat_card_le ce)).symm.trans
    (MulEquiv.ofBijective b (sb.bijective_of_nat_card_le cf))⟩
end CentralKernelCount
end

/- PowerMarks -/
section
namespace CentralKernelCount
open scoped commutatorElement
theorem card_adjoin_normalized_orders {G : Type*} [Group G] [Finite G] {d : ℕ} (T : Subgroup G)
    (x : Fin d → G) (ord : Fin d→ℕ) (ho : ∀ i,0 < ord i) (hn : ∀ i,x i ∈ Subgroup.normalizer T)
    (hs : ∀ i,x i ^ ord i ∈ T) (hc : ∀ i j, ⁅x i,x j⁆ ∈ T) :
    Nat.card (adjoin T x) ≤ (∏ i,ord i) * Nat.card T := by
  let N := Subgroup.normalizer (T : Set G)
  let U := T.subgroupOf N
  let y (i : Fin d) : N := ⟨x i,hn i⟩
  have su (i : Fin d) : y i ^ ord i ∈ U := hs i
  have cu (i j : Fin d) : ⁅y i,y j⁆ ∈ U := hc i j
  have count := card_adjoin_orders U y ord ho su cu
  have lower : U.map N.subtype=T := Subgroup.map_subgroupOf_eq_of_le T.le_normalizer
  have map_eq : (adjoin U y).map N.subtype = adjoin T x := (map_adjoin ..).trans (by rw [lower];rfl)
  calc
    _ = Nat.card (adjoin U y) := map_eq ▸ Subgroup.card_map_of_injective N.subtype_injective
    _ ≤ (∏ i,ord i) * Nat.card U := count
    _ = _ := congrArg ((∏ i,ord i) * ·) (Nat.card_congr (Subgroup.subgroupOfEquivOfLe T.le_normalizer).toEquiv)
end CentralKernelCount
end

/- RestrictedExtension -/
section
namespace Erdos1160.Sims
open CentralKernelCount
open scoped commutatorElement
abbrev ExtraSlot (n t : ℕ) := (Fin n × Fin t) ⊕ PairSlot n
structure ExtensionMark (H E : Type*) [Group H] [Group E] (n : ℕ) where
  incl : H →* E
  x : Fin n→E
  generate : adjoin incl.range x=⊤
def ExtensionFits {H E : Type*} [Group H] [Group E] {n t : ℕ} (m : ExtensionMark H E n)
    (base : Fin t→H) (ord : Fin n→ℕ) (power : Fin n→H) (comm : ExtraSlot n t→H) : Prop :=
  (∀i,m.x i^ord i=m.incl (power i)) ∧
  (∀i j,⁅m.x i,m.incl (base j)⁆=m.incl (comm (.inl (i,j)))) ∧
  (∀z : PairSlot n,⁅m.x z.1,m.x (second z)⁆=m.incl (comm (.inr z)))
theorem restricted_extension_separation {H E J : Type*} [Group H] [Group E] [Group J]
    [Finite H] [Finite E] [Finite J] {n t : ℕ} (m : ExtensionMark H E n) (m' : ExtensionMark H J n)
    (base : Fin t→H) (hbase : Subgroup.closure (Set.range base)=⊤)
    (ord : Fin n→ℕ) (ho : ∀i,0 < ord i) (power : Fin n→H) (comm : ExtraSlot n t→H)
    (he : ExtensionFits m base ord power comm) (hj : ExtensionFits m' base ord power comm)
    (ce : (∏i,ord i)*Nat.card H ≤ Nat.card E) (cj : (∏i,ord i)*Nat.card H ≤ Nat.card J) :
    Nonempty (E≃*J) := by
  let f := m.incl.prod m'.incl
  let T := f.range
  let x (i : Fin n) := (m.x i,m'.x i)
  have tgen : Subgroup.closure (Set.range (f ∘ base))=T := by
    rw [Set.range_comp,←MonoidHom.map_closure,hbase,←f.range_eq_map]
  have normal (i : Fin n) : x i∈Subgroup.normalizer T := by
    let c := (MulAut.conj (x i)).toMonoidHom
    have le : T.map c ≤ T := by
      calc
        T.map c = Subgroup.closure (c '' Set.range (f ∘ base)) := by rw [←MonoidHom.map_closure,tgen]
        _ ≤ T := ?_
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨_,⟨j,rfl⟩,rfl⟩
      change x i*f (base j)*(x i)⁻¹∈T
      have eq : x i*f (base j)*(x i)⁻¹=⁅x i,f (base j)⁆*f (base j) := by rw [commutatorElement_def];group
      rw [eq]
      exact T.mul_mem ⟨comm (.inl (i,j)),Prod.ext (he.2.1 i j).symm (hj.2.1 i j).symm⟩ ⟨base j,rfl⟩
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge le
      (Subgroup.card_map_of_injective (MulAut.conj (x i)).injective).ge)
  have pw (i : Fin n) : x i^ord i∈T := ⟨power i,Prod.ext (he.1 i).symm (hj.1 i).symm⟩
  have half (z : PairSlot n) : ⁅x z.1,x (second z)⁆∈T :=
    ⟨comm (.inr z),Prod.ext (he.2.2 z).symm (hj.2.2 z).symm⟩
  have cross (i j : Fin n) : ⁅x i,x j⁆∈T := by
    rcases lt_trichotomy i j with h|rfl|h
    · rw [←commutatorElement_inv];exact T.inv_mem (half ⟨j,⟨i.val,h⟩⟩)
    · simpa using T.one_mem
    · exact half ⟨i,⟨j.val,h⟩⟩
  have bound := (card_adjoin_normalized_orders T x ord ho normal pw cross).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ f.rangeRestrict_surjective))
  apply paired_of_order T x _ _ (bound.trans ce) (bound.trans cj)
  · change adjoin (f.range.map _) m.x=⊤
    rw [←MonoidHom.range_comp];exact m.generate
  · change adjoin (f.range.map _) m'.x=⊤
    rw [←MonoidHom.range_comp];exact m'.generate
theorem extraSlot_card (n t : ℕ) : Nat.card (ExtraSlot n t)=n*t+n*(n-1)/2 := by
  rw [ExtraSlot,Nat.card_sum,Nat.card_prod,Nat.card_fin,Nat.card_fin]
  congr 1
  rw [PairSlot,Nat.card_sigma]
  simp only [Nat.card_fin]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ=>i) n).trans (Finset.sum_range_id n)
end Erdos1160.Sims
end

/- RestrictedFiber -/
section
namespace Erdos1160.Sims
open CentralKernelCount
private lemma coset_card_le {H V : Type*} [Group H] [Group V] [Finite H] (π : H→*V) (v : V) :
    Nat.card {w : H // π w=v}≤Nat.card π.ker := by
  classical
  by_cases h : Nonempty {w : H // π w=v}
  · let z := h.some
    let T (w : {w : H // π w=v}) : π.ker := ⟨w.val*z.val⁻¹,by
      change π (_*_)=1;rw [map_mul,map_inv,w.property,z.property,mul_inv_cancel]⟩
    exact Nat.card_le_card_of_injective T (fun a b e=>Subtype.ext (mul_right_cancel (congrArg (fun k : π.ker=>k.val) e)))
  · let _ : IsEmpty {w : H // π w=v} := not_nonempty_iff.mp h
    simp
theorem restricted_extension_count {I H V : Type} [Group H] [Finite H] [Group V] {n t : ℕ}
    (E : I→Type) [∀i,Group (E i)] [∀i,Finite (E i)] (mark : ∀i,ExtensionMark H (E i) n)
    (base : Fin t→H) (hbase : Subgroup.closure (Set.range base)=⊤)
    (ord : Fin n→ℕ) (ho : ∀i,0 < ord i) (π : H→*V) (pattern : ExtraSlot n t→V)
    (w : I→Fin n→H) (c : I→ExtraSlot n t→H) (hc : ∀i z,π (c i z)=pattern z)
    (fits : ∀i,ExtensionFits (mark i) base ord (w i) (c i))
    (size : ∀i,(∏j,ord j)*Nat.card H ≤ Nat.card (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I ≤ Nat.card H^n*Nat.card π.ker^(n*t+n*(n-1)/2) := by
  classical
  let C (z : ExtraSlot n t) := {v : H // π v=pattern z}
  let enc (i : I) : (Fin n→H) × ((z : ExtraSlot n t)→C z) :=
    (w i,fun z=>⟨c i z,hc i z⟩)
  have hi : Function.Injective enc := by
    intro i j h
    have e₁ : w i=w j := congrArg Prod.fst h
    have e₂ : c i=c j := funext (fun z=>congrArg (fun a : (Fin n→H) × ((z : ExtraSlot n t)→C z)=>(a.2 z).val) h)
    apply sep i j
    exact restricted_extension_separation (mark i) (mark j) base hbase ord ho (w i) (c i) (fits i)
      (e₁ ▸ e₂ ▸ fits j) (size i) (size j)
  calc
    _ ≤ Nat.card ((Fin n→H) × ((z : ExtraSlot n t)→C z)) := Nat.card_le_card_of_injective _ hi
    _ = Nat.card H^n*∏ z,Nat.card (C z) := by rw [Nat.card_prod,Nat.card_fun,Nat.card_fin,Nat.card_pi]
    _ ≤ Nat.card H^n*∏ _z : ExtraSlot n t,Nat.card π.ker :=
      Nat.mul_le_mul_left _ (Finset.prod_le_prod' (fun z _=>coset_card_le π (pattern z)))
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,←Nat.card_eq_fintype_card,extraSlot_card]
end Erdos1160.Sims
end

/- HeadEmbedding -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second secondBracket lower_map_top)
open Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] (H : Subgroup G)
abbrev headQuot (G : Type) [Group G] := G ⧸ commutatorTail G
abbrev headMap (G : Type) [Group G] : G→*headQuot G := QuotientGroup.mk' (commutatorTail G)
abbrev headSub := (H.map (headMap G))
def toHeadSub : H→*headSub H := ((headMap G).comp H.subtype).codRestrict _ (fun x=>⟨x.val,x.property,rfl⟩)
theorem toHeadSub_surj : Function.Surjective (toHeadSub H) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩
theorem toHeadSub_kernel (hh : (commutator H).map H.subtype=commutator G) :
    (toHeadSub H).ker=commutatorTail H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [subgroup_tail_eq H hh]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp (congrArg (fun v:headSub H=>v.val) hy)
  · intro hx
    have incl : commutatorTail G ≤ H := (commutatorTail_le_derived G).trans
      (hh ▸ (Subgroup.map_subtype_le _))
    refine ⟨⟨x,incl hx⟩,?_,rfl⟩
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hx)
theorem head_derived_image (hh : (commutator H).map H.subtype=commutator G) :
    (Second (headSub H)).map (headSub H).subtype=Second (headQuot G) := by
  have part : (Second H).map (toHeadSub H)=Second (headSub H) := lower_map_top _ (toHeadSub_surj H) 1
  rw [←part,Subgroup.map_map,
    show (headSub H).subtype.comp (toHeadSub H)=(headMap G).comp H.subtype from rfl,←Subgroup.map_map]
  change ((commutator H).map H.subtype).map _=_
  rw [hh];exact lower_map_top _ (QuotientGroup.mk'_surjective _) 1
noncomputable def derivedHeadEquiv (hh : (commutator H).map H.subtype=commutator G) :
    Second (headSub H)≃*Second (headQuot G) :=
  ((Second (headSub H)).equivMapOfInjective (headSub H).subtype (headSub H).subtype_injective).trans
    (MulEquiv.subgroupCongr (head_derived_image H hh))
theorem headSub_class_two : Second (headSub H) ≤ Subgroup.center (headSub H) := by
  intro x hx
  have le : (commutator (headSub H)).map (headSub H).subtype ≤ commutator (headQuot G) := by
    rw [Subgroup.map_subtype_commutator];exact Subgroup.commutator_mono le_top le_top
  have mem : (x:headQuot G)∈Second (headQuot G) := le ⟨x,hx,rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro y
  exact Subtype.ext (Subgroup.mem_center_iff.mp ((head_conditions G).1 mem) y.val)
theorem headSub_derived_binary (hh : (commutator H).map H.subtype=commutator G) :
    ∀w:Second (headSub H),w*w=1 := by
  intro w
  apply (derivedHeadEquiv H hh).injective
  rw [map_mul,map_one]
  exact (head_conditions G).2 _
theorem headSub_kernel_frattini {m : ℕ} (hH : Nat.card H=2^m)
    (hh : (commutator H).map H.subtype=commutator G) : (toHeadSub H).ker ≤ frattini H := by
  rw [toHeadSub_kernel H hh,frattini_eq_squareCore hH]
  exact (commutatorTail_le_derived H).trans (Erdos1160.CentralLifts.Survival.derived_le_squares H)
end Erdos1160.Sims
end

/- BracketTensor -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi Erdos1160Growth.LowerTriangularUpper
open OrbitUp OrbitUp.MinSpan
open scoped commutatorElement
variable {G J W : Type*} [Group G] [Group J] [CommGroup W]
private theorem central_bracket_left (hc : Second J ≤ Subgroup.center J) (x y z : J) :
    secondBracket (x*y) z=secondBracket x z*secondBracket y z := by
  apply Subtype.ext
  change ⁅x*y,z⁆=⁅x,z⁆*⁅y,z⁆
  have a := Subgroup.mem_center_iff.mp (hc (secondBracket y z).property) x
  have b := Subgroup.mem_center_iff.mp (hc (secondBracket x z).property) ⁅y,z⁆
  change x*⁅y,z⁆=⁅y,z⁆*x at a
  change ⁅y,z⁆*⁅x,z⁆=⁅x,z⁆*⁅y,z⁆ at b
  rw [commutatorElement_mul_left_eq_conj_mul,a,mul_inv_cancel_right,b]
private theorem central_bracket_right (hc : Second J ≤ Subgroup.center J) (x y z : J) :
    secondBracket x (y*z)=secondBracket x y*secondBracket x z := by
  apply Subtype.ext
  change ⁅x,y*z⁆=⁅x,y⁆*⁅x,z⁆
  have a := Subgroup.mem_center_iff.mp (hc (secondBracket x z).property) y
  change y*⁅x,z⁆=⁅x,z⁆*y at a
  rw [commutatorElement_mul_right_eq_mul_conj,mul_assoc ⁅x,y⁆ y,mul_assoc ⁅x,y⁆,a,mul_inv_cancel_right]
def headBiHom (q : G→*J) (hc : Second J ≤ Subgroup.center J) (a : Second J→*W) :
    G→*(G→*W) where
  toFun x := {
    toFun y := a (secondBracket (q x) (q y))
    map_one' := by rw [q.map_one,show secondBracket (q x) 1=1 from Subtype.ext (commutatorElement_one_right _),a.map_one]
    map_mul' y z := by rw [q.map_mul,central_bracket_right hc,a.map_mul] }
  map_one' := by
    apply MonoidHom.ext;intro y
    change a (secondBracket (q 1) (q y))=1
    rw [q.map_one,show secondBracket 1 (q y)=1 from Subtype.ext (commutatorElement_one_left _),a.map_one]
  map_mul' x y := by
    apply MonoidHom.ext;intro z
    change a (secondBracket (q (x*y)) (q z))=a (secondBracket (q x) (q z))*a (secondBracket (q y) (q z))
    rw [q.map_mul,central_bracket_left hc,a.map_mul]
theorem squareCore_killed {E K : Type*} [Group E] [Group K] (v : E→*K) (hb : ∀x:K,x*x=1) :
    squareCore E ≤ v.ker := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x,rfl⟩
  change v (x*x)=1
  rw [v.map_mul,hb]
theorem exists_head_tensor {d b : ℕ} (p : G→*Multiplicative (OrbitUp.V d)) (sp : Function.Surjective p)
    (kp : p.ker=squareCore G) (q : G→*J) (sq : Function.Surjective q) (hc : Second J ≤ Subgroup.center J)
    (a : Second J≃*Multiplicative (OrbitUp.V b)) :
    ∃ β : Tensor d b, (∀x,β x x=0) ∧ BoundedMatrices.valuesOn β ⊤=⊤ ∧
      ∀x y,β (p x).toAdd (p y).toAdd=(a (secondBracket (q x) (q y))).toAdd := by
  let A := headBiHom q hc a.toMonoidHom
  have bin (w : Multiplicative (OrbitUp.V b)) : w*w=1 := by
    apply Multiplicative.toAdd.injective
    funext i
    exact (show ∀z:OrbitUp.K,z+z=0 by decide) _
  obtain ⟨B,hB⟩ := descend_pair p sp p sp A (kp ▸ squareCore_killed A (fun v=>MonoidHom.ext fun _=>bin _))
    (fun x=>kp ▸ squareCore_killed (A x) bin)
  let B' : OrbitUp.V d→+OrbitUp.V d→+OrbitUp.V b := {
    toFun x := (B (.ofAdd x)).toAdditive
    map_zero' := by rw [show Multiplicative.ofAdd (0:OrbitUp.V d)=1 from rfl,B.map_one];rfl
    map_add' x y := by rw [show Multiplicative.ofAdd (x+y)=Multiplicative.ofAdd x*Multiplicative.ofAdd y from rfl,B.map_mul];rfl }
  let β : Tensor d b := (((AddMonoidHom.toZModLinearMapEquiv 2).toAddMonoidHom.comp B').toZModLinearMap 2)
  have spec (x y : G) : β (p x).toAdd (p y).toAdd=(a (secondBracket (q x) (q y))).toAdd :=
    congrArg Multiplicative.toAdd (hB x y)
  refine ⟨β,?_,?_,spec⟩
  · intro x
    obtain ⟨u,hu⟩ := sp (.ofAdd x)
    have e : (p u).toAdd=x := congrArg Multiplicative.toAdd hu
    rw [←e,spec,show secondBracket (q u) (q u)=1 from Subtype.ext (commutatorElement_self _),a.map_one]
    rfl
  · let L := BoundedMatrices.valuesOn β ⊤
    let T : Subgroup (Second J) := { carrier := {w | (a w).toAdd∈L}
                                     one_mem' := by change (a 1).toAdd∈L; rw [a.map_one]; exact L.zero_mem
                                     mul_mem' := fun {x y} hx hy=>by change (a (x*y)).toAdd∈L;rw [map_mul];exact L.add_mem hx hy
                                     inv_mem' := fun {x} hx=>by change (a x⁻¹).toAdd∈L;rw [map_inv];exact L.neg_mem hx }
    have all : commutator J ≤ T.map (Second J).subtype := by
      rw [commutator_eq_closure,Subgroup.closure_le]
      rintro _ ⟨u,v,rfl⟩
      obtain ⟨x,rfl⟩ := sq u
      obtain ⟨y,rfl⟩ := sq v
      refine ⟨secondBracket _ _,?_,rfl⟩
      change (a (secondBracket (q x) (q y))).toAdd∈L
      rw [←spec]
      exact Submodule.subset_span ⟨(⟨_,Submodule.mem_top⟩,⟨_,Submodule.mem_top⟩),rfl⟩
    apply top_unique
    intro u _
    let w := a.symm (.ofAdd u)
    obtain ⟨v,hv,e⟩ := all w.property
    have h : v=w := Subtype.ext e
    change (a v).toAdd∈L at hv
    rw [h,show a w=.ofAdd u from a.apply_symm_apply _] at hv
    exact hv
end Erdos1160.Sims
end

/- SpanningSubgroup -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second secondMap secondBracket)
open OrbitUp OrbitUp.MinSpan
open OrbitUp.BoundedMatrices
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {d b : ℕ}
def vectorSub {d : ℕ} (H : Subgroup (Multiplicative (V d))) : Submodule K (V d) where
  carrier := {x | Multiplicative.ofAdd x∈H}
  zero_mem' := H.one_mem
  add_mem' := H.mul_mem
  smul_mem' k x hx := by
    rcases (show ∀k:K,k=0 ∨ k=1 by decide) k with rfl|rfl
    · rw [zero_smul];exact H.one_mem
    · rwa [one_smul]
theorem subgroup_of_spanning (hG : IsPGroup 2 G) (p : G→*Multiplicative (V d))
    (a : Second (G⧸commutatorTail G)≃*Multiplicative (V b)) (β : Tensor d b)
    (spec : ∀x y,β (p x).toAdd (p y).toAdd=(a (secondBracket
      ((QuotientGroup.mk' (commutatorTail G)) x) ((QuotientGroup.mk' (commutatorTail G)) y))).toAdd)
    (H : Subgroup G) (S : Submodule K (V d)) (hS : valuesOn β S=⊤)
    (covers : ∀u:S,∃x:H,(p x.val).toAdd=u.val) :
    (commutator H).map H.subtype=commutator G := by
  let q := QuotientGroup.mk' (commutatorTail G)
  have sq := QuotientGroup.mk'_surjective (commutatorTail G)
  let D := (commutator H).map H.subtype
  have hD : D ≤ commutator G := by
    rw [show D=⁅H,H⁆ from Subgroup.map_subtype_commutator H]
    exact Subgroup.commutator_mono le_top le_top
  let z := (D.map q).comap (Second (G⧸commutatorTail G)).subtype
  let W := vectorSub (z.map a.toMonoidHom)
  have incl : valuesOn β S ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨u,v⟩,rfl⟩
    obtain ⟨x,ex⟩ := covers u
    obtain ⟨y,ey⟩ := covers v
    change β u.val v.val∈W
    rw [←ex,←ey,spec]
    refine ⟨secondBracket (q x.val) (q y.val),?_,rfl⟩
    exact ⟨⁅x.val,y.val⁆,⟨(secondBracket x y).val,(secondBracket x y).property,rfl⟩,map_commutatorElement q _ _⟩
  rw [hS] at incl
  have all : (commutator G).map q ≤ D.map q := by
    rintro _ ⟨u,hu,rfl⟩
    let w := secondMap q sq ⟨u,hu⟩
    have mem := incl (Submodule.mem_top : (a w).toAdd∈⊤)
    obtain ⟨v,hv,ev⟩ := mem
    change v.val∈D.map q at hv
    rw [a.injective ev] at hv
    exact hv
  apply structural_derived hG H
  have hh := Subgroup.map_le_iff_le_comap.mp all
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk'] at hh
  exact hh
omit [Finite G] in


theorem lift_subspace (p : G→*Multiplicative (V d)) (sp : Function.Surjective p)
    (S : Submodule K (V d)) :
    ∃ (H : Subgroup G) (x : Fin (Module.finrank K S)→H),
      Subgroup.closure (Set.range x)=⊤ ∧ vectorSub (H.map p)=S := by
  classical
  let B := Module.finBasis K S
  choose y hy using fun i=>sp (Multiplicative.ofAdd (B i).val)
  let H := Subgroup.closure (Set.range y)
  let x (i) : H := ⟨y i,Subgroup.subset_closure ⟨i,rfl⟩⟩
  have hx : Subgroup.closure (Set.range x)=⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,H.range_subtype]
    rfl
  refine ⟨H,x,hx,le_antisymm ?_ ?_⟩
  · let T := S.toAddSubgroup.toSubgroup
    have le : H.map p ≤ T := by
      rw [show H=Subgroup.closure (Set.range y) from rfl,MonoidHom.map_closure,Subgroup.closure_le]
      rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
      rw [hy]
      exact (B i).property
    exact le
  · have bc : Submodule.span K (Set.range (fun i=>(B i).val))=S := by
      rw [show (fun i=>(B i).val)=S.subtype ∘ B from rfl,Set.range_comp,←Submodule.map_span,B.span_eq,Submodule.map_top,Submodule.range_subtype]
    rw [←bc]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨y i,(x i).property,hy i⟩
end Erdos1160.Sims
end

/- HeadSizes -/
section
namespace Erdos1160.Sims
open Erdos1160.DeepJacobi (Second)
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open Erdos1160.CentralLifts.Survival (derived_le_squares)
open OrbitUp
variable {G : Type} [Group G] [Finite G] {m d b : ℕ}
theorem head_size_budget (hG : Nat.card G=2^m) (p : G→*Multiplicative (V d)) (sp : Function.Surjective p)
    (kp : p.ker=squareCore G) (der : Nat.card (Second (headQuot G))=2^b) {t : ℕ}
    (tail : Nat.card (commutatorTail G)=2^t) : d+b+t ≤ m := by
  have van : commutatorTail G ≤ p.ker := kp ▸ (commutatorTail_le_derived G).trans (derived_le_squares G)
  let f := QuotientGroup.lift (commutatorTail G) p van
  have sf : Function.Surjective f := by
    intro w
    obtain ⟨u,rfl⟩ := sp w
    exact ⟨(headMap G) u,rfl⟩
  have incl : Second (headQuot G) ≤ f.ker := Abelianization.commutator_subset_ker f
  have large : 2^b ≤ Nat.card f.ker := der ▸ Nat.card_le_card_of_injective (Subgroup.inclusion incl) (Subgroup.inclusion_injective incl)
  have ix : f.ker.index=2^d := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f sf,Subgroup.card_top]
    change Nat.card (Fin d→ZMod 2)=_
    rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have hhead := f.ker.index_mul_card
  rw [ix] at hhead
  have ch : 2^d*2^b ≤ Nat.card (headQuot G) := (Nat.mul_le_mul_left _ large).trans_eq hhead
  have eq := (commutatorTail G).card_eq_card_quotient_mul_card_subgroup
  rw [hG,tail] at eq
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [pow_add,pow_add]
  exact (Nat.mul_le_mul_right _ ch).trans_eq eq.symm
theorem inside_tail_card (H : Subgroup G) (hh : (commutator H).map H.subtype=commutator G) :
    Nat.card (toHeadSub H).ker=Nat.card (commutatorTail G) := by
  rw [toHeadSub_kernel H hh,←subgroup_tail_eq H hh,Subgroup.card_map_of_injective H.subtype_injective]
theorem card_of_onto {A B : Type*} [Group A] [Group B] (f : A→*B) (sf : Function.Surjective f) :
    Nat.card A=Nat.card B*Nat.card f.ker := by
  rw [←f.ker.index_mul_card,Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f sf,Subgroup.card_top]
end Erdos1160.Sims
end

/- NucleusRank -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi
open scoped commutatorElement
variable {d m : ℕ} {Q : Type} [Group Q] [Finite Q]
noncomputable def jacobiRank (Q : Type) [Group Q] := Module.finrank (ZMod 2) (Additive (JacobiDual Q))
theorem cover_class_two_decomposition (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) :
    ∃ (Y : FiniteGrp.{0}) (j : ℕ) (f : Y →* Q) (g : FreeGroup (Fin d) →* Y),
      Function.Surjective f ∧ Function.Surjective g ∧ IsPGroup 2 Y ∧ Second Y ≤ Subgroup.center Y ∧
      f.ker ≤ Subgroup.center Y ∧ (∀x:f.ker,x*x=1) ∧ j ≤ jacobiRank Q ∧
      Nat.card (Cover π)=Nat.card Y * 2^j := by
  let φ := coverProjection π
  have hφ := cover_onto π hπ
  have hc := cover_card π hπ
  rw [hQ,←pow_add] at hc
  let _ : Finite (Cover π) := Nat.finite_of_card_ne_zero (hc ▸ Nat.ne_of_gt (Nat.two_pow_pos _))
  have hp := IsPGroup.of_card hc
  let N := Third (Cover π)
  have hN : N≤φ.ker := by
    apply Subgroup.commutator_le.mpr
    intro w hw x _
    rw [MonoidHom.mem_ker,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hclass (secondMap φ hφ ⟨w,hw⟩).property) _).symm
  let Y := Cover π ⧸ N
  let h := QuotientGroup.mk' N
  have sh := QuotientGroup.mk'_surjective N
  let f := QuotientGroup.lift N φ hN
  have sf : Function.Surjective f := fun z => by obtain ⟨u,rfl⟩ := hφ z;exact ⟨h u,rfl⟩
  let g := h.comp (QuotientGroup.mk' (universalKernel π))
  have sg := sh.comp (QuotientGroup.mk'_surjective _)
  have hfc : f.ker ≤ Subgroup.center Y := by
    intro u hu
    obtain ⟨w,rfl⟩ := sh u
    have hw : w∈φ.ker := hu
    apply Subgroup.mem_center_iff.mpr
    intro z
    obtain ⟨v,rfl⟩ := sh z
    exact (map_mul h _ _).symm.trans ((congrArg h (Subgroup.mem_center_iff.mp (cover_central π hw) v)).trans (map_mul h _ _))
  have hfs (u : f.ker) : u*u=1 := by
    apply Subtype.ext
    obtain ⟨w,hw⟩ := sh u.val
    have hφw : w∈φ.ker := by change f (h w)=1;rw [hw];exact u.property
    change u.val*u.val=1
    rw [←hw,←map_mul,show w*w=1 from congrArg Subtype.val (cover_binary π ⟨w,hφw⟩),map_one]
  obtain ⟨j,hj⟩ := (hp.to_subgroup N).exists_card_eq
  have hns (u : N) : u*u=1 := Subtype.ext (congrArg (fun v : (coverProjection π).ker => v.val) (cover_binary π ⟨u.val,hN u.property⟩))
  have rank := elementary_third_dimension φ hφ (cover_central π) (hN.trans (cover_central π)) hns hj
  exact ⟨FiniteGrp.of Y,j,f,g,sf,sg,hp.to_quotient N,ThirdLowerCentral.quotient_has_class_two _,hfc,hfs,rank,
    N.card_eq_card_quotient_mul_card_subgroup.trans (congrArg (Nat.card Y * ·) hj)⟩
theorem multiplicator_rank_of_class_bound (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) {D : ℕ}
    (h : ∀ (Y : FiniteGrp.{0}) (f : Y →* Q) (g : FreeGroup (Fin d) →* Y),
      Function.Surjective f → Function.Surjective g → IsPGroup 2 Y → Second Y ≤ Subgroup.center Y →
      f.ker ≤ Subgroup.center Y → (∀x:f.ker,x*x=1) → Nat.card Y ≤ Nat.card Q*2^D) :
    relRank π ≤ D+jacobiRank Q := by
  obtain ⟨Y,j,f,g,hf,hg,hp,hc,hk,hb,hj,hcard⟩ := cover_class_two_decomposition π hπ hQ hclass
  have a := Nat.mul_le_mul (h Y f g hf hg hp hc hk hb) (Nat.pow_le_pow_right (by decide : 0 < 2) hj)
  rw [←hcard,cover_card π hπ,Nat.mul_assoc,←pow_add,Nat.mul_comm (2^(relRank π)),hQ,←pow_add,←pow_add] at a
  have n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp a
  omega
end Erdos1160.CentralLifts.Survival
end

/- ClassTwoCoverSize -/
section
namespace Erdos1160.DeepJacobi
open scoped commutatorElement
private theorem generated_map {G J ι : Type} [Group G] [Group J] (v : ι → G)
    (hgen : Subgroup.closure (Set.range v)=⊤) (π : G →* J) (hπ : Function.Surjective π) :
    Subgroup.closure (Set.range (π ∘ v))=⊤ := by
  rw [Set.range_comp,←MonoidHom.map_closure,hgen,Subgroup.map_top_of_surjective π hπ]
private theorem abelian_binary_torsion {A ι : Type} [CommGroup A] [Finite A] [Fintype ι]
    (v : ι → A) (hgen : Subgroup.closure (Set.range v)=⊤) :
    Nat.card (powMonoidHom (α := A) 2).ker ≤ 2^(Fintype.card ι) := by
  classical
  let s := powMonoidHom (α := A) 2
  let R := s.range
  let π := QuotientGroup.mk' R
  have heq : Nat.card s.ker=Nat.card (A ⧸ R) := by
    have h1 := s.ker.index_mul_card
    rw [Subgroup.index_ker] at h1
    have h2 := R.card_mul_index
    exact Nat.eq_of_mul_eq_mul_left (by exact Nat.card_pos : 0 < Nat.card R) (h1.trans h2.symm)
  let T := Finset.univ.image (π ∘ v)
  have hc : Subgroup.closure (T:Set (A ⧸ R))=⊤ := by
    have eqs : (T : Set (A ⧸ R)) = Set.range (π ∘ v) := by ext x; simp [T,Function.comp_def]
    rw [eqs]; exact generated_map v hgen π (QuotientGroup.mk'_surjective R)
  have hsize : Group.rank (A ⧸ R) ≤ Fintype.card ι :=
    (Group.rank_le hc).trans (Finset.card_image_le.trans_eq (Finset.card_univ : (Finset.univ : Finset ι).card=_))
  have exp (x : A ⧸ R) : x^2=1 := by
    obtain ⟨q,rfl⟩ := QuotientGroup.mk'_surjective R x
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨q,rfl⟩
  exact heq.le.trans ((Nat.le_of_dvd (Nat.two_pow_pos _) (card_dvd_exponent_pow_rank' _ exp)).trans
    (Nat.pow_le_pow_right (by decide) hsize))
theorem generated_class_two_cover_bound {d : ℕ} {Y Q : Type} [Group Y] [Group Q] [Finite Y] [Finite Q]
    (f : Y →* Q) (hf : Function.Surjective f) (hker2 : ∀ x : f.ker, x*x=1)
    (hY : Second Y ≤ Subgroup.center Y) (g : FreeGroup (Fin d) →* Y) (hg : Function.Surjective g) :
    Nat.card Y ≤ Nat.card Q*2^(d*(d+1)/2) := by
  classical
  let u (i : Fin d) := g (FreeGroup.of i)
  have hgen : Subgroup.closure (Set.range u)=⊤ := generated_map _ (FreeGroup.closure_range_of _) g hg
  let T := (i : Fin d) × Fin i.val
  let bracket (i : T) := ⁅u i.1,u (⟨i.2.val,i.2.isLt.trans i.1.isLt⟩ : Fin d)⁆
  let C := Subgroup.closure (Set.range bracket)
  have hc : C ≤ Subgroup.center Y := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hY (secondBracket (u i.1) (u (⟨i.2.val,i.2.isLt.trans i.1.isLt⟩ : Fin d))).property
  letI : C.Normal := ⟨fun x hx y => by
    rw [Subgroup.mem_center_iff.mp (hc hx) y,mul_inv_cancel_right]; exact hx⟩
  let groupC : Group C := inferInstance
  letI : CommGroup C := { groupC with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hc b.property) a) }
  let w (i : T) : C := ⟨bracket i,Subgroup.subset_closure ⟨i,rfl⟩⟩
  have hCgen : Subgroup.closure (Set.range w)=⊤ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,C.range_subtype]
    rfl
  let π := QuotientGroup.mk' C
  let q := π ∘ u
  have hq := generated_map u hgen π (QuotientGroup.mk'_surjective C)
  have hpairs (i j : Fin d) (h : j < i) : q i*q j=q j*q i := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅π (u i),π (u j)⁆=1
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨⟨i,⟨j.val,h⟩⟩,rfl⟩)
  have hcomm : IsMulCommutative (Subgroup.closure (Set.range q)) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rcases lt_trichotomy i j with h|h|h
    · exact (hpairs _ _ h).symm
    · rw [h]
    · exact hpairs _ _ h
  change Subgroup.closure (Set.range q)=⊤ at hq
  rw [hq] at hcomm
  let groupQ : Group (Y ⧸ C) := inferInstance
  letI : CommGroup (Y ⧸ C) := { groupQ with
    mul_comm := fun a b => congrArg Subtype.val (hcomm.is_comm.comm (⟨a,trivial⟩ : (⊤ : Subgroup (Y ⧸ C))) ⟨b,trivial⟩) }
  let ψ := π.comp f.ker.subtype
  let qsq := powMonoidHom (α := Y ⧸ C) 2
  let csq := powMonoidHom (α := C) 2
  have him : ψ.range ≤ qsq.ker := by
    rintro _ ⟨x,rfl⟩
    change (ψ x)^2=1
    rw [←map_pow,pow_two,hker2,map_one]
  let lift (x : ψ.ker) : C := ⟨x.val.val,(QuotientGroup.eq_one_iff _).mp x.property⟩
  let κ (x : ψ.ker) : csq.ker := ⟨lift x,by
    apply Subtype.ext
    change x.val.val^2=1
    rw [pow_two]
    exact congrArg Subtype.val (hker2 x.val)⟩
  have inj : Function.Injective κ := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : csq.ker => z.val.val) h))
  have hk := (Nat.card_le_card_of_injective κ inj).trans (abelian_binary_torsion w hCgen)
  have hi := (Nat.card_le_card_of_injective (Subgroup.inclusion him) (Subgroup.inclusion_injective him)).trans
    (abelian_binary_torsion q hq)
  have he : Nat.card f.ker = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [←Subgroup.index_ker,Subgroup.index_mul_card]
  have hcT : d+Fintype.card T=d*(d+1)/2 := by
    change d+Fintype.card (Σ i : Fin d,Fin i.val)=_
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [Fin.sum_univ_eq_sum_range (fun i => i),Nat.add_comm,←Finset.sum_range_succ,Finset.sum_range_id]
    simp only [Nat.add_sub_cancel,Nat.mul_comm]

  calc
    _ = Nat.card Q * Nat.card f.ker := by
      rw [←f.ker.index_mul_card,Subgroup.index_ker,MonoidHom.range_eq_top_of_surjective f hf,Subgroup.card_top]
    _ ≤ Nat.card Q*(2^Fintype.card (Fin d)*2^Fintype.card T) := Nat.mul_le_mul_left _ (he.le.trans (Nat.mul_le_mul hi hk))
    _ = _ := by rw [←pow_add,Fintype.card_fin,hcT]
end Erdos1160.DeepJacobi
end

/- JacobiFiberCount -/
section
namespace Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi
variable {d t m : ℕ} {Q : Type} [Group Q] [Finite Q]
theorem class_two_multiplicator_bound (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) :
    relRank π ≤ d*(d+1)/2+jacobiRank Q :=
  multiplicator_rank_of_class_bound π hπ hQ hclass
    (fun _ f g hf hg _ hc _ hb => generated_class_two_cover_bound f hf hb hc g hg)
theorem marked_jacobi_fiber_product (π : FreeGroup (Fin d) →* Q) (hπ : Function.Surjective π)
    (hQ : Nat.card Q=2^m) (hclass : Second Q ≤ Subgroup.center Q) (j : ℕ) :
    (frattiniClasses m j Q).ncard ≤ ∏ i ∈ Finset.range j,(2^(d*(d+1)/2+jacobiRank Q+i*d)-1) := by
  apply (multiplicator_fiber_product π hπ hQ j).trans
  apply Finset.prod_le_prod'
  intro i _
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right (class_two_multiplicator_bound π hπ hQ hclass) _)
end Erdos1160.CentralLifts.Survival
end

/- RootPatternCount -/
section
namespace Erdos1160.Sims
open CentralKernelCount
open scoped commutatorElement
theorem root_pattern_count {I W : Type} [Group W] [Finite W] {r b : ℕ}
    (E : I→Type) [∀i,Group (E i)] [∀i,Finite (E i)] (mark : ∀i,ExtensionMark W (E i) r)
    (base : Fin b→W) (hbase : Subgroup.closure (Set.range base)=⊤)
    (central : ∀i,(mark i).incl.range ≤ Subgroup.center (E i))
    (ord : Fin r→ℕ) (ho : ∀i,0 < ord i) (pattern : PairSlot r→W)
    (pows : ∀i j,∃v,(mark i).x j^ord j=(mark i).incl v)
    (comm : ∀i (z : PairSlot r),⁅(mark i).x z.1,(mark i).x (second z)⁆=(mark i).incl (pattern z))
    (size : ∀i,(∏j,ord j)*Nat.card W ≤ Nat.card (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) : Nat.card I ≤ Nat.card W^r := by
  classical
  choose w hw using pows
  let c : ExtraSlot r b→W := Sum.elim (fun _=>1) pattern
  have fits (i : I) : ExtensionFits (mark i) base ord (w i) c := by
    refine ⟨hw i,?_,comm i⟩
    intro j k
    have h := (Subgroup.mem_center_iff.mp (central i (show (mark i).incl (base k)∈(mark i).incl.range from ⟨_,rfl⟩))) ((mark i).x j)
    change ⁅_,_⁆=(mark i).incl 1
    rw [map_one,commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h := restricted_extension_count E mark base hbase ord ho (MonoidHom.id W) c w (fun _=>c)
    (fun _ _=>rfl) fits size sep
  simpa using h
end Erdos1160.Sims
end

/- AlternatingPacking -/
section
namespace OrbitUp.MinSpan
open BoundedMatrices
variable {d b : ℕ}
abbrev AForm (d : ℕ) := V d→ₗ[K] Module.Dual K (V d)
abbrev Edge (d : ℕ) := (i : Fin d) × Fin i.val
private noncomputable def coord (d : ℕ) := (Pi.basisFun K (Fin d)).dualBasis.equivFun
noncomputable def scalarMatrix (A : AForm d) : Matrix (Fin d) (Fin d) K :=
  LinearMap.toMatrix' ((coord d).toLinearMap.comp A)
theorem scalarMatrix_rank (A : AForm d) : (scalarMatrix A).rank=Module.finrank K A.range := by
  have e : (scalarMatrix A).mulVecLin=(coord d).toLinearMap.comp A := by
    apply LinearMap.ext;intro x;exact LinearMap.toMatrix'_mulVec ((coord d).toLinearMap.comp A) x
  rw [Matrix.rank,e,LinearMap.range_comp]
  exact ((coord d).submoduleMap A.range).finrank_eq.symm
theorem scalarMatrix_inj : Function.Injective (@scalarMatrix d) := by
  intro x y e
  have eq := LinearMap.toMatrix'.injective e
  exact LinearMap.ext (fun i=>(coord d).injective (DFunLike.congr_fun eq i))
def edge (A : AForm d) (i : Edge d) := A (basis i.1) (basis ⟨i.2.val,lt_trans i.2.isLt i.1.isLt⟩)
private theorem alt_sym (A : AForm d) (alt : ∀x,A x x=0) (u v : V d) : A u v=A v u := by
  have e := alt (u+v)
  simp only [map_add,LinearMap.add_apply,alt,zero_add,add_zero] at e
  exact (show ∀x y:K,x+y=0→y=x by decide) _ _ e
theorem edge_sep (A B : AForm d) (ha : ∀x,A x x=0) (hb : ∀x,B x x=0) (eq : edge A=edge B) : A=B := by
  apply (Pi.basisFun K (Fin d)).ext;intro i;rw [Pi.basisFun_apply]
  apply (Pi.basisFun K (Fin d)).ext;intro j;rw [Pi.basisFun_apply]
  change A (basis i) (basis j)=B (basis i) (basis j)
  rcases lt_trichotomy j i with h|rfl|h
  · exact congrFun eq ⟨i,⟨j.val,h⟩⟩
  · rw [ha,hb]
  · rw [alt_sym A ha,alt_sym B hb];exact congrFun eq ⟨j,⟨i.val,h⟩⟩
structure SplitDual (b p : ℕ) where
  low : Fin p→Module.Dual K (V b)
  high : Fin (b-p)→Module.Dual K (V b)
  sep : ∀x y:V b,(∀i,low i x=low i y)→(∀i,high i x=high i y)→x=y
theorem split_under {p : ℕ} (T : Submodule K (Module.Dual K (V b))) (hp : p ≤ Module.finrank K T) :
    ∃a : SplitDual b p,∀i,a.low i∈T := by
  classical
  obtain ⟨i,hi⟩ := finrank_le_iff_exists_linearMap.mp (show Module.finrank K (V p) ≤ Module.finrank K T from (Module.finrank_fin_fun _).le.trans hp)
  let f := T.subtype.comp i
  have hfi : Function.Injective f := T.subtype_injective.comp hi
  let L := f.range
  have rank : Module.finrank K L=p := (LinearMap.finrank_range_of_inj hfi).trans (Module.finrank_fin_fun K)
  obtain ⟨H,hH⟩ := Submodule.exists_isCompl L
  have dims := Submodule.finrank_add_eq_of_isCompl hH
  rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun,rank] at dims
  let A := (Module.finBasis K L).reindex (finCongr rank)
  let B := (Module.finBasis K H).reindex (finCongr (show Module.finrank K H=b-p by omega))
  refine ⟨⟨fun j=>(A j).val,fun j=>(B j).val,?_⟩,fun j=>?_⟩
  · intro x y lo hi
    let g := Module.Dual.eval K (V b) x - Module.Dual.eval K (V b) y
    have van {U : Submodule K (Module.Dual K (V b))} {ι : Type} (C : Module.Basis ι K U)
        (hz : ∀j,(C j).val x=(C j).val y) : U ≤ g.ker := by
      have zg : g.comp U.subtype=0 := C.ext (fun j=>sub_eq_zero.mpr (hz j))
      intro jj h
      exact (show g jj=0 from DFunLike.congr_fun zg (⟨jj,h⟩ : U))
    have all : L⊔H ≤ g.ker := sup_le (van A lo) (van B hi)
    rw [hH.sup_eq_top] at all
    funext j
    exact sub_eq_zero.mp (all (x:=LinearMap.proj j) Submodule.mem_top)
  · obtain ⟨x,h⟩ := (A j).property
    change (A j).val∈T
    rw [←h]
    exact (i x).property
end OrbitUp.MinSpan
end

/- MinSpanEntropy -/
section
namespace OrbitUp.MinSpan
open BoundedMatrices
theorem minspan_packing {d b σ k : ℕ} (budget : b+1 < 2*k*k) :
    let p := σ-1-4*k
    Nat.card (minimalAlternating d b σ) ≤
      2^(b*b + 8*k*d*p + (b-p)*d.choose 2) := by
  classical
  let p := σ-1-4*k
  let X := minimalAlternating d b σ
  let L := {M : Matrix (Fin d) (Fin d) K // M.rank ≤ 4*k}
  let D := Module.Dual K (V b)
  letI : Finite D := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  by_cases existsX : Nonempty X
  swap
  · haveI : IsEmpty X := not_nonempty_iff.mp existsX
    change Nat.card X ≤ _
    simp
  have frames (x:X) : ∃ a : SplitDual b p,
      ∀j,(scalarMatrix (push (a.low j) x.val)).rank ≤ 4*k := by
    obtain ⟨T,hσ,low⟩ := many_low_rank_components x budget
    obtain ⟨a,good⟩ := split_under T (show p ≤ Module.finrank K T by dsimp [p];omega)
    exact ⟨a,fun j=>by rw [scalarMatrix_rank];exact (low _ (good j)).le⟩
  choose a hlow using frames
  let C := (Fin p→D) × (Fin (b-p)→D) × (Fin p→L) × (Fin (b-p)→Edge d→K)
  let code (x:X) : C :=
    ((a x).low,(a x).high,fun j=>⟨scalarMatrix (push ((a x).low j) x.val),hlow x j⟩,
      fun j=>edge (push ((a x).high j) x.val))
  have inject : Function.Injective code := by
    intro x y h
    have l := congrArg (fun c:C=>c.1) h
    have h' := congrArg (fun c:C=>c.2.1) h
    have ml := congrArg (fun c:C=>c.2.2.1) h
    have mh := congrArg (fun c:C=>c.2.2.2) h
    change (a x).low=(a y).low at l
    change (a x).high=(a y).high at h'
    apply Subtype.ext
    apply LinearMap.ext; intro u
    apply LinearMap.ext; intro v
    apply (a x).sep
    · intro j
      have E := congrArg Subtype.val (congrFun ml j)
      change scalarMatrix (push ((a x).low j) x.val)=scalarMatrix (push ((a y).low j) y.val) at E
      rw [←l] at E
      exact DFunLike.congr_fun (DFunLike.congr_fun (scalarMatrix_inj E) u) v
    · intro j
      have E := congrFun mh j
      change edge (push ((a x).high j) x.val)=edge (push ((a y).high j) y.val) at E
      rw [←h'] at E
      have alt (z:X) (w:V d) : push ((a x).high j) z.val w w=0 := by
        change (a x).high j (z.val w w)=0
        rw [z.property.1 w,map_zero]
      exact DFunLike.congr_fun (DFunLike.congr_fun (edge_sep _ _ (alt x) (alt y) E) u) v
  have hcard := Nat.card_le_card_of_injective code inject
  have Dcard : Nat.card D=2^b := by
    rw [Module.natCard_eq_pow_finrank (K:=K),Subspace.dual_finrank_eq,Module.finrank_fin_fun,Nat.card_zmod]
  have Ecard : Nat.card (Edge d)=d.choose 2 := by
    rw [Nat.choose_two_right];exact Erdos1160Growth.SharpFamily.triangular_card d
  have cardL : Nat.card L ≤ 2^(8*k*d) := by
    convert count_small_rank_matrices d d (4*k) using 2 <;> ring
  have pb : p ≤ b := by
    obtain ⟨x⟩ := existsX
    obtain ⟨T,h,_⟩ := many_low_rank_components x budget
    have hb := Submodule.finrank_le T
    rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun] at hb
    dsimp [p];omega
  change Nat.card X ≤ _
  refine hcard.trans ?_
  change Nat.card ((Fin p→D) × (Fin (b-p)→D) × (Fin p→L) × (Fin (b-p)→Edge d→K))≤_
  simp only [Nat.card_prod,Nat.card_fun,Nat.card_fin,Dcard,Ecard,Nat.card_zmod]
  refine (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left cardL p)))).trans ?_
  simp only [←pow_mul,←pow_add]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  have ep : b*p + b*(b-p)=b*b := by rw [←Nat.mul_add,Nat.add_sub_of_le pb]
  nlinarith only [ep]
end OrbitUp.MinSpan
end

/- UniformAlternatingEntropy -/
section
namespace OrbitUp.MinSpan
theorem minspan_entropy {d b σ m : ℕ} (hd : d ≤ m) (hb : b ≤ m) :
    Nat.card (minimalAlternating d b σ) ≤
      2^((b-(σ-1))*d.choose 2 + 13*(m.sqrt+1)*m^2) := by
  classical
  by_cases hx : Nonempty (minimalAlternating d b σ)
  swap
  · haveI : IsEmpty (minimalAlternating d b σ) := not_nonempty_iff.mp hx
    simp
  let k := m.sqrt+1
  let p := σ-1-4*k
  have hk : 1 ≤ k := by dsimp [k];omega
  have budget : b+1 < 2*k*k := by
    have H : m < k*k := Nat.lt_succ_sqrt m
    have h : 0 < k*k := Nat.mul_pos hk hk
    nlinarith
  have pb : p ≤ b := by
    obtain ⟨β⟩ := hx
    obtain ⟨T,h,_⟩ := many_low_rank_components β budget
    have hh := Submodule.finrank_le T
    rw [Subspace.dual_finrank_eq,Module.finrank_fin_fun] at hh
    dsimp [p];omega
  have base := minspan_packing (d:=d) (σ:=σ) budget
  change Nat.card _ ≤ 2^(b*b+8*k*d*p+(b-p)*d.choose 2) at base
  refine base.trans (Nat.pow_le_pow_right (by decide) ?_)
  have D : d.choose 2 ≤ m*m := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul hd ((Nat.sub_le ..).trans hd))
  have sub : b-p≤(b-(σ-1))+4*k := by dsimp [p];omega
  have charge := (Nat.mul_le_mul_right (d.choose 2) sub).trans_eq (Nat.add_mul ..)
  have B : b*b ≤ k*(m*m) := (Nat.mul_le_mul hb hb).trans (Nat.le_mul_of_pos_left _ hk)
  have mid : 8*k*d*p ≤ 8*k*(m*m) := by
    rw [Nat.mul_assoc];exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hd (pb.trans hb))
  have last := Nat.mul_le_mul_left (4*k) D
  change b*b+8*k*d*p+(b-p)*d.choose 2 ≤ (b-(σ-1))*d.choose 2+13*k*m^2
  nlinarith only [B,mid,last,charge]
end OrbitUp.MinSpan
end

/- CanonicalReference -/
section
namespace CentralKernelCount
open CategoryTheory Erdos1160Growth.LowerTriangularUpper
open scoped commutatorElement
noncomputable def standardWord {t : ℕ} (v : BitGroup t) : List (Fin t) :=
  (bits_word t v).choose
theorem standardWord_correct {t : ℕ} (v : BitGroup t) : word bit (standardWord v)=v :=
  (bits_word t v).choose_spec
end CentralKernelCount
end

/- ExteriorSupport -/
section
namespace OrbitUp
abbrev Face (J : Type) (p : ℕ) := {s : Finset J // s.card=p}
def exteriorStep {J : Type} [DecidableEq J] (i : J) : (Face J 2→K) →ₗ[K] (Face J 3→K) where
  toFun v s := if hi:i∈s.val then v ⟨s.val.erase i,by rw [Finset.card_erase_of_mem hi,s.property]⟩ else 0
  map_add' x y := by funext s;by_cases h : i∈s.val <;> simp [h]
  map_smul' c x := by funext s;by_cases h : i∈s.val <;> simp [h]
theorem exteriorStep_out {J : Type} [DecidableEq J] (i : J) (w : Face J 2→K) (s : Face J 3) (h : i∉s.val) :
    exteriorStep i w s=0 := by simp [exteriorStep,h]
theorem exteriorStep_insert {J : Type} [DecidableEq J] (i : J) (w : Face J 2→K) (s : Face J 2) (h : i∉s.val) :
    exteriorStep i w ⟨insert i s.val,by rw [Finset.card_insert_of_notMem h,s.property]⟩=w s := by
  simp [exteriorStep,h]
end OrbitUp
end

/- LeadingSites -/
section
namespace OrbitUp.Shadow
universe u
variable {J : Type u} [Fintype J] [LinearOrder J]
def Leads (w : J→K) (i : J) : Prop := w i≠0 ∧ ∀j,i < j→w j=0
noncomputable def sites (F : Submodule K (J→K)) : Finset J := by
  classical exact Finset.univ.filter (fun i=>∃w:F,Leads w.val i)
theorem mem_sites (F : Submodule K (J→K)) (i : J) : i∈sites F ↔ ∃w:F,Leads w.val i := by
  classical simp [sites]
theorem count_sites (F : Submodule K (J→K)) : (sites F).card=Module.finrank K F := by
  classical
  let L := ↥(sites F)
  have witness (i : L) : ∃v:F,Leads v.val i.val := (mem_sites F i.val).mp i.property
  choose w hw using witness
  have ind : LinearIndependent K w := by
    rw [linearIndependent_iff']
    intro s c zero i hi
    by_contra hn
    let p := s.filter (fun j=>c j≠0)
    have non : p.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨hi,hn⟩⟩
    let k := p.max' non
    have hk := Finset.mem_filter.mp (show k∈p from p.max'_mem non)
    have z : (∑j∈s,c j*(w j).val k.val)=0 := by
      have h := congrArg (fun v:F=>v.val k.val) zero
      simpa only [Submodule.coe_sum,SetLike.val_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,ZeroMemClass.coe_zero,Pi.zero_apply] using h
    rw [Finset.sum_eq_single k] at z
    · exact (mul_ne_zero hk.2 (hw k).1) z
    · intro j hj ne
      by_cases cj : c j=0
      · simp [cj]
      have lt : j < k := lt_of_le_of_ne (p.le_max' j (Finset.mem_filter.mpr ⟨hj,cj⟩)) ne
      rw [(hw j).2 k.val lt,mul_zero]
    · exact fun h=>False.elim (h hk.1)
  have le := ind.fintype_card_le_finrank
  have ge : Module.finrank K F ≤ Fintype.card L := by
    let projection : F→ₗ[K] (L→K) := {toFun := fun w i=>w.val i.val,map_add' _ _ := rfl,map_smul' _ _ := rfl}
    have inj : Function.Injective projection := by
      apply LinearMap.ker_eq_bot.mp
      apply le_bot_iff.mp
      intro w hz
      change w=0
      by_contra nz
      have n : ∃i,w.val i≠0 := by
        by_contra! h
        exact nz (Subtype.ext (funext h))
      let support := Finset.univ.filter (fun i=>w.val i≠0)
      have hn : support.Nonempty := n.imp (fun i hi=>Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩)
      let i := support.max' hn
      have hi := (Finset.mem_filter.mp (show i∈support from support.max'_mem hn)).2
      have im : i∈sites F := (mem_sites F i).mpr ⟨w,hi,fun j hj=>by
        by_contra hyp
        exact hj.not_ge (support.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hyp⟩))⟩
      exact hi (congrFun (show projection w=0 from hz) ⟨i,im⟩)
    exact (LinearMap.finrank_le_finrank_of_injective inj).trans_eq (Module.finrank_fintype_fun_eq_card K)
  simpa only [L,Fintype.card_coe] using le_antisymm le ge
theorem union_defect {P Q : Type*} [DecidableEq Q] (f : P→Finset Q)
    (overlap : ∀i j,i≠j→((f i)∩(f j)).card ≤ 1) (s : Finset P) :
    (∑i∈s,(f i).card)≤(s.biUnion f).card+s.card.choose 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have e := Finset.card_union_add_card_inter (f i) (s.biUnion f)
    have inter : ((f i)∩s.biUnion f).card ≤ s.card := by
      rw [Finset.inter_biUnion]
      exact (Finset.card_biUnion_le_card_mul _ _ 1 (fun j hj=>overlap i j (fun h=>hi (h ▸ hj)))).trans_eq (Nat.mul_one _)
    simp only [Finset.sum_insert hi,Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Nat.choose_succ_succ,Nat.choose_one_right]
    change (f i).card+(∑j∈s,(f j).card)≤(f i∪s.biUnion f).card+(s.card+s.card.choose 2)
    omega
end OrbitUp.Shadow
end

/- SymmetricShadow -/
section
namespace OrbitUp.Shadow
noncomputable section
variable {d n : ℕ}
noncomputable def monoWeight (s : Multiset (Fin d)) :=
  (MonomialOrder.lex (σ:=Fin d)).toSyn (Multiset.toFinsupp s)
noncomputable def symOrder (n : ℕ) : LinearOrder (Sym (Fin d) n) :=
  LinearOrder.lift' (fun s=>monoWeight s.val) (fun x y eq=>Subtype.ext (Multiset.toFinsupp.injective ((MonomialOrder.lex (σ:=Fin d)).toSyn.injective eq)))
local instance {n : ℕ} : LinearOrder (Sym (Fin d) n) := symOrder n
theorem mono_cons_lt (i : Fin d) (s t : Sym (Fin d) n) :
    Sym.cons i s < Sym.cons i t ↔ s < t := by
  change monoWeight (i ::ₘ s.val) < monoWeight (i ::ₘ t.val) ↔ monoWeight s.val < monoWeight t.val
  simp only [monoWeight,←Multiset.singleton_add,map_add,add_lt_add_iff_left]
def multiples (s : Sym (Fin d) n) : Finset (Sym (Fin d) (n+1)) :=
  Finset.univ.image (fun i=>Sym.cons i s)
theorem overlap_multiples {s t : Sym (Fin d) n} (h : s≠t) : ((multiples s)∩multiples t).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  obtain ⟨hx₁,hx₂⟩ := Finset.mem_inter.mp hx
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx₁
  obtain ⟨j,_,e⟩ := Finset.mem_image.mp hx₂
  obtain ⟨hy₁,hy₂⟩ := Finset.mem_inter.mp hy
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hy₁
  obtain ⟨v,_,f⟩ := Finset.mem_image.mp hy₂
  have ij : i≠j := fun he=>h ((Sym.cons_inj_right i s t).mp (he ▸ e.symm))
  have eq (p q : Fin d) (e : Sym.cons p s=Sym.cons q t) : ({p} : Multiset (Fin d))+s.val={q}+t.val := by
    rw [Multiset.singleton_add,Multiset.singleton_add];exact congrArg (fun z : Sym (Fin d) (n+1)=>z.val) e
  have h₁ := eq _ _ e.symm
  have h₂ := eq _ _ f.symm
  have mulEq : ({i}:Multiset (Fin d))+{v}={j}+{u} := by
    apply add_right_cancel (b:=s.val)
    calc ({i}+{v})+s.val = {v}+({i}+s.val) := by ac_rfl
         _ = {v}+({j}+t.val) := by rw [h₁]
         _ = {j}+({v}+t.val) := by ac_rfl
         _ = {j}+({u}+s.val) := by rw [←h₂]
         _ = ({j}+{u})+s.val := by ac_rfl
  have hi : i∈({j}+{u}:Multiset (Fin d)) := mulEq ▸ (show i∈({i}+{v}:Multiset (Fin d)) by simp)
  have iu : i=u := by simpa [ij] using hi
  rw [iu]
end
end OrbitUp.Shadow
end

/- ExteriorSharp -/
section
namespace OrbitUp.Shadow
noncomputable section
variable {d n : ℕ}
def forgetFace (s : Face (Fin d) n) : Sym (Fin d) n := ⟨s.val.val,s.property⟩
theorem forgetFace_inj : Function.Injective (@forgetFace d n) := fun x y eq=>Subtype.ext (Finset.val_inj.mp (congrArg Subtype.val eq))
local instance {n : ℕ} : LinearOrder (Sym (Fin d) n) := symOrder n
local instance {n : ℕ} : LinearOrder (Face (Fin d) n) := LinearOrder.lift' forgetFace forgetFace_inj
def extendFace (s : Face (Fin d) 2) (i : Fin d) (hi : i∉s.val) : Face (Fin d) 3 :=
  ⟨insert i s.val,by rw [Finset.card_insert_of_notMem hi,s.property]⟩
theorem forget_extend (s : Face (Fin d) 2) (i : Fin d) (hi : i∉s.val) :
    forgetFace (extendFace s i hi)=Sym.cons i (forgetFace s) := Subtype.ext (Finset.insert_val_of_notMem hi)
theorem exterior_leads {w : Face (Fin d) 2→K} {s : Face (Fin d) 2} (hs : Leads w s) (i : Fin d) (hi : i∉s.val) :
    Leads (exteriorStep i w) (extendFace s i hi) := by
  refine ⟨fun eq=>hs.1 ((exteriorStep_insert i w s hi).symm.trans eq),?_⟩
  intro t ht
  by_cases h : i∈t.val
  · let u : Face (Fin d) 2 := ⟨t.val.erase i,by rw [Finset.card_erase_of_mem h,t.property]⟩
    have miss : i∉u.val := by simp [u]
    have eq : extendFace u i miss=t := Subtype.ext (Finset.insert_erase h)
    change forgetFace (extendFace s i hi) < forgetFace t at ht
    rw [←eq,forget_extend,forget_extend] at ht
    have hu : forgetFace s < forgetFace u := (mono_cons_lt i _ _).mp ht
    exact ((congrArg ((exteriorStep i) w) eq.symm).trans (exteriorStep_insert _ _ _ miss)).trans (hs.2 _ hu)
  · exact exteriorStep_out i w t h
def extensions (s : Face (Fin d) 2) : Finset (Face (Fin d) 3) :=
  Finset.univ.image (fun i : {i // i∉s.val}=>extendFace s i.val i.property)
theorem card_extensions (s : Face (Fin d) 2) : (extensions s).card=d-2 := by
  have inj : Function.Injective (fun i : {i // i∉s.val} =>extendFace s i.val i.property) := by
    intro i j eq
    have im := congrArg forgetFace eq
    rw [forget_extend,forget_extend] at im
    exact Subtype.ext ((Sym.cons_inj_left ..).mp im)
  rw [extensions,Finset.card_image_of_injective _ inj,Finset.card_univ,Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe,s.property]
theorem extension_overlap {s t : Face (Fin d) 2} (hne : s≠t) :
    ((extensions s)∩extensions t).card ≤ 1 := by
  have inc (s : Face (Fin d) 2) (x : Face (Fin d) 3) (h : x∈extensions s) : forgetFace x∈multiples (forgetFace s) := by
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,(forget_extend ..).symm⟩
  apply Finset.card_le_one.mpr
  intro x hx y hy
  apply forgetFace_inj
  have h := Finset.card_le_one.mp (overlap_multiples (fun eq=>hne (forgetFace_inj eq)))
  exact h _ (Finset.mem_inter.mpr ⟨inc _ _ (Finset.mem_inter.mp hx).1,inc _ _ (Finset.mem_inter.mp hx).2⟩)
    _ (Finset.mem_inter.mpr ⟨inc _ _ (Finset.mem_inter.mp hy).1,inc _ _ (Finset.mem_inter.mp hy).2⟩)
theorem sharp_exterior_shadow (d : ℕ) (F : Submodule K (Face (Fin d) 2 → K)) (W : Submodule K (Face (Fin d) 3 → K))
    (hs : ∀i,F.map (exteriorStep i) ≤ W) :
    (d-2)*Module.finrank K F ≤ Module.finrank K W+(Module.finrank K F).choose 2 := by
  classical
  have cov : (sites F).biUnion extensions⊆sites W := by
    intro x hx
    obtain ⟨s,h,hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w,hw⟩ := (mem_sites F s).mp h
    exact (mem_sites W _).mpr ⟨⟨_,hs i.val ⟨w.val,w.property,rfl⟩⟩,exterior_leads hw i.val i.property⟩
  have h := union_defect extensions (fun _ _ n=>extension_overlap n) (sites F)
  simp only [card_extensions,Finset.sum_const,smul_eq_mul,count_sites] at h
  rw [Nat.mul_comm]
  exact h.trans (Nat.add_le_add_right ((Finset.card_le_card cov).trans_eq (count_sites W)) _)
end
end OrbitUp.Shadow
end

/- ExteriorSyzygy -/
section
namespace OrbitUp.Shadow
noncomputable def wedgeSum {d : ℕ} (F : Submodule K (Face (Fin d) 2→K)) :
    (Fin d→F)→ₗ[K] (Face (Fin d) 3→K) :=
  ∑i : Fin d,((exteriorStep i).comp F.subtype).comp (LinearMap.proj i)
theorem wedgeSum_apply {d : ℕ} (F : Submodule K (Face (Fin d) 2→K)) (c : Fin d→F) (s : Face (Fin d) 3) :
    wedgeSum F c s=∑i : Fin d,exteriorStep i (c i).val s := by
  simp only [wedgeSum,LinearMap.sum_apply,LinearMap.comp_apply,Submodule.subtype_apply,LinearMap.proj_apply,Finset.sum_apply]
end OrbitUp.Shadow
end

/- BinaryFactor -/
section
namespace BinaryFactor
abbrev Bit := ZMod 2
variable {G : Type*} [Group G]
abbrev C₁ (G : Type*) := G → Bit
namespace Cocycle
end Cocycle
end BinaryFactor
end

/- BinaryInflation -/
section
namespace BinaryFactor.Cocycle
open BinaryFactor
variable {G : Type*} [Group G]
def character (a : C₁ G) : Prop := ∀ x y,a (x*y)=a x+a y
end BinaryFactor.Cocycle
end

/- BinarySpaces -/
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
def characters : Submodule Bit (C₁ G) where
  carrier := {u | character u}
  zero_mem' := fun _ _ => by change (0:Bit)=0+0;simp
  add_mem' := by
    intro a b ha hb x y
    change a (x*y)+b (x*y)=(a x+b x)+(a y+b y)
    rw [ha x y,hb x y];abel
  smul_mem' := by
    intro k a ha x y
    change k*a (x*y)=k*a x+k*a y
    rw [ha x y,mul_add]
variable {G}
end BinaryFactor
end

/- BinaryBetti -/
section
namespace BinaryFactor
open Cocycle
variable (G : Type*) [Group G]
noncomputable abbrev r₁ := Module.finrank Bit (characters G)
variable {G}
end BinaryFactor
end

/- GenuineInflation -/
section
namespace BinaryFactor
open Cocycle
variable {E G H : Type*} [Group E] [Group G] [Group H]
def characterPull (f : E→*G) : characters G →ₗ[Bit] characters E where
  toFun a := ⟨fun x=>a.val (f x),fun x y=>by
    change a.val (f (x*y))=a.val (f x)+a.val (f y)
    rw [map_mul,a.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def characterCongr (i : E≃*G) : characters G ≃ₗ[Bit] characters E :=
  LinearEquiv.ofLinear (characterPull i.toMonoidHom) (characterPull i.symm.toMonoidHom)
    (by ext a x;change a.val (i.symm (i x))=a.val x;rw [i.symm_apply_apply])
    (by ext a x;change a.val (i (i.symm x))=a.val x;rw [i.apply_symm_apply])
end BinaryFactor
end

/- ElementaryParameters -/
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
open BinaryFactor
abbrev Vectors (d : ℕ) := Multiplicative (Fin d → Bit)
end BinaryFactor.Elementary
end

/- PairCup -/
section
namespace BinaryFactor.Elementary
open OrbitUp Cocycle Erdos1160Growth.LowerTriangularUpper
abbrev Pairs (d : ℕ) := Face (Fin d) 2 → Bit
def pair {d : ℕ} (i j : Fin d) (h : i ≠ j) : Face (Fin d) 2 := ⟨{i,j},Finset.card_pair h⟩
structure TripleRep {d : ℕ} (s : Face (Fin d) 3) where
  i : Fin d
  j : Fin d
  k : Fin d
  hij : i≠j
  hik : i≠k
  hjk : j≠k
  support : s.val={i,j,k}
noncomputable def tripleRep {d : ℕ} (s : Face (Fin d) 3) : TripleRep s :=
  Classical.choice (by obtain ⟨i,j,k,h₁,h₂,h₃,h₄⟩ := Finset.card_eq_three.mp s.property
                       exact ⟨⟨i,j,k,h₁,h₂,h₃,h₄⟩⟩)
end BinaryFactor.Elementary
end

/- PartialShadow -/
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.Shadow
open BinaryFactor.Elementary (pair TripleRep tripleRep)
variable {d b : ℕ}
theorem partial_exterior_codimension (P : Submodule K (Face (Fin d) 2→K)) {v : ℕ}
    (hv : v ≤ Module.finrank K P) :
    Module.finrank K (LinearMap.ker (wedgeSum P))+(d-2)*v ≤ d*Module.finrank K P+v.choose 2 := by
  classical
  obtain ⟨h,inj⟩ := finrank_le_iff_exists_linearMap.mp
    (show Module.finrank K (V v) ≤ Module.finrank K P from (Module.finrank_fin_fun _).le.trans hv)
  let f := P.subtype.comp h
  have fi : Function.Injective f := P.subtype_injective.comp inj
  let U := f.range
  have rank : Module.finrank K U=v :=
    (LinearMap.finrank_range_of_inj fi).trans (Module.finrank_fin_fun K)
  let W := LinearMap.range (wedgeSum P)
  have inc (i : Fin d) : U.map (exteriorStep i) ≤ W := by
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨Pi.single i (h x),?_⟩
    funext z
    rw [wedgeSum_apply,Fintype.sum_eq_single i]
    · simp [f]
    · intro j hj;rw [Pi.single_eq_of_ne hj];simp
  have sh := sharp_exterior_shadow d U W inc
  rw [rank] at sh
  have rn := LinearMap.finrank_range_add_finrank_ker (wedgeSum P)
  rw [Module.finrank_pi_fintype] at rn
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at rn
  change Module.finrank K W+_=d*_ at rn
  omega
theorem eval_wedge_sum (P : Submodule K (Face (Fin d) 2→K)) (c : Fin d→P) (z : Face (Fin d) 3)
    (t : TripleRep z) :
    wedgeSum P c z=(c t.i).val (pair t.j t.k t.hjk)+(c t.j).val (pair t.i t.k t.hik)+(c t.k).val (pair t.i t.j t.hij) := by
  classical
  have entry (i j k : Fin d) (ne : j≠k) (hi : i≠j) (hk : i≠k) (eq : z.val=insert i (pair j k ne).val) :
      exteriorStep i (c i).val z=(c i).val (pair j k ne) := by
    have miss : i∉(pair j k ne).val := by simp [pair,hi,hk]
    exact (congrArg ((exteriorStep i) (c i).val) (show z=⟨insert i (pair j k ne).val,_⟩ from Subtype.ext eq)).trans (exteriorStep_insert _ _ _ miss)
  have hi := entry _ _ _ t.hjk t.hij t.hik t.support
  have hj := entry _ _ _ t.hik t.hij.symm t.hjk (t.support.trans (Finset.insert_comm ..))
  have hk := entry _ _ _ t.hij t.hik.symm t.hjk.symm (by rw [t.support];ext;simp [pair];tauto)
  rw [wedgeSum_apply,←Finset.sum_subset (Finset.subset_univ z.val) (fun i _ h=>exteriorStep_out _ _ _ h)]
  change (∑i∈z.val,exteriorStep i (c i).val z)=_
  conv_lhs => arg 1;rw [t.support]
  simp [hi,hj,hk,t.hij,t.hik,t.hjk,add_assoc]
end Erdos1160.Sims
end

/- CharacterBasis -/
section
namespace BinaryFactor.Elementary
open Erdos1160Growth.LowerTriangularUpper
def characterDual (d : ℕ) : characters (Vectors d) ≃ₗ[Bit] Module.Dual Bit (V d) where
  toFun a :=
    let h : V d →+ Bit := {
      toFun := fun x => a.val (.ofAdd x)
      map_zero' := by have h := a.property 1 1; change a.val 1=0; simpa using h
      map_add' x y := a.property (.ofAdd x) (.ofAdd y)
    }
    h.toZModLinearMap 2
  invFun f := ⟨fun x=>f x.toAdd,fun x y=>f.map_add x.toAdd y.toAdd⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end BinaryFactor.Elementary
end

/- FixedFrattiniCup -/
section
namespace BinaryFactor.Elementary
open Cocycle
theorem vectors_char_rank (d : ℕ) : r₁ (Vectors d)=d := by
  change Module.finrank Bit (characters (Vectors d))=_
  rw [(characterDual d).finrank_eq,Subspace.dual_finrank_eq,Module.finrank_fin_fun]
end BinaryFactor.Elementary
end

/- MarkedBracketRows -/
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.Shadow BinaryFactor BinaryFactor.Elementary Erdos1160.DeepJacobi
open Erdos1160.CentralLifts.Survival (jacobiRank)
open scoped commutatorElement
variable {Q : Type} [Group Q] [Finite Q] {r : ℕ}
private noncomputable def choosePair (z : Face (Fin r) 2) :
    {v : Fin r × Fin r // v.1≠v.2 ∧ z.val={v.1,v.2}} :=
  Classical.choice (by obtain ⟨i,j,hn,he⟩ := Finset.card_eq_two.mp z.property
                       exact ⟨⟨(i,j),hn,he⟩⟩)
private noncomputable def bracketMark (x : Fin r→Q) (z : Face (Fin r) 2) : Second Q :=
  secondBracket (x (choosePair z).val.1) (x (choosePair z).val.2)
private theorem bracket_pair (x : Fin r→Q) (hb : ∀w:Second Q,w*w=1) (i j : Fin r) (ne : i≠j) :
    bracketMark x (pair i j ne)=secondBracket (x i) (x j) := by
  let z := pair i j ne
  let u := (choosePair z).val.1
  let v := (choosePair z).val.2
  have he : ({i,j}:Finset (Fin r))={u,v} := (choosePair z).property.2
  have hs : ({i,j}:Set (Fin r))={u,v} := by simpa using congrArg (fun s:Finset (Fin r)=>(s:Set (Fin r))) he
  change secondBracket (x u) (x v)=secondBracket (x i) (x j)
  obtain ⟨hu,hv⟩|⟨hu,hv⟩ := Set.pair_eq_pair_iff.mp hs
  · rw [←hu,←hv]
  · rw [←hu,←hv]
    let w := secondBracket (x i) (x j)
    have inv : w⁻¹=w := inv_eq_of_mul_eq_one_left (hb w)
    exact (show secondBracket (x j) (x i)=w⁻¹ from Subtype.ext (commutatorElement_inv ..).symm).trans inv
private theorem bracket_gen (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) :
    Subgroup.closure (Set.range (bracketMark x))=⊤ := by
  let C := Subgroup.closure (Set.range (fun z=>(bracketMark x z).val))
  have cent : C ≤ Subgroup.center Q := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨z,rfl⟩;exact hc (bracketMark x z).property
  letI : C.Normal := ⟨fun a ha b=>by rw [Subgroup.mem_center_iff.mp (cent ha) b,mul_inv_cancel_right];exact ha⟩
  let f := QuotientGroup.mk' C
  have gen : Subgroup.closure (Set.range (f ∘ x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective f (QuotientGroup.mk'_surjective _)]
  have comm : IsMulCommutative (Subgroup.closure (Set.range (f ∘ x))) := by
    apply Subgroup.isMulCommutative_closure
    rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
    rcases eq_or_ne i j with rfl|hne
    · rfl
    · apply commutatorElement_eq_one_iff_mul_comm.mp
      change ⁅f (x i),f (x j)⁆=1
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr
        (Subgroup.subset_closure ⟨pair i j hne,congrArg Subtype.val (bracket_pair x hb i j hne)⟩)
  rw [gen] at comm
  have derived : Second Q ≤ C := by
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    apply (QuotientGroup.eq_one_iff _).mp
    change f ⁅a,b⁆=1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (comm.is_comm.comm (⟨f a,trivial⟩:(⊤:Subgroup (Q⧸C))) ⟨f b,trivial⟩)
  apply Subgroup.map_injective (Second Q).subtype_injective
  rw [MonoidHom.map_closure,←Set.range_comp,←MonoidHom.range_eq_map,Subgroup.range_subtype]
  exact le_antisymm (by apply (Subgroup.closure_le _).mpr;rintro _ ⟨z,rfl⟩;exact (bracketMark x z).property) derived
private noncomputable def rowMap (x : Fin r→Q) : characters (Second Q)→ₗ[K] Pairs r where
  toFun a z := a.val (bracketMark x z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def toHom {A : Type} [Group A] (a : characters A) : A→*C₂ where
  toFun v := .ofAdd (a.val v)
  map_mul' u v := congrArg Multiplicative.ofAdd (a.property u v)
  map_one' := by change a.val 1=0;simpa using a.property 1 1
private theorem row_inj (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) :
    Function.Injective (rowMap x) := by
  intro a b he
  have equal : toHom a=toHom b := MonoidHom.eq_of_eqOn_dense (bracket_gen x hx hc hb) (by
    rintro _ ⟨z,rfl⟩;exact congrArg Multiplicative.ofAdd (congrFun he z))
  exact Subtype.ext (funext fun y=>congrArg (fun f : Second Q→*C₂=>(f y).toAdd) equal)
private def scalarRow (a : JacobiDual Q) (v : Q) : characters (Second Q) :=
  ⟨fun w=>(a.val w v).toAdd,fun w u=>congrArg (fun f : Q→*C₂=>(f v).toAdd) (a.val.map_mul w u)⟩
private noncomputable def rows (x : Fin r→Q) (a : JacobiDual Q) : Fin r→(rowMap x).range :=
  fun i=>⟨rowMap x (scalarRow a (x i)),⟨_,rfl⟩⟩
private theorem rows_cancel (x : Fin r→Q) (hb : ∀w:Second Q,w*w=1) (a : JacobiDual Q) :
    rows x a∈(wedgeSum (rowMap x).range).ker := by
  funext z
  let t := tripleRep z
  rw [eval_wedge_sum _ _ _ t]
  change (a.val (bracketMark x _) (x t.i)).toAdd+(a.val (bracketMark x _) (x t.j)).toAdd+
    (a.val (bracketMark x _) (x t.k)).toAdd=0
  rw [bracket_pair x hb,bracket_pair x hb,bracket_pair x hb]
  exact (show ∀u v w : C₂,u=v*w⁻¹→u.toAdd+v.toAdd+w.toAdd=0 by decide) _ _ _ (a.property ..)
private theorem rows_inj (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1) : Function.Injective (rows x) := by
  intro a b he
  apply Subtype.ext
  apply MonoidHom.ext
  intro w
  apply MonoidHom.eq_of_eqOn_dense hx
  rintro _ ⟨i,rfl⟩
  have h := row_inj x hx hc hb (congrArg Subtype.val (congrFun he i))
  exact congrArg (fun f : characters (Second Q)=>Multiplicative.ofAdd (f.val w)) h
theorem marked_jacobi_rank_bound {b : ℕ} (x : Fin r→Q) (hx : Subgroup.closure (Set.range x)=⊤)
    (hc : Second Q ≤ Subgroup.center Q) (hb : ∀w:Second Q,w*w=1)
    (hw : Nat.card (Second Q)=2^b) (hr : r-1 ≤ b) :
    jacobiRank Q+(r-1).choose 2 ≤ r*b := by
  obtain ⟨e⟩ := Erdos1160Growth.LowerTriangularUpper.exist_elementary_coords hb hw
  let P := (rowMap x).range
  have hP : Module.finrank K P=b :=
    (LinearMap.finrank_range_of_inj (row_inj x hx hc hb)).trans
      ((characterCongr e).finrank_eq.symm.trans (vectors_char_rank b))
  let emb (a : JacobiDual Q) : (wedgeSum P).ker := ⟨rows x a,rows_cancel x hb a⟩
  have he : Function.Injective emb := fun a b eq=>rows_inj x hx hc hb (congrArg Subtype.val eq)
  have comp := Nat.card_le_card_of_injective emb he
  change Nat.card (Additive (JacobiDual Q)) ≤ Nat.card (wedgeSum P).ker at comp
  rw [Module.natCard_eq_pow_finrank (K:=K) (V:=Additive (JacobiDual Q)),
    Module.natCard_eq_pow_finrank (K:=K) (V:=(wedgeSum P).ker),Nat.card_zmod] at comp
  have dim : jacobiRank Q ≤ Module.finrank K (wedgeSum P).ker := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp comp
  have sh := partial_exterior_codimension P (v:=r-1) (hP ▸ hr)
  rw [hP] at sh
  have twice : 2*((r-1).choose 2)=(r-2)*(r-1) := by
    rcases r with _|(_|r)
    · decide
    · decide
    · change 2*(r+1).choose 2=r*(r+1)
      simpa only [Nat.choose_one_right,Nat.mul_comm] using (Nat.add_one_mul_choose_eq r 1).symm
  omega
end Erdos1160.Sims
end

/- SimsFrame -/
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second)
open Erdos1160.CentralLifts.Survival
open scoped commutatorElement
abbrev W (b : ℕ) := Multiplicative (V b)
structure Shape (m d σ : ℕ) where
  r : ℕ
  n : ℕ
  h : ℕ
  t : ℕ
  r_le : r≤σ
  n_le : n+σ ≤ d
  ht_le : h+t ≤ m
  rootOrder : Fin r→Fin (2^m)
  extOrder : Fin n→Fin (2^m)
  rootVec : Fin r→V d
  baseVec : Fin σ→V d
  extVec : Fin n→V d
def rootPattern {m d b σ} (S : Shape m d σ) (β : Tensor d b) (z : PairSlot S.r) : W b :=
  .ofAdd (β (S.rootVec z.1) (S.rootVec (second z)))
def extraPattern {m d b σ} (S : Shape m d σ) (β : Tensor d b) : ExtraSlot S.n σ→W b :=
  Sum.elim (fun p=>.ofAdd (β (S.extVec p.1) (S.baseVec p.2)))
    (fun z=>.ofAdd (β (S.extVec z.1) (S.extVec (second z))))
structure SimsFrame {m d b σ} (S : Shape m d σ) (β : Tensor d b) (E : FiniteGrp.{0}) where
  Q : FiniteGrp.{0}
  H : FiniteGrp.{0}
  root : ExtensionMark (W b) Q S.r
  central : root.incl.range ≤ Subgroup.center Q
  rootPowers : ∀i,∃v,root.x i^((S.rootOrder i).val+1)=root.incl v
  rootComms : ∀z:PairSlot S.r,⁅root.x z.1,root.x (second z)⁆=root.incl (rootPattern S β z)
  rootSize : (∏i,((S.rootOrder i).val+1))*Nat.card (W b) ≤ Nat.card Q
  qsize : Nat.card Q=2^S.h
  hsize : Nat.card H=2^(S.h+S.t)
  π : H→*Q
  onto : Function.Surjective π
  kerFrattini : π.ker ≤ frattini H
  kerSize : Nat.card π.ker ≤ 2^S.t
  base : Fin σ→H
  gen : Subgroup.closure (Set.range base)=⊤
  classTwo : Second Q ≤ Subgroup.center Q
  elementary : ∀w:Second Q,w*w=1
  dimDerived : Nat.card (Second Q)=2^b
  ext : ExtensionMark H E S.n
  powers : Fin S.n→H
  comms : ExtraSlot S.n σ→H
  patterns : ∀z,π (comms z)=root.incl (extraPattern S β z)
  fits : ExtensionFits ext base (fun i=>(S.extOrder i).val+1) powers comms
  size : (∏i,((S.extOrder i).val+1))*Nat.card H ≤ Nat.card E
  tail : S.t ≤ m-d-b
end Erdos1160.Sims
end

/- SimsSeed -/
section
namespace Erdos1160.Sims
open OrbitUp OrbitUp.MinSpan OrbitUp.BoundedMatrices
open Erdos1160.DeepJacobi (Second secondBracket)
open Erdos1160Growth.LowerTriangularUpper (squareCore exist_elementary_coords)
structure Seed (G : Type) [Group G] [Finite G] (d b σ : ℕ) where
  p : G→*W d
  onto : Function.Surjective p
  ker : p.ker=squareCore G
  a : Second (headQuot G)≃*W b
  β : minimalAlternating d b σ
  compatible : ∀x y,β.val (p x).toAdd (p y).toAdd=(a (secondBracket (headMap G x) (headMap G y))).toAdd
  H : Subgroup G
  x : Fin σ→H
  generates : Subgroup.closure (Set.range x)=⊤
  derived : (commutator H).map H.subtype=commutator G
  subrank : Module.finrank K (vectorSub (H.map p))=σ
theorem seed_exists {G : Type} [Group G] [Finite G] {d m : ℕ} (size : Nat.card G=2^m)
    (rank : Nat.card (G⧸squareCore G)=2^d) : ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ Nonempty (Seed G d b σ) := by
  classical
  have pg := IsPGroup.of_card size
  let π := QuotientGroup.mk' (squareCore G)
  have sq (v : G⧸squareCore G) : v*v=1 := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (squareCore G) v
    rw [←map_mul];exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨w,rfl⟩)
  obtain ⟨i⟩ := exist_elementary_coords sq rank
  let p := i.toMonoidHom.comp π
  have sp := i.surjective.comp (QuotientGroup.mk'_surjective (squareCore G))
  have kp : p.ker=squareCore G := by
    ext x
    change i (π x)=1 ↔ x∈_
    rw [←i.map_one,i.injective.eq_iff];exact QuotientGroup.eq_one_iff _
  obtain ⟨b,hb⟩ := ((pg.to_quotient (commutatorTail G)).to_subgroup (Second (headQuot G))).exists_card_eq
  obtain ⟨a⟩ := exist_elementary_coords (head_conditions G).2 hb
  obtain ⟨β,alt,full,spec⟩ := exists_head_tensor p sp kp (headMap G) (QuotientGroup.mk'_surjective _)
    (head_conditions G).1 a
  let prop (s : ℕ) := ∃S : Submodule K (V d),valuesOn β S=⊤ ∧Module.finrank K S=s
  have ex : ∃s,prop s := ⟨_,⊤,full,rfl⟩
  let σ := Nat.find ex
  obtain ⟨S,hS,hσ⟩ := Nat.find_spec ex
  have minimal (T : Submodule K (V d)) (hT : valuesOn β T=⊤) : σ ≤ Module.finrank K T :=
    Nat.find_min' ex ⟨T,hT,rfl⟩
  obtain ⟨H,x,hx,hs⟩ := lift_subspace p sp S
  have cov (u : S) : ∃x:H,(p x.val).toAdd=u.val := by
    obtain ⟨w,hw,eq⟩ := (show u.val∈vectorSub (H.map p) from hs ▸ u.property)
    exact ⟨⟨w,hw⟩,congrArg Multiplicative.toAdd eq⟩
  have hh := subgroup_of_spanning pg p a β spec H S hS cov
  have sd := minimal ⊤ full
  rw [finrank_top,Module.finrank_fin_fun] at sd
  obtain ⟨T,hT,small⟩ := minimal_commutator_span β alt full
  have ss := (minimal T hT).trans small
  rw [Module.finrank_fin_fun] at ss
  obtain ⟨t,ht⟩ := (pg.to_subgroup (commutatorTail G)).exists_card_eq
  have bound := head_size_budget size p sp kp hb ht
  refine ⟨b,σ,by omega,sd,by omega,⟨?_,?_,?_,?_,?_,?_,H,?_,?_,hh,?_⟩⟩
  · exact p
  · exact sp
  · exact kp
  · exact a
  · exact ⟨β,alt,full,⟨S,hS,hσ⟩,minimal⟩
  · exact spec
  · exact x ∘ (finCongr hσ).symm
  · rw [Set.range_comp,(finCongr hσ).symm.surjective.range_eq,Set.image_univ];exact hx
  · rw [hs];exact hσ
end Erdos1160.Sims
end

/- SeedPattern -/
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second secondBracket)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {d b σ : ℕ} (C : Seed G d b σ)
noncomputable def Seed.headEquiv : Second (headSub C.H)≃*W b :=
  (derivedHeadEquiv C.H C.derived).trans C.a
noncomputable def Seed.headIncl : W b→*headSub C.H :=
  (Second (headSub C.H)).subtype.comp C.headEquiv.symm.toMonoidHom
theorem Seed.headIncl_range : C.headIncl.range=Second (headSub C.H) := by
  rw [Seed.headIncl,MonoidHom.range_comp,MonoidHom.range_eq_top_of_surjective _ C.headEquiv.symm.surjective,
    ←MonoidHom.range_eq_map,Subgroup.range_subtype]
theorem Seed.headIncl_value (v : W b) : (C.headIncl v).val=(C.a.symm v).val := by
  have e := C.headEquiv.apply_symm_apply v
  change C.a (derivedHeadEquiv C.H C.derived (C.headEquiv.symm v))=v at e
  exact congrArg (fun z:Second (headQuot G)=>z.val) (C.a.injective (e.trans (C.a.apply_symm_apply v).symm))
theorem Seed.compatible_of_lift (x y : G) (u : C.H) (e : u.val=⁅x,y⁆) :
    toHeadSub C.H u=C.headIncl (.ofAdd (C.β.val (C.p x).toAdd (C.p y).toAdd)) := by
  apply Subtype.ext
  rw [C.headIncl_value,C.compatible]
  change _ = (C.a.symm (C.a (secondBracket _ _))).val
  rw [C.a.symm_apply_apply]
  change headMap G u.val=⁅headMap G x,headMap G y⁆
  rw [e,map_commutatorElement]
theorem Seed.commutator_le : commutator G ≤ C.H :=
  C.derived ▸ Subgroup.map_subtype_le _
theorem Seed.head_order : Nat.card (Second (headSub C.H))=2^b := by
  rw [Nat.card_congr C.headEquiv.toEquiv]
  change Nat.card (Fin b→ZMod 2)=_
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
end Erdos1160.Sims
end

/- ClassTwoData -/
section
namespace ClassTwoProfile
open scoped commutatorElement
abbrev Cyc (n : ℕ) := Multiplicative (ZMod (2^n))
abbrev Factors {r : ℕ} (e : Fin r → ℕ) := (i : Fin r) → Cyc (e i)
def gen {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : Factors e :=
  Pi.mulSingle i (Multiplicative.ofAdd 1)
theorem gen_pow {r : ℕ} (e : Fin r → ℕ) (i : Fin r) : gen e i ^ (2^(e i)) = 1 := by
  rw [gen,← Pi.mulSingle_pow]
  have h : (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ (2^(e i)) = 1 := by
    change (2^(e i)) • (1 : ZMod (2^(e i))) = 0
    simp [nsmul_eq_mul]
  rw [h,Pi.mulSingle_one]
theorem gen_closure {r : ℕ} (e : Fin r → ℕ) : Subgroup.closure (Set.range (gen e)) = ⊤ := by
  apply top_unique
  intro v hv
  clear hv
  induction v using Pi.mulSingle_induction with
  | one => exact Subgroup.one_mem _
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy
  | mulSingle i x =>
    let j := x.toAdd.val
    have hx : x = (Multiplicative.ofAdd (1 : ZMod (2^(e i)))) ^ j := by
      change x.toAdd = j • (1 : ZMod (2^(e i)))
      simp [j,nsmul_eq_mul]
    rw [hx,Pi.mulSingle_pow]
    exact Subgroup.pow_mem _ (show gen e i ∈ Subgroup.closure (Set.range (gen e)) from Subgroup.subset_closure ⟨i,rfl⟩) _
theorem card_factors {r : ℕ} (e : Fin r → ℕ) : Nat.card (Factors e) = 2^(∑ i, e i) := by
  rw [Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => Nat.card_zmod _
namespace Data
abbrev Tor (k : ℕ) (b : Fin s→ℕ) := {w : Factors b // w^(2^k) = 1}
end Data
end ClassTwoProfile
end

/- ParameterSizes -/
section
namespace ClassTwoProfile
variable {d s : ℕ} (e : Fin d→ℕ) (b : Fin s→ℕ)
lemma card_tor (k : ℕ) :
    Nat.card (Data.Tor k b) = 2^(∑ i, min k (b i)) := by
  let f : Data.Tor k b ≃ ∀ i, (powMonoidHom (2^k) : Cyc (b i) →* Cyc (b i)).ker :=
    { toFun := fun w i => ⟨w.1 i,congrFun w.2 i⟩
      invFun := fun w => ⟨fun i => w i, funext (fun i => (w i).2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr f,Nat.card_pi,←Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [IsCyclic.card_powMonoidHom_ker]
  change (Nat.card (ZMod (2^(b i)))).gcd (2^k) = _
  rw [Nat.card_zmod]
  rcases le_total k (b i) with h|h
  · rw [min_eq_left h, Nat.gcd_eq_right (pow_dvd_pow 2 h)]
  · rw [min_eq_right h, Nat.gcd_eq_left (pow_dvd_pow 2 h)]
end ClassTwoProfile
end

/- SquareSizes -/
section
namespace ClassTwoProfile
open Erdos1160Growth.LowerTriangularUpper
lemma squareCore_eq_range (A : Type*) [CommGroup A] : squareCore A = (powMonoidHom 2 : A→*A).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a,rfl⟩
    exact ⟨a,sq a⟩
  · rintro _ ⟨u,rfl⟩
    exact Subgroup.subset_closure ⟨u,(sq u).symm⟩
lemma squareCore_size {A : Type} [CommGroup A] {s : ℕ} {b : Fin s→ℕ}
    (f : A ≃* Factors b) (hb : ∀ i,0 < b i) :
    Nat.card (squareCore A)*2^s = 2^(∑ i,b i) := by
  let g := (powMonoidHom 2 : A→*A)
  let kerE : g.ker ≃ Data.Tor 1 b :=
    { toFun := fun w => ⟨f w.val,by change (f w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      invFun := fun w => ⟨f.symm w.val,by change (f.symm w.val)^2=1; rw [←map_pow,show w.val^2=1 from w.2,map_one]⟩
      left_inv := by intro w; exact Subtype.ext (f.symm_apply_apply _)
      right_inv := by intro w; exact Subtype.ext (f.apply_symm_apply _) }
  have hk : Nat.card g.ker = 2^s := by
    rw [Nat.card_congr kerE,card_tor]
    have he (i : Fin s) : min 1 (b i)=1 := min_eq_left (show 1 ≤ b i from hb i)
    simp [he]
  have h := g.ker.index_mul_card
  rw [Subgroup.index_ker,hk, Nat.card_congr f.toEquiv, card_factors] at h
  rw [squareCore_eq_range]
  exact h
end ClassTwoProfile
end

/- CyclicCoords -/
section
namespace ClassTwoProfile
lemma exists_cyclic_coords (A : Type) [CommGroup A] [Finite A] {m : ℕ}
    (hc : Nat.card A = 2^m) :
    ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ (∑ i, e i)=m ∧ Nonempty (A ≃* Factors e) := by
  classical
  obtain ⟨ι,_,n,hn,⟨f⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have hor : ∏ i, n i = 2^m := by
    rw [←hc, Nat.card_congr f.toEquiv,Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => (Nat.card_zmod _).symm
  have pow (i : ι) : ∃ a ≤ m, n i = 2^a := by
    apply (Nat.dvd_prime_pow Nat.prime_two).mp
    rw [←hor]
    exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  let e' (i : ι) := (pow i).choose
  have hn' (i : ι) : n i = 2^(e' i) := (pow i).choose_spec.2
  let t := Fintype.equivFin ι
  let e := e' ∘ t.symm
  let reindex : ((i : ι) → Multiplicative (ZMod (n i))) ≃*
      ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) :=
    { Equiv.piCongrLeft' _ t with map_mul' := by intros; rfl }
  let factorIso : ((j : Fin (Fintype.card ι)) → Multiplicative (ZMod (n (t.symm j)))) ≃* Factors e :=
    MulEquiv.piCongrRight fun j => by change Multiplicative (ZMod (n (t.symm j))) ≃* Multiplicative (ZMod (2^(e' (t.symm j)))); rw [hn']
  let h := (f.trans reindex).trans factorIso
  refine ⟨_,e,?_,?_,⟨h⟩⟩
  · intro i
    have hni := hn (t.symm i)
    rw [hn'] at hni
    change 0 < e' _
    by_contra! he
    simp [Nat.eq_zero_of_le_zero he] at hni
  · apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2^(∑ i,e i) = 2^m
    rw [←hc, Nat.card_congr h.toEquiv,card_factors]
end ClassTwoProfile
end

/- QuotientRanks -/
section
namespace Erdos1160.Sims
open CentralKernelCount ClassTwoProfile OrbitUp
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
structure QuotientMark (H : Subgroup G) [H.Normal] (n : ℕ) where
  ord : Fin n→ℕ
  positive : ∀i,0 < ord i
  bounded : ∀i,ord i ≤ Nat.card G
  y : Fin n→G
  powers : ∀i,y i^ord i∈H
  generates : adjoin H y=⊤
  size : (∏i,ord i)*Nat.card H=Nat.card G
  rank : (squareCore (G⧸H)).index=2^n
theorem exists_quotient_mark (hG : IsPGroup 2 G) (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃n,Nonempty (QuotientMark H n) := by
  classical
  let q := QuotientGroup.mk' H
  have sq := QuotientGroup.mk'_surjective H
  let commutes (a b : G⧸H) : a*b=b*a := by
    obtain ⟨u,rfl⟩ := sq a
    obtain ⟨v,rfl⟩ := sq b
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)))
  letI : CommGroup (G⧸H) := { (inferInstance : Group (G⧸H)) with mul_comm := commutes }
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m,hm⟩ := IsPGroup.iff_card.mp (hG.to_quotient H)
  obtain ⟨n,e,he,hes,⟨f⟩⟩ := exists_cyclic_coords (G⧸H) hm
  let π := f.toMonoidHom.comp q
  have hπ : Function.Surjective π := f.surjective.comp sq
  choose y hy using fun i=>hπ (gen e i)
  have hk : π.ker=H := by
    rw [show π.ker=(f.toMonoidHom.ker).comap q from rfl,MonoidHom.ker_eq_bot _ f.injective,
      MonoidHom.comap_bot,QuotientGroup.ker_mk']
  have prod : (∏i,2^(e i))=H.index := by rw [Finset.prod_pow_eq_pow_sum,hes,←hm];rfl
  have genc : adjoin H y=⊤ := by
    let A := adjoin H y
    have im : A.map π=⊤ := by
      rw [←top_le_iff,←gen_closure e,Subgroup.closure_le]
      rintro _ ⟨i,rfl⟩
      refine ⟨y i,?_,hy i⟩
      exact le_sup_right (a:=H) (Subgroup.subset_closure ⟨i,rfl⟩)
    have h := congrArg (Subgroup.comap π) im
    rw [Subgroup.comap_map_eq,Subgroup.comap_top,hk,sup_eq_left.mpr (show H ≤ A from le_sup_left)] at h
    exact h
  have hidx : (squareCore (G⧸H)).index=2^n := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=squareCore (G⧸H)))
    rw [Subgroup.card_mul_index,hm,←hes]
    exact (squareCore_size f he).symm
  refine ⟨n,⟨⟨(fun i=>2^(e i)),fun i=>Nat.two_pow_pos _,?_,y,?_,genc,prod ▸ H.index_mul_card,hidx⟩⟩⟩
  · intro i
    have hi : e i≤∑j,e j := Finset.single_le_sum (f:=e) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hi).trans ((hes ▸ hm.symm.le).trans (Nat.card_le_card_of_surjective q sq))
  · intro i
    rw [←hk,MonoidHom.mem_ker,map_pow,hy,gen_pow]
theorem outer_quotient_mark {d : ℕ} (hG : IsPGroup 2 G) (p : G→*Multiplicative (V d))
    (hp : Function.Surjective p) (hk : p.ker=squareCore G)
    (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃ n,Nonempty (QuotientMark H n) ∧ n+Module.finrank K (vectorSub (H.map p))=d := by
  obtain ⟨n,⟨M⟩⟩ := exists_quotient_mark hG H hc
  have hIdx : (H.map p).index=2^n := by
    let q := QuotientGroup.mk' H
    have sq := QuotientGroup.mk'_surjective H
    rw [←M.rank,←CentralKernelCount.squareCore_map q sq,Subgroup.index_map,Subgroup.index_map,
      p.range_eq_top_of_surjective hp,q.range_eq_top_of_surjective sq]
    simp only [Subgroup.index_top,mul_one, q,QuotientGroup.ker_mk',hk,sup_comm]
  have hCard : Nat.card (H.map p)=2^(Module.finrank K (vectorSub (H.map p))) := by
    change Nat.card (vectorSub (H.map p))=_
    rw [Module.natCard_eq_pow_finrank (K:=K),Nat.card_zmod]
  refine ⟨n,⟨M⟩,Nat.pow_right_injective (by decide : 1 < 2) ?_⟩
  change 2^(n+Module.finrank K (vectorSub (H.map p)))=2^d
  rw [pow_add,←hIdx,←hCard,Subgroup.index_mul_card]
  change Nat.card (Fin d→ZMod 2)=_
  rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
private theorem generator_square_index {A : Type} [Group A] [Finite A] {r : ℕ} (x : Fin r→A)
    (hx : Subgroup.closure (Set.range x)=⊤) : (squareCore A).index ≤ 2^r := by
  classical
  let H := squareCore A
  let π := QuotientGroup.mk' H
  have onto := QuotientGroup.mk'_surjective H
  have hb (v : A⧸H) : v^2=1 := by
    obtain ⟨u,rfl⟩ := onto v
    rw [←map_pow,pow_two]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_closure ⟨u,rfl⟩)
  have inv (v : A⧸H) : v⁻¹=v := inv_eq_of_mul_eq_one_left (by rw [←pow_two];exact hb _)
  letI : CommGroup (A⧸H) := { (inferInstance : Group (A⧸H)) with
    mul_comm := fun a b=>by rw [←inv (a*b),mul_inv_rev,inv,inv] }
  let y := π ∘ x
  let T := Finset.univ.image y
  have hT : (T:Set (A⧸H))=Set.range y := by ext;simp [T]
  have hgen : Subgroup.closure (T:Set (A⧸H))=⊤ := by
    rw [hT,Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective π onto]
  have rank : Group.rank (A⧸H) ≤ r := (Group.rank_le hgen).trans (Finset.card_image_le.trans_eq (by simp))
  exact (Nat.le_of_dvd (Nat.two_pow_pos _) (card_dvd_exponent_pow_rank' _ hb)).trans (Nat.pow_le_pow_right (by decide) rank)
theorem inner_quotient_mark {r : ℕ} (hG : IsPGroup 2 G) (x : Fin r→G)
    (hx : Subgroup.closure (Set.range x)=⊤) (H : Subgroup G) [H.Normal] (hc : commutator G ≤ H) :
    ∃ n,Nonempty (QuotientMark H n) ∧ n ≤ r := by
  obtain ⟨n,⟨M⟩⟩ := exists_quotient_mark hG H hc
  let q := QuotientGroup.mk' H
  have sq := QuotientGroup.mk'_surjective H
  have gen : Subgroup.closure (Set.range (q ∘ x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,hx,Subgroup.map_top_of_surjective q sq]
  refine ⟨n,⟨M⟩,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp ?_⟩
  rw [←M.rank]
  exact generator_square_index _ gen
end Erdos1160.Sims
end

/- SimsAssembly -/
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp OrbitUp.MinSpan
open Erdos1160.DeepJacobi (Second secondBracket)
open Erdos1160Growth.LowerTriangularUpper (squareCore)
open scoped commutatorElement
theorem frame_of_seed {m d b σ : ℕ} (E : FiniteGrp.{0}) (size : Nat.card E=2^m)
    (C : Seed E d b σ) : ∃ S : Shape m d σ, Nonempty (SimsFrame S C.β.val E) := by
  classical
  let H := C.H
  let Q := headSub H
  let π := toHeadSub H
  have sp := toHeadSub_surj H
  letI : H.Normal := Subgroup.Normal.of_commutator_le E C.commutator_le
  have pg := IsPGroup.of_card size
  have pH := pg.to_subgroup H
  have pQ := (pg.to_quotient (commutatorTail E)).to_subgroup Q
  have genQ : Subgroup.closure (Set.range (π ∘ C.x))=⊤ := by
    rw [Set.range_comp,←MonoidHom.map_closure,C.generates,Subgroup.map_top_of_surjective π sp]
  obtain ⟨n,⟨ext⟩,ns⟩ := outer_quotient_mark pg C.p C.onto C.ker H C.commutator_le
  rw [C.subrank] at ns
  obtain ⟨r,⟨root⟩,rs⟩ := inner_quotient_mark pQ (π ∘ C.x) genQ (commutator Q) le_rfl
  obtain ⟨h,hQ⟩ := pQ.exists_card_eq
  obtain ⟨t,ht⟩ := (pg.to_subgroup (commutatorTail E)).exists_card_eq
  have hs : Nat.card H=2^(h+t) := by
    rw [card_of_onto π sp,inside_tail_card H C.derived,ht,hQ,pow_add]
  have hHm : h+t ≤ m := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hs ▸ size ▸ Subgroup.card_le_card_group H)
  have hQm : Nat.card Q ≤ 2^m := (Nat.card_le_card_of_surjective π sp).trans (size ▸ Subgroup.card_le_card_group H)
  have hW : Nat.card (W b)=2^b := by change Nat.card (Fin b→ZMod 2)=_;rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  have hb : Nat.card (Second (headQuot E))=2^b := (Nat.card_congr C.a.toEquiv).trans hW
  have mt := head_size_budget size C.p C.onto C.ker hb ht
  choose lift hlift using fun j=>sp (root.y j)
  let ro (j : Fin r) : Fin (2^m) := ⟨root.ord j-1,by have := (root.bounded j).trans hQm;have := root.positive j;omega⟩
  let xo (j : Fin n) : Fin (2^m) := ⟨ext.ord j-1,by have := ext.bounded j;rw [size] at this;have := ext.positive j;omega⟩
  have rord (j : Fin r) : (ro j).val+1=root.ord j := by change root.ord j-1+1=_;have := root.positive j;omega
  have xord (j : Fin n) : (xo j).val+1=ext.ord j := by change ext.ord j-1+1=_;have := ext.positive j;omega
  let S : Shape m d σ := ⟨r,n,h,t,rs,ns.le,hHm,ro,xo,fun i=>(C.p (lift i).val).toAdd,
    fun i=>(C.p (C.x i).val).toAdd,fun i=>(C.p (ext.y i)).toAdd⟩
  let R : ExtensionMark (W b) Q r := ⟨C.headIncl,root.y,by rw [C.headIncl_range];exact root.generates⟩
  let X : ExtensionMark H E n := ⟨H.subtype,ext.y,by rw [H.range_subtype];exact ext.generates⟩
  let comm (x y : E) : H := ⟨⁅x,y⁆,C.commutator_le (secondBracket x y).property⟩
  let c : ExtraSlot n σ→H := Sum.elim (fun z=>comm (ext.y z.1) (C.x z.2).val)
    (fun z=>comm (ext.y z.1) (ext.y (second z)))
  let v (j : Fin n) : H := ⟨ext.y j^ext.ord j,ext.powers j⟩
  refine ⟨S,⟨⟨FiniteGrp.of Q,FiniteGrp.of H,R,?_,?_,?_,?_,hQ,hs,π,sp,?_,?_,C.x,C.generates,
    headSub_class_two H,headSub_derived_binary H C.derived,C.head_order,X,v,c,?_,?_,?_,by change t ≤ m-d-b;omega⟩⟩⟩
  · change C.headIncl.range ≤ Subgroup.center Q
    rw [C.headIncl_range];exact headSub_class_two H
  · intro i
    change ∃ v,root.y i^((ro i).val+1)=C.headIncl v
    rw [rord]
    obtain ⟨v,hv⟩ := (C.headIncl_range ▸ root.powers i : root.y i^root.ord i∈C.headIncl.range)
    exact ⟨v,hv.symm⟩
  · intro z
    change ⁅root.y z.1,root.y (second z)⁆=C.headIncl (.ofAdd (C.β.val _ _))
    rw [←hlift,←hlift,←map_commutatorElement]
    exact C.compatible_of_lift _ _ ⁅lift z.1,lift (second z)⁆ rfl
  · change (∏i,((ro i).val+1))*Nat.card (W b) ≤ Nat.card Q
    simp only [rord,hW,←C.head_order]
    exact root.size.le
  · exact headSub_kernel_frattini H hs C.derived
  · exact ((inside_tail_card H C.derived).trans ht).le
  · intro z
    rcases z with z|z <;> exact C.compatible_of_lift _ _ _ rfl
  · refine ⟨fun i=>?_,fun _ _=>rfl,fun _=>rfl⟩
    change ext.y i^((xo i).val+1)=ext.y i^ext.ord i
    rw [xord]
  · change (∏i,((xo i).val+1))*Nat.card H ≤ Nat.card E
    simpa only [xord] using ext.size.le
theorem group_frame {m d : ℕ} (E : FiniteGrp.{0}) (size : Nat.card E=2^m)
    (rank : Nat.card (E⧸squareCore E)=2^d) :
    ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ ∃(β : minimalAlternating d b σ)(S : Shape m d σ),
      Nonempty (SimsFrame S β.val E) := by
  obtain ⟨b,σ,hd,hs,hb,⟨C⟩⟩ := seed_exists size rank
  obtain ⟨S,frame⟩ := frame_of_seed E size C
  exact ⟨b,σ,hd,hs,hb,C.β,S,frame⟩
end Erdos1160.Sims
end

/- CoreRange89 -/
section
namespace Erdos1160.OuterExtensions
open CategoryTheory
abbrev ClassOf (n : ℕ) := Tables.orderClasses n
noncomputable def orderRep {n : ℕ} (c : ClassOf n) : FiniteGrp.{0} := c.property.choose
theorem rep_size {n : ℕ} (c : ClassOf n) : Nat.card (orderRep c) = n := c.property.choose_spec.1
end Erdos1160.OuterExtensions
end

/- CoreMoment29 -/
section
namespace Erdos1160.OuterExtensions
open CategoryTheory
open scoped BigOperators
noncomputable instance classFintype (n : ℕ) : Fintype (ClassOf n) := (Tables.orderClasses_finite n).fintype
end Erdos1160.OuterExtensions
end

/- NonrootProfiles85 -/
section
namespace Erdos1160.Paper85
open OuterExtensions
open Erdos1160.DeepJacobi (binaryThird)
open Erdos1160Growth.LowerTriangularUpper
open scoped Classical
def inCentralStrip (m d : ℕ) : Prop :=
  1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d
noncomputable def generatorRank {m : ℕ} (c : ClassOf (2^m)) :=
  Nat.log 2 (frattini (orderRep c)).index
end Erdos1160.Paper85
end

/- SimsCoverage -/
section
namespace Erdos1160.Sims
open Erdos1160.OuterExtensions Erdos1160.Paper85 OrbitUp.MinSpan
open Erdos1160Growth.LowerTriangularUpper (squareCore frattini_eq_squareCore)
theorem frame_coverage {m : ℕ} (c : ClassOf (2^m)) :
    let d := generatorRank c
    ∃ b σ,d+b ≤ m ∧ σ ≤ d ∧ σ-1 ≤ b ∧ ∃(β : minimalAlternating d b σ)(S : Shape m d σ),
      Nonempty (SimsFrame S β.val (orderRep c)) := by
  let G := orderRep c
  have hG : Nat.card G=2^m := rep_size c
  obtain ⟨d,hd⟩ := ((IsPGroup.of_card hG).to_quotient (frattini G)).exists_card_eq
  change (frattini G).index=2^d at hd
  have hd' : generatorRank c=d := by
    change Nat.log 2 (frattini G).index=d
    rw [hd,Nat.log_pow (by decide : 1 < 2)]
  dsimp only
  rw [hd']
  exact group_frame G hG (by rw [←frattini_eq_squareCore hG];exact hd)
end Erdos1160.Sims
end

/- SimsPair -/
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp.MinSpan
open scoped commutatorElement
theorem bits_generate (b : ℕ) : Subgroup.closure (Set.range (bit : Fin b→W b))=⊤ := by
  apply top_unique
  intro v _
  rw [←standardWord_correct v]
  exact word_mem (Subgroup.closure (Set.range (bit : Fin b→W b))) bit (fun i=>Subgroup.subset_closure ⟨i,rfl⟩) _
theorem homs_of_gens {H Q : Type} [Group H] [Group Q] [Finite Q] {s : ℕ}
    (a : Fin s→H) (ha : Subgroup.closure (Set.range a)=⊤) : Nat.card (H→*Q) ≤ Nat.card Q^s := by
  let ev (f : H→*Q) (i : Fin s) := f (a i)
  have inj : Function.Injective ev := by
    intro f g eq
    apply MonoidHom.eq_of_eqOn_dense ha
    rintro _ ⟨i,rfl⟩
    exact congrFun eq i
  simpa only [Nat.card_fun,Nat.card_fin] using Nat.card_le_card_of_injective ev inj
structure FixedPair {m d b σ} (S : Shape m d σ) (β : Tensor d b)
    (H Q E : FiniteGrp.{0}) where
  base : Fin σ→H
  gen : Subgroup.closure (Set.range base)=⊤
  π : H→*Q
  kerSize : Nat.card π.ker ≤ 2^S.t
  incl : W b→*Q
  mark : ExtensionMark H E S.n
  pw : Fin S.n→H
  co : ExtraSlot S.n σ→H
  pat : ∀z,π (co z)=incl (extraPattern S β z)
  fits : ExtensionFits mark base (fun i=>(S.extOrder i).val+1) pw co
  size : (∏i,((S.extOrder i).val+1))*Nat.card H ≤ Nat.card E
def SimsFrame.overPair {m d b σ} {S : Shape m d σ} {β : Tensor d b} {E H Q : FiniteGrp.{0}}
    (D : SimsFrame S β E) (e : D.H≃*H) (v : D.Q≃*Q) : FixedPair S β H Q E := by
  let π := v.toMonoidHom.comp (D.π.comp e.symm.toMonoidHom)
  have ke : D.π.ker.map e.toMonoidHom=π.ker := by
    ext w
    constructor
    · rintro ⟨x,hx,rfl⟩
      change v (D.π (e.symm (e x)))=1
      rw [e.symm_apply_apply,show D.π x=1 from hx,v.map_one]
    · intro hw
      refine ⟨e.symm w,?_,e.apply_symm_apply w⟩
      apply v.injective
      exact (show v (D.π (e.symm w))=1 from hw).trans v.map_one.symm
  let z : ExtensionMark H E S.n := {
    incl := D.ext.incl.comp e.symm.toMonoidHom
    x := D.ext.x
    generate := by
      change adjoin (D.ext.incl.comp e.symm.toMonoidHom).range D.ext.x=⊤
      rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,←MonoidHom.range_eq_map];exact D.ext.generate }
  refine ⟨e ∘ D.base,?_,π,?_,v.toMonoidHom.comp D.root.incl,z,e ∘ D.powers,e ∘ D.comms,?_,?_,?_⟩
  · change Subgroup.closure (Set.range (e.toMonoidHom ∘ D.base))=⊤
    rw [Set.range_comp,←MonoidHom.map_closure (f:=e.toMonoidHom),D.gen,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top];exact e.surjective
  · rw [←ke,Subgroup.card_map_of_injective e.injective];exact D.kerSize
  · intro j;change v (D.π (e.symm (e (D.comms j))))=v (D.root.incl _)
    rw [e.symm_apply_apply,D.patterns]
  · refine ⟨fun i=>?_,fun i j=>?_,fun z=>?_⟩
    · change D.ext.x i^_=D.ext.incl (e.symm (e (D.powers i)))
      simpa only [e.symm_apply_apply] using D.fits.1 i
    · change ⁅D.ext.x i,D.ext.incl (e.symm (e (D.base j)))⁆=D.ext.incl (e.symm (e (D.comms (.inl (i,j)))))
      simpa only [e.symm_apply_apply] using D.fits.2.1 i j
    · change ⁅_,_⁆=D.ext.incl (e.symm (e (D.comms (.inr z))))
      simpa only [e.symm_apply_apply] using D.fits.2.2 z
  · rw [←Nat.card_congr e.toEquiv];exact D.size
theorem fixed_pair_count {I : Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    {H Q : FiniteGrp.{0}} (E : I→FiniteGrp.{0}) (D : ∀i,FixedPair S β H Q (E i))
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I≤(Nat.card H^σ*(Nat.card Q^σ*Nat.card Q^b))*
      (Nat.card H^S.n*(2^S.t)^(S.n*σ+S.n*(S.n-1)/2)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let i0 := h.some
    let A := (Fin σ→H) × (H→*Q) × (W b→*Q)
    let key (i:I) : A := ((D i).base,(D i).π,(D i).incl)
    haveI : Finite (H→*Q) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
    haveI : Finite (W b→*Q) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
    have cov : Nat.card A ≤ Nat.card H^σ*(Nat.card Q^σ*Nat.card Q^b) := by
      dsimp only [A]
      rw [Nat.card_prod,Nat.card_prod,Nat.card_fun,Nat.card_fin]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (homs_of_gens (D i0).base (D i0).gen)
        (homs_of_gens bit (bits_generate b)))
    refine (PresentationCount.card_le_of_fiber_bound key _ (fun a=>?_)).trans (Nat.mul_le_mul_right _ cov)
    let F := {i:I // key i=a}
    by_cases hf : Nonempty F
    swap
    · haveI : IsEmpty F := not_nonempty_iff.mp hf
      change Nat.card F≤_;simp
    let j := hf.some
    have parts (i:F) : (D i.val).base=(D j.val).base ∧ (D i.val).π=(D j.val).π ∧ (D i.val).incl=(D j.val).incl := by
      have h := i.property.trans j.property.symm
      exact ⟨congrArg Prod.fst h,congrArg (fun z:A=>z.2.1) h,congrArg (fun z:A=>z.2.2) h⟩
    let pat := (D j.val).incl ∘ extraPattern S β
    have step := restricted_extension_count (fun i:F=>(E i.val : Type)) (fun i=>(D i.val).mark)
      (D j.val).base (D j.val).gen (fun i=>(S.extOrder i).val+1) (fun _=>Nat.succ_pos _)
      (D j.val).π pat (fun i=>(D i.val).pw) (fun i=>(D i.val).co)
      (fun i z=>by dsimp [pat];rw [←(parts i).2.1,←(parts i).2.2];exact (D i.val).pat z)
      (fun i=>by rw [←(parts i).1];exact (D i.val).fits)
      (fun i=>(D i.val).size) (fun i j e=>Subtype.ext (sep _ _ e))
    exact step.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (D j.val).kerSize _))
end Erdos1160.Sims
end

/- SimsCohorts -/
section
namespace Erdos1160.Sims
open CategoryTheory CentralKernelCount OrbitUp.MinSpan
open Erdos1160.CentralLifts.Survival
open Erdos1160.DeepJacobi (Second)
abbrev IsoClass := Quotient (isIsomorphicSetoid FiniteGrp.{0})
abbrev cls (G:FiniteGrp.{0}) : IsoClass := Quotient.mk _ G
private theorem same_of_iso {G H:FiniteGrp.{0}} (h:Nonempty (G≃*H)) : cls G=cls H :=
  Quotient.sound ⟨InducedCategory.isoMk (F:=FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X:=G.toGrp) (Y:=H.toGrp) h.some)⟩
private noncomputable def iso_of_same {G H:FiniteGrp.{0}} (h:cls G=cls H) : G≃*H :=
  ((inducedFunctor FiniteGrp.toGrp).mapIso (Quotient.exact h).some).groupIsoToMulEquiv
theorem by_iso_cohorts {I:Type} [Finite I] (X:I→FiniteGrp.{0}) {B M:ℕ}
    (keys : ∀{P:Type} [Finite P] (f:P→I), (∀a b,Nonempty (X (f a)≃*X (f b))→a=b)→Nat.card P ≤ B)
    (fiber : ∀{P:Type} [Finite P] (f:P→I),Function.Injective f→∀ r:I,
      (∀a,Nonempty (X (f a)≃*X r))→Nat.card P ≤ M) : Nat.card I ≤ B*M := by
  classical
  let R := Setoid.ker (fun i=>cls (X i))
  let P := Quotient R
  let key : I→P := Quotient.mk _
  have keybd : Nat.card P ≤ B := keys (fun c:P=>c.out) (fun a b h=>by
    have eq : key a.out=key b.out := Quotient.sound (same_of_iso h)
    simpa only [key,Quotient.out_eq] using eq)
  apply (PresentationCount.card_le_of_fiber_bound key M (fun p=>?_)).trans (Nat.mul_le_mul_right M keybd)
  apply fiber (fun a:{i:I // key i=p}=>a.val) Subtype.val_injective p.out
  intro a
  have e : key a.val=key p.out := a.property.trans (Quotient.out_eq p).symm
  exact ⟨iso_of_same (Quotient.exact e)⟩
theorem root_class_bound {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i))
    (sep : ∀i j,Nonempty ((D i).Q≃*(D j).Q)→i=j) : Nat.card I ≤ 2^(b*S.r) := by
  have h := root_pattern_count (fun i=>(D i).Q) (fun i=>(D i).root) bit (bits_generate b)
    (fun i=>(D i).central) (fun i=>(S.rootOrder i).val+1) (fun _=>Nat.succ_pos _) (rootPattern S β)
    (fun i=>(D i).rootPowers) (fun i=>(D i).rootComms) (fun i=>(D i).rootSize) sep
  exact h.trans_eq (by change (Nat.card (Fin b→ZMod 2))^S.r=_;rw [Nat.card_fun,Nat.card_fin,Nat.card_zmod,←pow_mul])
theorem tower_class_bound {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i)) {E₀:FiniteGrp.{0}} (A:SimsFrame S β E₀)
    (same : ∀i,Nonempty ((D i).Q≃*A.Q))
    (sep : ∀i j,Nonempty ((D i).H≃*(D j).H)→i=j) :
    Nat.card I ≤ 2^(S.t*(σ*(σ+1)/2+jacobiRank A.Q)+σ*S.t.choose 2) := by
  classical
  let Q := A.Q
  let T := frattiniClasses S.h S.t Q
  have fin : T.Finite := (Tables.orderClasses_finite (2^(S.h+S.t))).subset (by
    rintro _ ⟨G,sz,_,rfl⟩;exact ⟨G,sz,rfl⟩)
  haveI : Finite T := fin.to_subtype
  let key (i:I) : T := ⟨cls (D i).H,(D i).H,(D i).hsize,⟨(same i).some.toMonoidHom.comp (D i).π,
    (same i).some.surjective.comp (D i).onto,by
      intro x hx
      apply (D i).kerFrattini
      apply (same i).some.injective
      exact (show (same i).some ((D i).π x)=1 from hx).trans (same i).some.map_one.symm⟩,rfl⟩
  have inj : Function.Injective key := fun i j h=>sep i j ⟨iso_of_same (congrArg Subtype.val h)⟩
  have keyBound : Nat.card I ≤ T.ncard := (Nat.card_le_card_of_injective _ inj).trans_eq (Nat.card_coe_set_eq ..)
  let a : Fin σ→Q := A.π ∘ A.base
  have gen : Subgroup.closure (Set.range a)=⊤ := by
    dsimp [a]
    rw [Set.range_comp,←MonoidHom.map_closure, A.gen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact A.onto
  have hi := marked_jacobi_fiber_product (FreeGroup.lift a) (MonoidHom.range_eq_top.mp ((FreeGroup.range_lift_eq_closure).trans gen))
    A.qsize A.classTwo S.t
  refine keyBound.trans (hi.trans ?_)
  calc
    _ ≤ ∏i ∈ Finset.range S.t,2^(σ*(σ+1)/2+jacobiRank Q+i*σ) :=
      Finset.prod_le_prod' (fun _ _=>Nat.sub_le ..)
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,
        ←Finset.sum_mul,Finset.sum_range_id,←Nat.choose_two_right,Nat.mul_comm (S.t.choose 2)]
      rfl
end Erdos1160.Sims
end

/- SuXiaOptimization -/
section
namespace Erdos1160.GeneratorLocalization
noncomputable def F (x : ℝ) := x^2*(1-x)/2
noncomputable def weakCount (x y z w : ℝ) :=
  x^2*(y+z-w)/2+x*y*w/2+(w*y-w^2/2)*z+w*z^2/2
noncomputable def strongCount (x y z w : ℝ) :=
  x^2*(y+z-w)/2+(w*y-w^2/2)*z+w*z^2/2
theorem peak_gap (x : ℝ) : 2/27 - F x = (x-2/3)^2*(x+1/3)/2 := by unfold F; ring
theorem high_rank {x y z w : ℝ} (hs : x+y+z=1) (hx : 3/5 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) : weakCount x y z w ≤ F x := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have h : x/2-x^2+(1-3*x/2)*z-z^2/2-w*z/2 ≤ 0 := by
    nlinarith only [hx,mul_nonneg hx0 (sub_nonneg.mpr hx1),
      sq_nonneg (z-(1-3*x/2)),mul_nonneg hw hz]
  have hy' : y=1-x-z := by linarith
  unfold weakCount F
  rw [hy']
  nlinarith only [mul_nonpos_of_nonneg_of_nonpos hw h]
private theorem monotone_F {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2/3) : F x ≤ F y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have h₁ : x^2+x*y+y^2 ≤ 3*y*(x+y)/2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ 2*x+y by linarith)]
  have h₂ : x^2+x*y+y^2 ≤ x+y := by nlinarith only [h₁,mul_nonneg (show 0 ≤ 2-3*y by linarith) (add_nonneg hx hy0)]
  unfold F
  nlinarith only [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr h₂)]
private noncomputable def envelope (x w : ℝ) := F x+w*(1-2*x)/2-w^2*(1-x)/2
private theorem bound_envelope {x y z w : ℝ} (hs : x+y+z=1) (hw : 0 ≤ w)
    (hy : w ≤ y) : strongCount x y z w ≤ envelope x w := by
  have hz : z=1-x-y := by linarith
  unfold strongCount envelope F
  rw [hz]
  nlinarith only [mul_nonneg (mul_nonneg hw (hw.trans hy)) (sub_nonneg.mpr hy)]
private theorem envelope_low {x w : ℝ} (hx : 0 ≤ x) (hw : 0 ≤ w) (hwx : w ≤ x)
    (hx' : x ≤ 1/2) : envelope x w ≤ 1/16 := by
  by_cases hlow : x ≤ 2/7
  · have base : 0 ≤ 1-4*x+2*x^2 := by
      have h : 0 ≤ (2/7-x)*(4-2*(x+2/7)) := by
        apply mul_nonneg <;> linarith
      nlinarith only [h]
    have delta : 0 ≤ (1-2*x)-(1-x)*(w+x) := by
      nlinarith only [base,mul_nonneg (sub_nonneg.mpr hwx) (show 0 ≤ 1-x by linarith)]
    unfold envelope F
    nlinarith only [mul_nonneg (sub_nonneg.mpr hwx) delta, sq_nonneg (x-1/4)]
  · have xlo : 2/7 ≤ x := by linarith
    have b : 0 ≤ 4*((x-1/2)^2+(1/2-x)*(3/14)+(3/14)^2)+2 := by
      nlinarith only [sq_nonneg (x-1/2),hx']
    have poly : 0 ≤ 4*x^3-6*x^2+5*x-1 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr xlo) b]
    have bound : 16*(1-x)*(envelope x w-1/16) ≤ 0 := by
      unfold envelope F
      nlinarith only [mul_nonneg (show 0 ≤ 1-2*x by linarith) poly,
        sq_nonneg (2*(1-x)*w-(1-2*x))]
    by_contra! h
    exact (not_lt_of_ge bound) (mul_pos (by linarith) (sub_pos.mpr h))
theorem low_rank {x y z w : ℝ} (hs : x+y+z=1) (hx : 0 ≤ x) (hhi : x ≤ 3/5)
    (hw : 0 ≤ w) (hwy : w ≤ y) (hwx : w ≤ x) (hz : 0 ≤ z) : strongCount x y z w ≤ 9/125 := by
  by_cases hm : x ≤ 1/2
  · exact ((bound_envelope hs hw hwy).trans (envelope_low hx hw hwx hm)).trans (by norm_num)
  · have ys : z=1-x-y := by linarith
    have hb : strongCount x y z w ≤ F x := by
      have hneg : 0 ≤ w*(2*x-1+y^2)+w^2*z := by
        apply add_nonneg
        · apply mul_nonneg hw; nlinarith only [hm,sq_nonneg y]
        · exact mul_nonneg (sq_nonneg w) hz
      rw [ys] at hneg ⊢
      unfold strongCount F
      nlinarith only [hneg]
    have hf := monotone_F hx hhi (by norm_num : (3:ℝ)/5 ≤ 2/3)
    exact hb.trans (hf.trans (by norm_num [F]))
theorem separated_high_rank {x y z w ε : ℝ} (hs : x+y+z=1) (hx : 3/5 ≤ x)
    (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) (hε : ε^2 ≤ (x-2/3)^2) :
    weakCount x y z w ≤ 2/27-7*ε^2/15 := by
  have coef : (14:ℝ)/15 ≤ x+1/3 := by linarith
  have h₁ := mul_le_mul_of_nonneg_left coef (sq_nonneg (x-2/3))
  linarith only [high_rank hs hx hy hz hw,peak_gap x,hε,h₁]
end Erdos1160.GeneratorLocalization
end

/- OffStripCubic -/
section
namespace Erdos1160.GeneratorLocalization
def profileExponent (d b u q : ℕ) : ℕ :=
  (b-q)*d.choose 2 + (d.choose 2)*u + (q*b-q.choose 2)*u + q*u.choose 2
private theorem strip_gap {m d : ℕ} (hm : 0 < m)
    (out : ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)) :
    (1/3000:ℝ)^2≤((d:ℝ)/m-2/3)^2 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have split : 3000*d+ m ≤ 2000*m ∨ 2000*m + m ≤ 3000*d := by omega
  rcases split with h|h
  · have hR : 3000*(d:ℝ)+m ≤ 2000*m := by exact_mod_cast h
    have low : (d:ℝ)/m ≤ 2/3-1/3000 := (div_le_iff₀ hmR).mpr (by linarith)
    nlinarith only [mul_nonneg (show 0 ≤ 2/3-(d:ℝ)/m-1/3000 by linarith)
      (show 0 ≤ 2/3-(d:ℝ)/m+1/3000 by linarith)]
  · have hR : 2000*(m:ℝ)+m ≤ 3000*d := by exact_mod_cast h
    have high : (2/3+1/3000:ℝ) ≤ d/m := (le_div_iff₀ hmR).mpr (by linarith)
    nlinarith only [mul_nonneg (show 0≤(d:ℝ)/m-2/3-1/3000 by linarith)
      (show 0≤(d:ℝ)/m-2/3+1/3000 by linarith)]
theorem offstrip_profile_cubic {m d b u q : ℕ} (hm : 0 < m) (sum : d+b+u=m)
    (hqb : q ≤ b) (hqd : q ≤ d)
    (out : ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d)) :
    27*100000000*profileExponent d b u q + 27*m^3 ≤ 2*100000000*m^3 := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  let x : ℝ := d/m
  let y : ℝ := b/m
  let z : ℝ := u/m
  let w : ℝ := q/m
  have hh : x+y+z=1 := by
    have H : (d:ℝ)+b+u=m := by exact_mod_cast sum
    dsimp [x,y,z];rw [←add_div,←add_div,H,div_self hmR.ne']
  have hx : 0 ≤ x := by dsimp [x];positivity
  have hy : 0 ≤ y := by dsimp [y];positivity
  have hz : 0 ≤ z := by dsimp [z];positivity
  have hw : 0 ≤ w := by dsimp [w];positivity
  have hwx : w ≤ x := div_le_div_of_nonneg_right (by exact_mod_cast hqd) hmR.le
  have hwy : w ≤ y := div_le_div_of_nonneg_right (by exact_mod_cast hqb) hmR.le
  have upper : strongCount x y z w ≤ 2/27-1/100000000 := by
    by_cases hi : 3/5 ≤ x
    · have h := separated_high_rank hh hi hy hz hw (strip_gap hm out)
      have leweak : strongCount x y z w ≤ weakCount x y z w := by
        unfold strongCount weakCount
        nlinarith only [mul_nonneg (mul_nonneg hx hy) hw]
      linarith
    · have h := low_rank hh hx (le_of_not_ge hi) hw hwy hwx hz
      linarith
  have scale : strongCount x y z w*(m:ℝ)^3 =
      (d:ℝ)^2*(b+u-q)/2+((q:ℝ)*b-(q:ℝ)^2/2)*u+(q:ℝ)*u^2/2 := by
    dsimp [x,y,z,w,strongCount]
    field_simp [hmR.ne']
  have small : (profileExponent d b u q : ℝ) ≤ strongCount x y z w*(m:ℝ)^3 := by
    have qq : q.choose 2 ≤ q*b := by
      rw [Nat.choose_two_right]
      exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ ((Nat.sub_le ..).trans hqb))
    rw [scale,profileExponent]
    push_cast [Nat.cast_sub hqb,Nat.cast_sub qq,Nat.cast_choose_two]
    nlinarith only [mul_nonneg (show 0≤(b:ℝ)-q by exact sub_nonneg.mpr (by exact_mod_cast hqb))
      (Nat.cast_nonneg d (α:=ℝ)),mul_nonneg (Nat.cast_nonneg d (α:=ℝ)) (Nat.cast_nonneg u (α:=ℝ))]
  have bnd := mul_le_mul_of_nonneg_right upper (show 0≤(m:ℝ)^3 by positivity)
  have ans : 27*100000000*(profileExponent d b u q : ℝ)+27*(m:ℝ)^3 ≤ 2*100000000*(m:ℝ)^3 := by
    linarith only [small,bnd]
  exact_mod_cast ans
end Erdos1160.GeneratorLocalization
end

/- SimsPrice85 -/
section
namespace Erdos1160.GeneratorLocalization
private theorem choose_two_add (a b : ℕ) :
    (a+b).choose 2 = a.choose 2 + a*b + b.choose 2 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ,Nat.choose_succ_succ,Nat.choose_succ_succ b,
      Nat.choose_one_right,Nat.choose_one_right,ih]
    ring
theorem sims_extension_price {m d b σ n q ν t u : ℕ} (hdb : d+b ≤ m)
    (hu : u=m-d-b) (ht : t ≤ u) (hn : n+σ ≤ d) (hq : q=σ-1) (hb : q ≤ b)
    (hν : ν+q.choose 2≤σ*b) :
    t*(σ*(σ+1)/2+ν)+σ*t.choose 2+t*(n*σ+n.choose 2) ≤
      d.choose 2*u+(q*b-q.choose 2)*u+q*u.choose 2+4*m^2 := by
  have choose_bound (a : ℕ) : a.choose 2 ≤ a*a := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  have qsub : q.choose 2 ≤ q*b := (choose_bound q).trans (Nat.mul_le_mul_left q hb)
  have hσ : σ ≤ q+1 := by omega
  have hs : σ*b ≤ q*b+b := by simpa [Nat.add_mul] using Nat.mul_le_mul_right b hσ
  have nu : ν ≤ q*b-q.choose 2+b := by omega
  have tr : σ*(σ+1)/2=σ.choose 2+σ := by
    calc
      _ = (σ+1).choose 2 := by rw [Nat.choose_two_right];simp [Nat.mul_comm]
      _ = _ := by rw [Nat.choose_succ_succ,Nat.choose_one_right,add_comm]
  have bin := Nat.choose_le_choose 2 hn
  rw [choose_two_add] at bin
  have block : σ*(σ+1)/2+(n*σ+n.choose 2) ≤ d.choose 2+σ := by rw [tr];omega
  have uM : u ≤ m := by omega
  have dM : σ ≤ m := by omega
  have tM := ht.trans uM
  have bM : b ≤ m := by omega
  have tσ := Nat.mul_le_mul tM dM
  have tb := Nat.mul_le_mul tM bM
  have tu := Nat.choose_le_choose 2 ht
  have uu := (choose_bound u).trans (Nat.mul_le_mul uM uM)
  have hw := Nat.mul_le_mul hσ tu
  have p₁ := Nat.mul_le_mul_left t block
  have p₂ := Nat.mul_le_mul_left t nu
  have dt := Nat.mul_le_mul_left (d.choose 2) ht
  have qt := Nat.mul_le_mul_left (q*b-q.choose 2) ht
  nlinarith only [p₁,p₂,tσ,tb,hw,uu,dt,qt]
end Erdos1160.GeneratorLocalization
end

/- SimsFixedCount -/
section
namespace Erdos1160.Sims
open CentralKernelCount OrbitUp.MinSpan Erdos1160.CentralLifts.Survival
open GeneratorLocalization
theorem sims_fixed_count {I:Type} [Finite I] {m d b σ} {S : Shape m d σ} {β : Tensor d b}
    (E : I→FiniteGrp.{0}) (D : ∀i,SimsFrame S β (E i)) (hdb : d+b ≤ m) (hq : σ-1 ≤ b)
    (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    let t := m-d-b
    Nat.card I ≤ 2^(d.choose 2*t+((σ-1)*b-(σ-1).choose 2)*t+(σ-1)*t.choose 2+9*m^2) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    let q := σ-1
    let u := m-d-b
    let L := σ*b-q.choose 2
    let head := S.t*(σ*(σ+1)/2+L)+σ*S.t.choose 2
    let extra := S.t*(S.n*σ+S.n.choose 2)
    have hl : L+q.choose 2≤σ*b := by
      have ch : q.choose 2 ≤ q*b := by
        rw [Nat.choose_two_right]
        exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ ((Nat.sub_le ..).trans hq))
      dsimp only [L];rw [Nat.sub_add_cancel (ch.trans (Nat.mul_le_mul_right b (Nat.sub_le σ 1)))]
    have hd : d ≤ m := by omega
    have hb : b ≤ m := by omega
    have hs : σ ≤ m := by have := S.n_le;omega
    have hn : S.n ≤ m := by have := S.n_le;omega
    have cost := sims_extension_price hdb (u:=u) rfl (D h.some).tail S.n_le (q:=q) rfl hq hl
    have total : Nat.card I ≤ 2^(m^2)*(2^head * 2^(4*m^2+extra)) := by
      apply by_iso_cohorts (fun i=>(D i).Q)
      · intro P _ f separated
        exact (root_class_bound (fun i=>E (f i)) (fun i=>D (f i)) separated).trans
          (Nat.pow_le_pow_right (by decide) (by simpa only [pow_two] using Nat.mul_le_mul hb (S.r_le.trans hs)))
      · intro P _ f hf r same
        apply by_iso_cohorts (fun i:P=>(D (f i)).H)
        · intro J _ g disj
          have bnd := tower_class_bound (fun i:J=>E (f (g i))) (fun i=>D (f (g i))) (D r) (fun i=>same (g i)) disj
          have gen : Subgroup.closure (Set.range ((D r).π ∘ (D r).base))=⊤ := by
            rw [Set.range_comp,←MonoidHom.map_closure,(D r).gen,←MonoidHom.range_eq_map,MonoidHom.range_eq_top]
            exact (D r).onto
          have cap := marked_jacobi_rank_bound _ gen (D r).classTwo (D r).elementary (D r).dimDerived hq
          have bound : jacobiRank (D r).Q ≤ L := by dsimp [L,q];omega
          exact bnd.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right
            (Nat.mul_le_mul_left _ (Nat.add_le_add_left bound _)) _))
        · intro J _ g hg s sameH
          let H := (D (f s)).H
          let Q := (D r).Q
          let M (i:J) : FixedPair S β H Q (E (f (g i))) :=
            (D (f (g i))).overPair (sameH i).some (same (g i)).some
          have ext := fixed_pair_count (fun i=>E (f (g i))) M (fun i j e=>hg (hf (sep _ _ e)))
          have cH : Nat.card H ≤ 2^m := (D (f s)).hsize.le.trans (Nat.pow_le_pow_right (by decide) S.ht_le)
          have cQ : Nat.card Q ≤ 2^m := (D r).qsize.le.trans (Nat.pow_le_pow_right (by decide) ((Nat.le_add_right ..).trans S.ht_le))
          have field {X l : ℕ} (a : X ≤ 2^m) (c : l ≤ m) : X^l ≤ 2^(m^2) := by
            refine (Nat.pow_le_pow_left a _).trans ?_;rw [←pow_mul,pow_two];exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ c)
          have rem : (2^S.t)^(S.n*σ+S.n*(S.n-1)/2)=2^extra := by rw [←pow_mul,←Nat.choose_two_right]
          apply ext.trans
          rw [rem]
          refine (Nat.mul_le_mul (Nat.mul_le_mul (field cH hs) (Nat.mul_le_mul (field cQ hs) (field cQ hb)))
              (Nat.mul_le_mul_right _ (field cH hn))).trans_eq ?_
          simp only [←pow_add]
          congr 1;ring
    refine total.trans ?_
    rw [←pow_add,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change m^2+(head+(4*m^2+extra))≤_
    dsimp only [head,extra,u,q,L] at *
    omega
end Erdos1160.Sims
end

/- SimsShapeSize -/
section
namespace Erdos1160.Sims
open OrbitUp
private abbrev Sizes (m d σ : ℕ) := Fin (σ+1) × Fin (d+1) × Fin (m+1) × Fin (m+1)
private abbrev Entries (m d σ : ℕ) (v : Sizes m d σ) :=
  (Fin v.1.val → Fin (2^m)) × (Fin v.2.1.val → Fin (2^m)) ×
  (Fin v.1.val → V d) × (Fin σ → V d) × (Fin v.2.1.val → V d)
private abbrev Record (m d σ : ℕ) := (v : Sizes m d σ) × Entries m d σ v
private def record {m d σ : ℕ} (x : Shape m d σ) : Record m d σ :=
  ⟨(⟨x.r,by have := x.r_le;omega⟩,⟨x.n,by have := x.n_le;omega⟩,
    ⟨x.h,by have := x.ht_le;omega⟩,⟨x.t,by have := x.ht_le;omega⟩),
    x.rootOrder,x.extOrder,x.rootVec,x.baseVec,x.extVec⟩
private def readRecord {m d σ : ℕ} (v : Record m d σ) : Option (Shape m d σ) :=
  if hn : v.1.2.1.val+σ ≤ d then
    if ht : v.1.2.2.1.val+v.1.2.2.2.val ≤ m then
      some ⟨v.1.1.val,v.1.2.1.val,v.1.2.2.1.val,v.1.2.2.2.val,by have := v.1.1.isLt;omega,hn,ht,
        v.2.1,v.2.2.1,v.2.2.2.1,v.2.2.2.2.1,v.2.2.2.2.2⟩
    else none
  else none
private theorem read_record {m d σ : ℕ} (x : Shape m d σ) : readRecord (record x)=some x := by
  cases x with
  | mk r n h t hr hn ht a b c e f => simp [record,readRecord,hn,ht]
private theorem record_inj {m d σ : ℕ} : Function.Injective (@record m d σ) := by
  intro x y h
  exact Option.some.inj ((read_record x).symm.trans ((congrArg readRecord h).trans (read_record y)))
instance (m d σ : ℕ) : Finite (Shape m d σ) := Finite.of_injective record record_inj
theorem shape_size {m d σ : ℕ} (hs : σ ≤ d) (hd : d ≤ m) :
    Nat.card (Shape m d σ) ≤ 2^(10*m^2+10) := by
  classical
  have initial := Nat.card_le_card_of_injective (@record m d σ) record_inj
  apply initial.trans
  rw [Nat.card_sigma]
  have per (v : Sizes m d σ) : Nat.card (Entries m d σ v) ≤ 2^(5*m^2) := by
    have r : v.1.val ≤ m := by have := v.1.isLt;omega
    have n : v.2.1.val ≤ m := by have := v.2.1.isLt;omega
    have s := hs.trans hd
    simp only [Entries,Nat.card_prod,Nat.card_fun,Nat.card_fin,V,K,Nat.card_zmod,
      ←pow_mul,←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.mul_le_mul (le_refl m) r,Nat.mul_le_mul (le_refl m) n,
      Nat.mul_le_mul hd r,Nat.mul_le_mul hd s,Nat.mul_le_mul hd n]
  apply (Finset.sum_le_sum (g:=fun _=>2^(5*m^2)) (fun v _=>per v)).trans
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul]
  have n : m+1 ≤ 2^m := Nat.lt_two_pow_self
  have b : Nat.card (Sizes m d σ) ≤ 2^(4*m) := by
    simp only [Sizes,Nat.card_prod,Nat.card_fin]
    calc
      _ ≤ 2^m*(2^m*(2^m*2^m)) := Nat.mul_le_mul ((Nat.add_le_add_right (hs.trans hd) 1).trans n)
        (Nat.mul_le_mul ((Nat.add_le_add_right hd 1).trans n) (Nat.mul_le_mul n n))
      _ = _ := by rw [←pow_add,←pow_add,←pow_add];congr 1;omega
  apply (Nat.mul_le_mul_right _ b).trans
  rw [←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  nlinarith only [Nat.le_self_pow (by decide : 2≠0) m]
end Erdos1160.Sims
end

/- SimsProfileCount -/
section
namespace Erdos1160.Sims
open OrbitUp.MinSpan GeneratorLocalization
open OrbitUp (V K)
theorem sims_profile_count {I:Type} [Finite I] {m d b σ} (E : I→FiniteGrp.{0})
    (frames : ∀i,∃(β:minimalAlternating d b σ) (S:Shape m d σ),Nonempty (SimsFrame S β.val (E i)))
    (hdb : d+b ≤ m) (hs : σ ≤ d) (hq : σ-1 ≤ b) (sep : ∀i j,Nonempty (E i≃*E j)→i=j) :
    Nat.card I ≤ 2^(profileExponent d b (m-d-b) (σ-1)+13*(m.sqrt+1)*m^2+19*m^2+19) := by
  classical
  letI : Finite (V d→ₗ[K]V b) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (Tensor d b) := Finite.of_injective DFunLike.coe DFunLike.coe_injective
  letI : Finite (minimalAlternating d b σ) := inferInstanceAs (Finite (Subtype _))
  choose β S H using frames
  let key (i:I) : minimalAlternating d b σ × Shape m d σ := (β i,S i)
  let q := σ-1
  let u := m-d-b
  let P := d.choose 2*u+(q*b-q.choose 2)*u+q*u.choose 2+9*m^2
  have total := PresentationCount.card_le_of_fiber_bound key (2^P) (fun a=>by
    let F := {i:I // key i=a}
    have D (i:F) : SimsFrame a.2 a.1.val (E i.val) := by
      have eq := i.property
      have eb : β i.val=a.1 := congrArg Prod.fst eq
      have es : S i.val=a.2 := congrArg Prod.snd eq
      rw [←eb,←es];exact (H i.val).some
    exact sims_fixed_count (fun i:F=>E i.val) D hdb hq (fun i j e=>Subtype.ext (sep _ _ e)))
  have hd : d ≤ m := by omega
  have hb : b ≤ m := by omega
  rw [Nat.card_prod] at total
  refine total.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul (minspan_entropy hd hb) (shape_size hs hd))).trans ?_)
  rw [←pow_add,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  dsimp [P,q,u,profileExponent]
  omega
end Erdos1160.Sims
end

/- OffStripAggregation -/
section
namespace Erdos1160.GeneratorLocalization
open Filter
private theorem entropy_vanishes (C J : ℕ) : ∀ᶠ m:ℕ in atTop,
    J*(13*(m.sqrt+1)*m^2 + C*m^2 + C + 3*m) ≤ m^3 := by
  let B := J*(29+2*C)
  filter_upwards [eventually_ge_atTop (max 1 (B*B))] with m hm
  have h1 : 1 ≤ m := (le_max_left _ _).trans hm
  have hs : 1 ≤ m.sqrt := Nat.le_sqrt.mpr h1
  have big : B ≤ m.sqrt := Nat.le_sqrt.mpr ((le_max_right _ _).trans hm)
  have self := (Nat.mul_le_mul_right m.sqrt big).trans (Nat.sqrt_le m)
  have cap := Nat.mul_le_mul_right (m^2) self
  have mq : 1 ≤ m^2 := Nat.one_le_pow _ _ h1
  have mq' : m ≤ m^2 := by nlinarith only [Nat.mul_le_mul_right m h1]
  have error : 13*(m.sqrt+1)*m^2 + C*m^2 + C + 3*m ≤ (29+2*C)*m.sqrt*m^2 := by
    have h := Nat.mul_le_mul_right (m^2) (Nat.mul_le_mul_left (16+2*C) hs)
    have c := Nat.mul_le_mul_left C mq
    nlinarith only [h,c,mq']
  have h := Nat.mul_le_mul_left J error
  dsimp [B] at cap
  nlinarith only [cap,h]
theorem offstrip_profile_sum (C : ℕ) :
    ∀ᶠ m:ℕ in atTop,
    ∀ {I : Type} [Fintype I] (f : I→ℕ),
      Fintype.card I≤(m+1)^3 →
      (∀i, f i=0 ∨ ∃d b u q, d+b+u=m ∧ q ≤ b ∧ q ≤ d ∧
        ¬(1000*(2*m-3*d) ≤ 2*d ∧ 1000*(3*d-2*m) ≤ 2*d) ∧
        f i ≤ 2^(profileExponent d b u q+13*(m.sqrt+1)*m^2+C*m^2+C)) →
      (∑i,f i)^(27*100000000)*2^(m^3) ≤ 2^(2*100000000*m^3) := by
  filter_upwards [entropy_vanishes C (27*100000000),eventually_ge_atTop 1] with m hm h1
  classical
  intro I _ f card price
  cases isEmpty_or_nonempty I with
  | inl h => simp
  | inr h =>
    obtain ⟨i,_,maxi⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
    have size : ∑i,f i ≤ 2^(3*m)*f i := by
      have sum := Finset.sum_le_card_nsmul Finset.univ f (f i) maxi
      rw [Finset.card_univ,nsmul_eq_mul] at sum
      have bound := Nat.pow_le_pow_left (show m+1 ≤ 2^m from Nat.lt_two_pow_self) 3
      rw [←pow_mul,Nat.mul_comm m] at bound
      exact sum.trans (Nat.mul_le_mul_right _ (card.trans bound))
    rcases price i with zero|⟨d,b,u,q,total,qb,qd,out,pr⟩
    · rw [zero,Nat.mul_zero] at size
      simp [Nat.le_zero.mp size]
    · have single := offstrip_profile_cubic h1 total qb qd out
      have tot := size.trans (Nat.mul_le_mul_left _ pr)
      rw [←pow_add] at tot
      apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left tot _)).trans
      rw [←pow_mul,←pow_add]
      apply Nat.pow_le_pow_right (by decide)
      nlinarith only [single,hm]
end Erdos1160.GeneratorLocalization
end

/- SuXia35 -/
section
namespace Erdos1160.Sims
open OuterExtensions Paper85 GeneratorLocalization Filter
private theorem rep_separates {m : ℕ} (a b : ClassOf (2^m)) (e : Nonempty (orderRep a ≃* orderRep b)) : a=b := by
  apply Subtype.ext
  rw [←a.property.choose_spec.2,←b.property.choose_spec.2]
  apply Quotient.sound
  exact ⟨CategoryTheory.InducedCategory.isoMk (F:=FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X:=(orderRep a).toGrp) (Y:=(orderRep b).toGrp) e.some)⟩
theorem su_xia_3_5 : ∀ᶠ m:ℕ in atTop,
    (Nat.card {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)})^(27*100000000) *
      2^(m^3) ≤ 2^(2*100000000*m^3) := by
  classical
  filter_upwards [offstrip_profile_sum 19] with m bound
  let I := {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)}
  let J := Fin (m+1) × Fin (m+1) × Fin (m+1)
  let d (i:I) := generatorRank i.val
  choose b σ db sd qb frames using fun i:I=>frame_coverage i.val
  let key (i:I) : J := (⟨d i,by have := db i;change d i+b i ≤ m at this;omega⟩,
    ⟨b i,by have := db i;omega⟩,⟨σ i,by have := sd i;have := db i;omega⟩)
  let C (j:J) := {i:I // key i=j}
  let f (j:J) := Nat.card (C j)
  have partition : Nat.card I=∑j:J,f j := by
    rw [←Nat.card_sigma]
    exact (Nat.card_congr (Equiv.sigmaFiberEquiv key)).symm
  change (Nat.card I)^_*_≤_
  rw [partition]
  apply bound f (by dsimp [J];simp [pow_succ,Nat.mul_assoc])
  intro j
  by_cases hj : Nonempty (C j)
  swap
  · left
    haveI : IsEmpty (C j) := not_nonempty_iff.mp hj
    exact Nat.card_of_isEmpty
  right
  let r := hj.some.val
  have parts (i:C j) : d i.val=d r ∧ b i.val=b r ∧ σ i.val=σ r := by
    have eq := i.property.trans hj.some.property.symm
    exact ⟨congrArg (fun k:J=>k.1.val) eq,congrArg (fun k:J=>k.2.1.val) eq,congrArg (fun k:J=>k.2.2.val) eq⟩
  have s : σ r ≤ d r := sd r
  have sum : d r+b r ≤ m := db r
  refine ⟨d r,b r,m-d r-b r,σ r-1,by omega,qb r,by omega,r.property,?_⟩
  let e := (Fintype.equivFin (C j)).symm
  change Nat.card (C j)≤_
  rw [←Nat.card_congr e]
  refine sims_profile_count (fun i=>orderRep (e i).val.val) ?_ sum s (qb r) ?_
  · intro i
    rw [←(parts (e i)).1,←(parts (e i)).2.1,←(parts (e i)).2.2]
    exact frames (e i).val
  · intro i k h
    exact e.injective (Subtype.ext (Subtype.ext (rep_separates _ _ h)))
end Erdos1160.Sims

end

namespace Erdos1160.Sims
open Filter OuterExtensions Paper85

theorem four_times_offstrip_count : ∀ᶠ m:ℕ in atTop, ∀ C : Set (ClassOf (2^m)),
    (∀c∈C,¬inCentralStrip m (generatorRank c)) →
    (4*C.ncard)^27*2^(9*m^2) ≤ 2^(2*m^3) := by
  classical
  filter_upwards [su_xia_3_5,eventually_ge_atTop (100*100000000)] with m cap hm
  intro C hc
  let X := {c:ClassOf (2^m) // ¬inCentralStrip m (generatorRank c)}
  let emb : C→X := fun c=>⟨c.val,hc c.val c.property⟩
  have sub : C.ncard ≤ Nat.card X := by
    rw [←Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_injective emb (fun _ _ e=>Subtype.ext (congrArg (fun v:X=>v.val) e))
  have cost : (54+9*m^2)*100000000 ≤ m^3 := by
    have h1 : 1 ≤ m^2 := Nat.one_le_pow _ _ (by omega)
    have big := Nat.mul_le_mul_right (m^2) hm
    nlinarith only [h1,big]
  apply (Nat.pow_le_pow_iff_left (by decide : 100000000≠0)).mp
  calc
    _ = C.ncard^(27*100000000)*2^((54+9*m^2)*100000000) := by
      have z : (4*C.ncard)^27*2^(9*m^2) = C.ncard^27*2^(54+9*m^2) := by
        rw [mul_pow,pow_add]
        rw [Nat.mul_comm (4^27),Nat.mul_assoc]
        rfl
      rw [z,mul_pow,←pow_mul,←pow_mul]
    _ ≤ (Nat.card X)^(27*100000000)*2^(m^3) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left sub _) (Nat.pow_le_pow_right (by decide) cost)
    _ ≤ 2^(2*100000000*m^3) := cap
    _ = _ := by rw [←pow_mul];congr 1;ring

end Erdos1160.Sims
theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R2.H4 := by
  classical
  unfold OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R2.H4
  filter_upwards [Erdos1160.Sims.four_times_offstrip_count] with m h
  apply h
  exact fun c hc=>hc.2
