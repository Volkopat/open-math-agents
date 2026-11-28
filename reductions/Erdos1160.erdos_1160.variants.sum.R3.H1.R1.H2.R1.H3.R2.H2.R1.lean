import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.GroupTheory.Frattini
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.MonoidAlgebra.Module

import Mathlib.Algebra.Module.ZMod
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.SpecificGroups.ZGroup
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/- Credit: @wispiANt. Count the groups with cyclic Sylow subgroups explicitly.
The Z-group approach was suggested by @hiattco in desk note 69164.
The cyclic-complement bound combines the nilpotent count of @gertjanvdgoot
(PR #7292) with the cyclic-action method discussed by @hiattco (desk note 69414).
The remaining estimates concern nonnilpotent soluble groups of mixed order,
separating abelian from nonabelian Sylow subgroups. -/

open CategoryTheory Erdos1160

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1

open Nat (card log) in
open Subgroup (center) in
open MulAut (conj) in
open Group in
def H1 : Prop :=
  ∃ E, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G | card G = q ∧ Group.IsSolvable G ∧ ¬ ((((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ IsNilpotent N ∧ (card N).Coprime (card P)) ∨
        ((∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsNilpotent N ∧ IsNilpotent P ∧ card N^(rank N * rank P) ≤ 2^(r*r*2) ∧ (card N).Coprime (card P)) ∨ (∃ (N : Subgroup G) (_ : N.Normal), (∃ (M : Subgroup N) (_ : M.Normal), IsNilpotent M ∧ IsCyclic (N ⧸ M)) ∧ IsCyclic (G ⧸ N)))) ∨ (∃ A B : FiniteGrp.{0}, 1 < card A ∧ 1 < card B ∧ (card A).Coprime (card B) ∧ Nonempty (G ≃* A × B))) ∨
        ((∃ K : Subgroup G, K.Normal ∧ IsNilpotent K ∧ 1 < card K ∧ (card K).Coprime K.index) ∨ ((∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ 1 < card P) ∨ (∃ (N : Subgroup G) (_ : N.Normal), let m := N.index; IsCyclic (G ⧸ N) ∧ 1 < m ∧ let J := (conj : N →* MulAut N).range; ∃ _ : J.Normal, (ConjClasses.mk '' {t : MulAut N ⧸ J | t^m = 1}).ncard * card (center N) ≤ card N^(E*log 2 m+1))))) ∧ ¬ IsZGroup G ∧
        (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P) ∧ ¬ (∃ (N : Subgroup G) (_ : N.Normal), let m := N.index; IsCyclic (G ⧸ N) ∧ 1 < m ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N), m = p^a ∧
        p^((conj : N →* MulAut N).range.subgroupOf (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
        card (center N) ≤ card N^(E*log 2 m+1))}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

open Nat (card log) in
open Subgroup (center) in
open MulAut (conj) in
open Group in
def H2 : Prop :=
  ∃ E : ℕ, ∀ q r : ℕ, Odd q → q < 2^r → ¬ IsPrimePow q →
    ¬ (∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l) →
    let shape (p l a : ℕ) := p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G | card G = q ∧ Group.IsSolvable G ∧ ¬ ((∃ p l a : ℕ, shape p l a) ∧
        ∀ p l a : ℕ, (shape p l a) →
          ((∃ N : Subgroup G, N.Normal ∧ card N = p^a) ∨ card (Sylow l G) = 1)) ∧ ¬ ((((∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ IsNilpotent N ∧ (card N).Coprime (card P)) ∨
        ((∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsNilpotent N ∧ IsNilpotent P ∧ card N ^ (rank N * rank P) ≤ 2^(r*r*2) ∧ (card N).Coprime (card P)) ∨ (∃ (N : Subgroup G) (_ : N.Normal), (∃ (M : Subgroup N) (_ : M.Normal), IsNilpotent M ∧ IsCyclic (N ⧸ M)) ∧ IsCyclic (G ⧸ N)))) ∨ (∃ A B : FiniteGrp.{0}, 1 < card A ∧ 1 < card B ∧ (card A).Coprime (card B) ∧ Nonempty (G ≃* A × B))) ∨
        ((∃ K : Subgroup G, K.Normal ∧ IsNilpotent K ∧ 1 < card K ∧ (card K).Coprime K.index) ∨ ((∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ 1 < card P) ∨ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (conj : N →* MulAut N).range; ∃ _ : J.Normal, (ConjClasses.mk '' {t : MulAut N ⧸ J | t^N.index = 1}).ncard * card (center N) ≤ card N^(E * log 2 N.index+1))))) ∧ (∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P) ∧ ¬ (∃ (N : Subgroup G) (_ : N.Normal), let m := N.index; IsCyclic (G ⧸ N) ∧ 1 < m ∧
          (∃ P : Sylow m.minFac G, center P ⊔ N.subgroupOf P = ⊤) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N), 0 < a ∧ m = p^a ∧
        p ^ ((conj : N →* MulAut N).range.subgroupOf
          (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
        card (center N) ≤ card N ^ (E * log 2 m + 1))}).ncard ≤
      2^(E*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p)

/-- Label each group by a multiplication table on Fin n. -/
lemma finite_classes (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  classical
  let T := {m : Fin n → Fin n → Fin n // ∃ s : Group (Fin n), s.mul = m}
  let _ : Finite T := inferInstanceAs (Finite (Subtype _))
  let model (t : T) := @FiniteGrp.of (Fin n) t.property.choose inferInstance
  let c (t : T) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (model t)
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n} ⊆ Set.range c := by
    rintro _ ⟨G, hG, rfl⟩
    let e : Fin n ≃ G := ((Nat.equivFinOfCardPos (α := G) Nat.card_pos.ne').trans
      (finCongr hG)).symm
    let law : Group (Fin n) := e.group
    let t : T := ⟨law.mul, law, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    let f : model t ≃* G := { e with
      map_mul' := fun a b =>
        (congrArg e (congrFun (congrFun t.property.choose_spec a) b)).trans
          (e.apply_symm_apply (e a * e b)) }
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.toGrpIso⟩
  exact (Set.finite_range c).subset cover

lemma positive_count {n : ℕ} (hn : 0 < n) : 0 < g n := by
  apply (Set.ncard_pos (finite_classes n)).mpr
  let _ : NeZero n := ⟨hn.ne'⟩
  exact ⟨_, FiniteGrp.of (Multiplicative (ZMod n)), Nat.card_zmod _, rfl⟩

lemma cyclic_actions (H K : Type*) [Group H] [Group K] [Finite K]
    [IsCyclic H] [IsCyclic K] : Nat.card (H →* MulAut K) ≤ (Nat.card K).totient := by
  let _ : Finite (MulAut K) := Finite.of_injective (fun a : MulAut K => (a : K → K))
    (fun _ _ h => DFunLike.ext' h)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := H)
  have inj : Function.Injective (fun f : H →* MulAut K => f x) := by
    intro f g h
    apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := hx y
    simpa only [map_zpow] using congrArg (fun a : MulAut K => a ^ z) h
  exact (Nat.card_le_card_of_injective _ inj).trans
    (IsCyclic.card_mulAut K).le

lemma cyclic_sylows_bound (q : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G}).ncard ≤ q := by
  classical
  let C (i : ℕ) := Multiplicative (ZMod (i+1))
  let A (i : q.divisors) := C (q / (i : ℕ) - 1) →* MulAut (C ((i : ℕ)-1))
  have ccard (i : ℕ) : Nat.card (C i) = i+1 := Nat.card_zmod _
  let (i : q.divisors) : Finite (A i) := by
    let _ : Finite (MulAut (C ((i : ℕ)-1))) := Finite.of_injective
      (fun a : MulAut (C ((i : ℕ)-1)) => (a : C ((i : ℕ)-1) → C ((i : ℕ)-1))) (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A i => (a : C _ → MulAut (C ((i : ℕ)-1))))
      (fun _ _ h => DFunLike.ext' h)
  let decode (x : (i : q.divisors) × A i) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    let K := C ((x.1 : ℕ)-1)
    let H := C (q / (x.1 : ℕ) - 1)
    letI : Finite (SemidirectProduct K H x.2) :=
      Finite.of_equiv (K × H) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct K H x.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G} ⊆
      Set.range decode := by
    rintro _ ⟨G, ⟨hG, _, hz⟩, rfl⟩
    obtain ⟨N, H, a, e, hH, hN, _⟩ := isZGroup_iff_exists_mulEquiv.mp hz
    have hp : 0 < Nat.card N := Nat.card_pos
    have hh : 0 < Nat.card H := Nat.card_pos
    let i : q.divisors := ⟨Nat.card N, Nat.mem_divisors.mpr
      ⟨hG ▸ N.card_subgroup_dvd_card, hG ▸ Nat.card_pos.ne'⟩⟩
    have hi : (i : ℕ) = Nat.card N := rfl
    have size := Nat.card_congr e.toEquiv
    rw [SemidirectProduct.card, hG] at size
    have hj : q / (i : ℕ) = Nat.card H := by rw [hi, size, Nat.mul_div_cancel_left _ hp]
    let fn : N ≃* C ((i : ℕ)-1) := mulEquivOfCyclicCardEq (by rw [ccard, hi]; omega)
    let fh : H ≃* C (q / (i : ℕ) - 1) :=
      mulEquivOfCyclicCardEq (by rw [ccard, hj]; omega)
    let f := e.trans (SemidirectProduct.congr' (φ₁ := a) fn fh)
    refine ⟨⟨i, MonoidHom.comp (MulAut.congr fn) (a.comp fh.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((i : q.divisors) × A i) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ i : q.divisors, Nat.card (A i) := Nat.card_sigma
    _ ≤ ∑ i : q.divisors, (i : ℕ).totient := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Nat.pos_of_mem_divisors i.property
      have hn : (i : ℕ)-1+1 = (i : ℕ) := by omega
      simpa only [ccard, hn] using
        cyclic_actions (C (q / (i : ℕ) - 1)) (C ((i : ℕ)-1))
    _ = q := (Finset.sum_finset_coe Nat.totient q.divisors).trans (Nat.sum_totient q)

/-- In particular all groups of squarefree order are included in the explicit bound. -/
lemma squarefree_count {q : ℕ} (hs : Squarefree q) : g q ≤ q := by
  have eq : {G : FiniteGrp.{0} | Nat.card G = q} =
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ IsZGroup G} := by
    ext G
    constructor
    · intro hG
      let _ : IsZGroup G := IsZGroup.of_squarefree (hG.symm ▸ hs)
      exact ⟨hG, inferInstance, inferInstance⟩
    · exact fun h => h.1
  simpa only [g, eq] using cyclic_sylows_bound q

/-- Adapted from nilpotent_ncard_le in the merged R2.H2.R1.H2.R1.H2 proof.
The Sylow profile of a nilpotent group determines it up to isomorphism. -/
lemma nilpotent_bound (q : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ Group.IsNilpotent G}).ncard ≤
      ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n}
  let Profile (n : ℕ) := (p : n.primeFactors) → O ((p : ℕ)^n.factorization p)
  let rep {k : ℕ} (x : O k) : FiniteGrp.{0} := Classical.choose x.property
  have rep_class {k : ℕ} (x : O k) :
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep x) = x.val :=
    (Classical.choose_spec x.property).2
  let realize {n : ℕ} (x : Profile n) :=
    Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (FiniteGrp.of (∀ p, rep (x p)))
  let (p : q.primeFactors) : Finite (O ((p : ℕ)^q.factorization p)) :=
    (finite_classes _).to_subtype
  let _ : Finite (Profile q) := inferInstanceAs (Finite (∀ p : q.primeFactors, O _))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ Group.IsNilpotent G} ⊆
      Set.range (realize (n := q)) := by
    rintro _ ⟨G, ⟨rfl, _, hn⟩, rfl⟩
    let _ := hn
    let t : Profile (Nat.card G) := fun p => by
      let _ : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      let P : Sylow (p : ℕ) G := default
      exact ⟨Quotient.mk _ (FiniteGrp.of P), FiniteGrp.of P, P.card_eq_multiplicity, rfl⟩
    refine ⟨t, Quotient.sound ?_⟩
    let E := Sylow.directProductOfNormal (G := G) fun _ => inferInstance
    let L (p : (Nat.card G).primeFactors) : (∀ P : Sylow (p : ℕ) G, P) ≃* rep (t p) := by
      let _ : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      let P : Sylow (p : ℕ) G := default
      have he : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep (t p)) =
          Quotient.mk _ (FiniteGrp.of P) := rep_class _
      let iso := Classical.choice (Quotient.exact he)
      let e := ((inducedFunctor FiniteGrp.toGrp).mapIso iso).groupIsoToMulEquiv
      let _ : Unique (Sylow (p : ℕ) G) := Sylow.unique_of_normal P inferInstance
      exact (MulEquiv.piUnique (fun Q : Sylow (p : ℕ) G => Q)).trans e.symm
    let e := (MulEquiv.piCongrRight L).symm.trans E
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.toGrpIso⟩
  calc
    _ ≤ (Set.range (realize (n := q))).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card (Profile q) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = ∏ p : q.primeFactors, g (p ^ q.factorization p) := by rw [Nat.card_pi]; rfl
    _ = _ := Finset.prod_finset_coe (fun p => g (p ^ q.factorization p)) q.primeFactors

lemma prime_power_count {q : ℕ} (hpp : IsPrimePow q) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G}).ncard ≤
      ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hpp
  rw [Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton, Nat.factorization_pow_self hp]
  have sub : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^k ∧ Group.IsSolvable G} ⊆
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^k} := by
    rintro _ ⟨G, ⟨hG, _⟩, rfl⟩
    exact ⟨G, hG, rfl⟩
  exact Set.ncard_le_ncard sub (finite_classes _)

/-- Thin generators relative to a subgroup. Each retained generator at least doubles
the order of the subgroup already generated. -/
theorem thin_relative_generators {G : Type*} [Group G] [Finite G] (H : Subgroup G) (s : Finset G) :
    ∃ t : Finset G, t ⊆ s ∧
      H ⊔ Subgroup.closure (t : Set G) = H ⊔ Subgroup.closure (s : Set G) ∧
      2 ^ t.card * Nat.card H ≤ Nat.card (H ⊔ Subgroup.closure (s : Set G) : Subgroup G) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp, rfl, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨t, hts, ht, hpow⟩ := ih
    let A := H ⊔ Subgroup.closure (s : Set G)
    let J := H ⊔ Subgroup.closure ((insert x s : Finset G) : Set G)
    have hle : A ≤ J := sup_le_sup_left (Subgroup.closure_mono (by simp)) _
    have hxJ : x ∈ J := (show Subgroup.closure ((insert x s : Finset G) : Set G) ≤ J from le_sup_right)
      (Subgroup.subset_closure (by simp))
    by_cases hxA : x ∈ A
    · have heq : J = A := by
        apply le_antisymm _ hle
        apply sup_le le_sup_left
        apply (Subgroup.closure_le _).2
        rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨hxA, fun _ hy => (show Subgroup.closure (s : Set G) ≤ A from le_sup_right)
          (Subgroup.subset_closure hy)⟩
      exact ⟨t, hts.trans (Finset.subset_insert _ _), ht.trans heq.symm, by change 2 ^ t.card * Nat.card H ≤ Nat.card J; rw [heq]; exact hpow⟩
    · have hlt : Nat.card A < Nat.card J := by
        apply lt_of_not_ge
        intro h
        exact hxA ((Subgroup.eq_of_le_of_card_ge hle h).symm ▸ hxJ)
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
      have hk2 : 2 ≤ k := by
        by_contra! h
        interval_cases k <;> simp_all
      refine ⟨insert x t, Finset.insert_subset_insert _ hts, ?_, ?_⟩
      · simp only [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union]
        simpa only [sup_left_comm H] using congrArg (Subgroup.closure {x} ⊔ ·) ht
      · change 2 ^ (insert x t).card * Nat.card H ≤ Nat.card J
        rw [Finset.card_insert_of_notMem (fun h => hx (hts h)), pow_succ, mul_right_comm, hk]
        exact Nat.mul_le_mul hpow hk2

/-- Thin a finite generating set, recording the doubling of subgroup order at each step. -/
theorem thin_generators {G : Type*} [Group G] [Finite G] (s : Finset G) :
    ∃ t : Finset G, t ⊆ s ∧ Subgroup.closure (t : Set G) = Subgroup.closure (s : Set G) ∧
      2 ^ t.card ≤ Nat.card (Subgroup.closure (s : Set G)) := by
  simpa using thin_relative_generators (⊥ : Subgroup G) s

lemma exists_relative_generators_le_log_index {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    ∃ t : Finset G, H ⊔ Subgroup.closure (t : Set G) = ⊤ ∧ t.card ≤ Nat.log 2 H.index := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨t,_,gen,size⟩ := thin_relative_generators H (Finset.univ : Finset G)
  simp only [Finset.coe_univ,Subgroup.closure_univ,sup_top_eq,Subgroup.card_top] at gen size
  rw [← H.index_mul_card] at size
  exact ⟨t,gen,Nat.le_log_of_pow_le (by decide) (Nat.le_of_mul_le_mul_right size Nat.card_pos)⟩

/-- Images of relative generators determine an automorphism that fixes H pointwise. -/
lemma pointwise_stabilizer_relative_generator_bound {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (t : Finset G) (gen : H ⊔ Subgroup.closure (t : Set G) = ⊤) :
    Nat.card (fixingSubgroup (MulAut G) (H : Set G)) ≤ Nat.card G ^ t.card := by
  let eval (f : fixingSubgroup (MulAut G) (H : Set G)) (x : t) := f.val x
  have inj : Function.Injective eval := by
    intro f g eq
    apply Subtype.ext
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense (s := (H : Set G) ∪ (t : Set G))
    · simpa only [Subgroup.closure_union,Subgroup.closure_eq] using gen
    · intro x hx
      rcases hx with hx | hx
      · exact ((mem_fixingSubgroup_iff _).mp f.property x hx).trans
          (((mem_fixingSubgroup_iff _).mp g.property x hx).symm)
      · exact congrFun eq ⟨x,hx⟩
  exact (Nat.card_le_card_of_injective eval inj).trans_eq (by simp [Nat.card_fun])

/-- The Sylow subgroup of the pointwise stabilizer is determined by its action on
relative generators. Each generator orbit has prime-power size and lies in its
prescribed image set. -/
lemma stabilizer_prime_part_orbit_bound {K : Type*} [Group K] [Finite K]
    {p : ℕ} [hp : Fact p.Prime] (H : Subgroup K) (t : Finset K)
    (gen : H ⊔ Subgroup.closure (t : Set K) = ⊤) (B : K → Set K)
    (images : ∀ f : fixingSubgroup (MulAut K) (H : Set K), ∀ x ∈ t, f.val x ∈ B x) :
    p ^ (Nat.card (fixingSubgroup (MulAut K) (H : Set K))).factorization p ≤
      ∏ x ∈ t, p ^ Nat.log p (B x).ncard := by
  classical
  let A := fixingSubgroup (MulAut K) (H : Set K)
  let P : Sylow p A := default
  let T (x : t) := MulAction.orbit P x.val
  let eval (u : P) (x : t) : T x := ⟨u • x.val,⟨u,rfl⟩⟩
  have inj : Function.Injective eval := by
    intro u v eq
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.toMonoidHom_injective
    apply MonoidHom.eq_of_eqOn_dense (s := (H : Set K) ∪ (t : Set K))
    · simpa only [Subgroup.closure_union,Subgroup.closure_eq] using gen
    · intro x hx
      rcases hx with hx | hx
      · exact ((mem_fixingSubgroup_iff _).mp u.val.property x hx).trans
          (((mem_fixingSubgroup_iff _).mp v.val.property x hx).symm)
      · exact congrArg Subtype.val (congrFun eq ⟨x,hx⟩)
  have size (x : t) : Nat.card (T x) ≤ p ^ Nat.log p (B x.val).ncard := by
    have sub : T x ⊆ B x.val := by
      rintro _ ⟨u,rfl⟩
      exact images u.val x.val x.property
    have le := Set.ncard_le_ncard sub (Set.toFinite _)
    obtain ⟨j,hj⟩ := P.isPGroup'.card_orbit x.val
    change Nat.card (T x) = p^j at hj
    change Nat.card (T x) ≤ (B x.val).ncard at le
    rw [hj] at le ⊢
    exact Nat.pow_le_pow_right hp.out.pos (Nat.le_log_of_pow_le hp.out.one_lt le)
  rw [← P.card_eq_multiplicity]
  apply (Nat.card_le_card_of_injective eval inj).trans
  rw [Nat.card_pi,← Finset.prod_coe_sort t]
  exact Finset.prod_le_prod' fun x _ => size x

/-- An automorphism fixing H preserves every power of x lying in H. -/
lemma stabilizer_prime_part_power_fibers {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (H : Subgroup K) (t : Finset K)
    (gen : H ⊔ Subgroup.closure (t : Set K) = ⊤) :
    p ^ (Nat.card (fixingSubgroup (MulAut K) (H : Set K))).factorization p ≤
      ∏ x ∈ t, p ^ Nat.log p ({y : K | orderOf y = orderOf x ∧ ∀ n : ℕ, x^n ∈ H → y^n = x^n} : Set K).ncard := by
  apply stabilizer_prime_part_orbit_bound H t gen
  intro f x _
  refine ⟨f.val.orderOf_eq x,?_⟩
  intro n hn
  rw [← map_pow]
  exact (mem_fixingSubgroup_iff _).mp f.property _ hn

/-- If each relative generator has fewer than p possible images, the stabilizer has
trivial p-part. -/
lemma stabilizer_prime_part_one_of_small_fibers {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (H : Subgroup K) (t : Finset K)
    (gen : H ⊔ Subgroup.closure (t : Set K) = ⊤)
    (small : ∀ x ∈ t, ({y : K | orderOf y = orderOf x ∧ ∀ n : ℕ, x^n ∈ H → y^n = x^n} : Set K).ncard < p) :
    p ^ (Nat.card (fixingSubgroup (MulAut K) (H : Set K))).factorization p = 1 := by
  apply Nat.le_antisymm _ (Nat.pow_pos (Fact.out : p.Prime).pos)
  apply (stabilizer_prime_part_power_fibers (p := p) H t gen).trans
  exact le_of_eq (Finset.prod_eq_one fun x hx => by rw [Nat.log_eq_zero_iff.mpr (Or.inl (small x hx)),pow_zero])

theorem hom_count (G A : Type*) [Group G] [Group A] [Finite G] [Finite A] :
    Nat.card (G →* A) ≤ Nat.card A ^ Nat.log 2 (Nat.card G) := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨t, _, ht, hsize⟩ := thin_generators (Finset.univ : Finset G)
  rw [Finset.coe_univ, Subgroup.closure_univ] at ht hsize
  rw [Subgroup.card_top] at hsize
  let restrict (f : G →* A) (x : t) := f x
  have inj : Function.Injective restrict := by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense ht
    intro x hx
    exact congrFun h ⟨x, hx⟩
  calc
    Nat.card (G →* A) ≤ Nat.card (t → A) := Nat.card_le_card_of_injective restrict inj
    _ = Nat.card A ^ t.card := by simp [Nat.card_fun]
    _ ≤ _ := Nat.pow_le_pow_right Nat.card_pos (Nat.le_log_of_pow_le (by decide) hsize)

theorem cyclic_action_count (H K : FiniteGrp.{0}) [IsCyclic H] :
    Nat.card (H →* MulAut K) ≤ Nat.card K ^ Nat.log 2 (Nat.card K) := by
  let _ : Finite (MulAut K) := Finite.of_injective (fun a : MulAut K => (a : K → K))
    (fun _ _ h => DFunLike.ext' h)
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := H)
  have inj : Function.Injective (fun f : H →* MulAut K => f x) := by
    intro f g h
    apply MonoidHom.ext
    intro y
    obtain ⟨z, rfl⟩ := hx y
    simpa only [map_zpow] using congrArg (fun a : MulAut K => a ^ z) h
  let _ : Finite (K →* K) := Finite.of_injective (fun f : K →* K => (f : K → K))
    (fun _ _ h => DFunLike.ext' h)
  have injAut : Function.Injective (fun e : MulAut K => e.toMonoidHom) := by
    intro e f h
    exact DFunLike.ext' (congrArg (fun a : K →* K => (a : K → K)) h)
  exact (Nat.card_le_card_of_injective _ inj).trans
    ((Nat.card_le_card_of_injective _ injAut).trans (hom_count K K))

lemma normal_hall_of_sylow_count {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) (G : FiniteGrp.{0}) (hG : Nat.card G = k*l)
    (hcase : Nat.card (Sylow l G) = k ∨ k.Coprime (l-1)) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = k := by
    classical
    let _ : Fact l.Prime := ⟨hl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd hcop, hl.factorization]
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    have central : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
      rcases hcase with hfull | haut
      · have hind := P.card_eq_index_normalizer.symm.trans hfull
        have hsize := (Subgroup.normalizer (P : Set G)).index_mul_card
        rw [hind, hG] at hsize
        have eq := Subgroup.eq_of_le_of_card_ge P.le_normalizer
          ((Nat.eq_of_mul_eq_mul_left hk hsize).le.trans hP.ge)
        exact eq.ge.trans P.le_centralizer
      · have key := Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
        rw [Subgroup.normalizerMonoidHom_ker, ← Subgroup.index, ← Subgroup.relIndex] at key
        apply Subgroup.relIndex_eq_one.mp
        apply Nat.eq_one_of_dvd_coprimes _ dvd_rfl key
        rw [hc.card_mulAut, hP, Nat.totient_prime hl]
        apply Nat.Coprime.coprime_dvd_left (Subgroup.relIndex_dvd_card ..)
        apply Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
        rw [hG]
        exact haut.mul_left ((Nat.coprime_self_sub_right hl.one_le).mpr (Nat.coprime_one_right _))
    let N := (MonoidHom.transferSylow P central).ker
    have comp : N.IsComplement' (P : Subgroup G) := MonoidHom.ker_transferSylow_isComplement' P central
    have hn : Nat.card N = k := by
      have h := comp.card_mul_card
      change Nat.card N * Nat.card P = Nat.card G at h
      rw [hP, hG] at h
      exact Nat.eq_of_mul_eq_mul_right hl.pos h
    exact ⟨N, inferInstance, hn⟩

/-- Count split extensions by a cyclic complement, restricting the allowed kernels. -/
theorem cyclic_split_count {k l : ℕ} (hl : 0 < l) (W : FiniteGrp.{0} → Prop) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k ∧ W G}).ncard * k^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let _ : NeZero l := ⟨hl.ne'⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1.1
  let _ : Finite (orderClasses k) := ((finite_classes k).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite (orderClasses k)
  let A (x : orderClasses k) := H →* MulAut (K x)
  let (x : orderClasses k) : Finite (A x) := by
    let _ : Finite (MulAut (K x)) := Finite.of_injective (fun a : MulAut (K x) => (a : K x → K x))
      (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A x => (a : H → MulAut (K x))) (fun _ _ h => DFunLike.ext' h)
  let decode (z : (x : orderClasses k) × A x) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    letI : Finite (SemidirectProduct (K z.1) H z.2) :=
      Finite.of_equiv (K z.1 × H) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct (K z.1) H z.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨N, P, hN, comp, hc, hn, hP, hw⟩, rfl⟩
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨hn, hw⟩, rfl⟩
    let i := Classical.choice (Quotient.exact (rep x))
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv.symm
    let fh : P ≃* H := mulEquivOfCyclicCardEq (hP.trans (Nat.card_zmod _).symm)
    let e := SemidirectProduct.mulEquivSubgroup comp
    let f := e.symm.trans (SemidirectProduct.congr' fn fh)
    let a : P →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
    refine ⟨⟨x, MonoidHom.comp (MulAut.congr fn) (a.comp fh.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((x : orderClasses k) × A x) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ x : orderClasses k, Nat.card (A x) := Nat.card_sigma
    _ ≤ ∑ _x : orderClasses k, k^(Nat.log 2 k) := Finset.sum_le_sum fun x _ => by
      simpa only [order] using cyclic_action_count H (K x)
    _ = _ := by simp [← Nat.card_eq_fintype_card, orderClasses]

/-- Count groups having a normal Hall subgroup of prime index. -/
theorem peel {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ (∃ N : Subgroup G, N.Normal ∧ Nat.card N = k)}).ncard ≤ g k * k^(Nat.log 2 k) := by
  classical
  let _ : Fact l.Prime := ⟨hl⟩
  have bound := cyclic_split_count (k := k) hl.pos (fun _ => True)
  simp only [and_true] at bound
  apply le_trans _ bound
  apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono ?_))
  · rintro _ ⟨G, ⟨hG, hcase⟩, rfl⟩
    obtain ⟨N, hN, hn⟩ := hcase
    let _ : N.Normal := hN
    have hind : N.index = l := by
      have h := N.index_mul_card
      rw [hn, hG, Nat.mul_comm k l] at h
      exact Nat.eq_of_mul_eq_mul_right hk h
    have cop : (Nat.card N).Coprime N.index := by
      rw [hn, hind]
      exact (hl.coprime_iff_not_dvd.mpr hcop).symm
    obtain ⟨P, comp⟩ := Subgroup.exists_right_complement'_of_coprime cop
    have hP : Nat.card P = l := comp.symm.index_eq_card.symm.trans hind
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    exact ⟨G, ⟨N, P, hN, comp, hc, hn, hP⟩, rfl⟩
  · rintro G ⟨N, P, _, comp, _, hn, hP⟩
    exact comp.card_mul_card.symm.trans (congrArg₂ (· * ·) hn hP)

/-- Count actions of the allowed complements on a cyclic normal subgroup. -/
theorem cyclic_kernel_count {k l : ℕ} (hl : 0 < l) (W : FiniteGrp.{0} → Prop) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k ∧ W G}).ncard * l^(Nat.log 2 k) := by
  classical
  let orderClasses (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let _ : NeZero l := ⟨hl.ne'⟩
  let H := FiniteGrp.of (Multiplicative (ZMod l))
  let _ : IsCyclic H := inferInstanceAs (IsCyclic (Multiplicative (ZMod l)))
  let K (x : orderClasses k) : FiniteGrp.{0} := x.property.choose
  have rep (x : orderClasses k) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : orderClasses k) : Nat.card (K x) = k := x.property.choose_spec.1.1
  let _ : Finite (orderClasses k) := ((finite_classes k).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite (orderClasses k)
  let A (x : orderClasses k) := K x →* MulAut H
  let (x : orderClasses k) : Finite (A x) := by
    let _ : Finite (MulAut H) := Finite.of_injective (fun a : MulAut H => (a : H → H))
      (fun _ _ h => DFunLike.ext' h)
    exact Finite.of_injective (fun a : A x => (a : K x → MulAut H)) (fun _ _ h => DFunLike.ext' h)
  let decode (z : (x : orderClasses k) × A x) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    letI : Finite (SemidirectProduct H (K z.1) z.2) :=
      Finite.of_equiv (H × K z.1) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct H (K z.1) z.2))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ Nat.card N = k ∧ Nat.card P = l ∧ W (FiniteGrp.of N)} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨N, P, hPnorm, comp, hc, hn, hP, hw⟩, rfl⟩
    let x : orderClasses k := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨hn, hw⟩, rfl⟩
    let i := Classical.choice (Quotient.exact (rep x))
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso i).groupIsoToMulEquiv.symm
    let fh : P ≃* H := mulEquivOfCyclicCardEq (hP.trans (Nat.card_zmod _).symm)
    let e := SemidirectProduct.mulEquivSubgroup comp.symm
    let f := e.symm.trans (SemidirectProduct.congr' fh fn)
    let a : N →* MulAut P := (P : Subgroup G).normalizerMonoidHom.comp
      (Subgroup.inclusion ((P : Subgroup G).normalizer_eq_top ▸ le_top))
    refine ⟨⟨x, MonoidHom.comp (MulAut.congr fh) (a.comp fn.symm)⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) f.symm.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((x : orderClasses k) × A x) :=
      Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ x : orderClasses k, Nat.card (A x) := Nat.card_sigma
    _ ≤ ∑ _x : orderClasses k, l^(Nat.log 2 k) := Finset.sum_le_sum fun x _ => by
      let _ : Finite (MulAut H) := Finite.of_injective (fun a : MulAut H => (a : H → H))
        (fun _ _ h => DFunLike.ext' h)
      have bound := hom_count (K x) (MulAut H)
      have cardH : Nat.card H = l := Nat.card_zmod _
      rw [IsCyclic.card_mulAut H, cardH, order] at bound
      exact bound.trans (Nat.pow_le_pow_left (Nat.totient_le _) _)
    _ = _ := by simp [← Nat.card_eq_fintype_card, orderClasses]

/-- Count the cyclic normal Sylow kernel by actions of a complement of order k. -/
theorem normal_prime_count {k l : ℕ} (hk : 0 < k) (hl : l.Prime)
    (hcop : ¬ l ∣ k) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k*l ∧ Nat.card (Sylow l G) = 1}).ncard ≤ g k * l^(Nat.log 2 k) := by
  classical
  let _ : Fact l.Prime := ⟨hl⟩
  have bound := cyclic_kernel_count (k := k) hl.pos (fun _ => True)
  simp only [and_true] at bound
  apply le_trans _ bound
  apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono ?_))
  · rintro _ ⟨G, ⟨hG, count_one⟩, rfl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd hcop, hl.factorization]
    have hc : IsCyclic P := isCyclic_of_prime_card hP
    have hindex : P.index = k := by
      have h := (P : Subgroup G).index_mul_card
      change P.index * Nat.card P = Nat.card G at h
      rw [hP, hG] at h
      exact Nat.eq_of_mul_eq_mul_right hl.pos h
    let _ : Subsingleton (Sylow l G) := (Nat.card_eq_one_iff_unique.mp count_one).1
    let _ : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    have cop : (Nat.card P).Coprime P.index := by
      rw [hP, hindex]
      exact hl.coprime_iff_not_dvd.mpr hcop
    obtain ⟨N, comp⟩ := Subgroup.exists_right_complement'_of_coprime cop
    have hn : Nat.card N = k := comp.symm.index_eq_card.symm.trans hindex
    exact ⟨G, ⟨N, P, inferInstance, comp.symm, hc, hn, hP⟩, rfl⟩
  · rintro G ⟨N, P, _, comp, _, hn, hP⟩
    exact comp.card_mul_card.symm.trans (congrArg₂ (· * ·) hn hP)

/-- Bound the classes with a normal Sylow subgroup in either characteristic. -/
theorem normal_hall_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)}).ncard ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  have hk : 0 < p^a := pow_pos hp.pos _
  have hcop : ¬ l ∣ p^a := fun h =>
    hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
  have hkr := (Nat.le_mul_of_pos_right (p^a) hl.pos).trans_lt hr
  have overhead (b : ℕ) (hb : b ≤ 2^r) : b^(Nat.log 2 (p^a)) ≤ 2^(r*r) := by
    calc
      _ ≤ (2^r)^(Nat.log 2 (p^a)) := Nat.pow_le_pow_left hb _
      _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hk.ne' hkr).le
      _ = 2^(r*r) := (pow_mul ..).symm
  have hv : (p^a*l).factorization p = a := by
    rw [Nat.factorization_mul hk.ne' hl.ne_zero, Finsupp.add_apply, Nat.factorization_pow_self hp,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h)), add_zero]
  have hmem : p ∈ (p^a*l).primeFactors := Nat.mem_primeFactors.mpr
    ⟨hp, dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _, (Nat.mul_pos hk hl.pos).ne'⟩
  have positive (b : ℕ) (hb : b ∈ (p^a*l).primeFactors) :
      1 ≤ g (b^(p^a*l).factorization b) := by
    exact positive_count (pow_pos (Nat.prime_of_mem_primeFactors hb).pos _)
  have component := Finset.single_le_prod' positive hmem
  rw [hv] at component
  let S (t : FiniteGrp.{0} → Prop) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ t G}
  let A (G : FiniteGrp.{0}) := ∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a
  let B (G : FiniteGrp.{0}) := Nat.card (Sylow l G) = 1
  have cover : S (fun G => A G ∨ B G) = S A ∪ S B := by
    ext c
    constructor
    · rintro ⟨G, ⟨hg, h | h⟩, rfl⟩
      · exact Or.inl ⟨G, ⟨hg, h⟩, rfl⟩
      · exact Or.inr ⟨G, ⟨hg, h⟩, rfl⟩
    · rintro (⟨G, ⟨hg, h⟩, rfl⟩ | ⟨G, ⟨hg, h⟩, rfl⟩)
      · exact ⟨G, ⟨hg, Or.inl h⟩, rfl⟩
      · exact ⟨G, ⟨hg, Or.inr h⟩, rfl⟩
  let L := ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b)
  have major (b : ℕ) (hb : b ≤ 2^r) :
      g (p^a)*b^(Nat.log 2 (p^a)) ≤ 2^(r*r)*L :=
    (Nat.mul_comm ..).le.trans (Nat.mul_le_mul (overhead _ hb) component)
  have boundA := (peel hk hl hcop).trans (major _ hkr.le)
  have boundB := (normal_prime_count hk hl hcop).trans
    (major _ ((Nat.le_mul_of_pos_left l hk).trans hr.le))
  change (S (fun G => A G ∨ B G)).ncard ≤ _
  rw [cover]
  calc
    _ ≤ (S A).ncard + (S B).ncard := Set.ncard_union_le _ _
    _ ≤ 2^(r*r)*L + 2^(r*r)*L := Nat.add_le_add boundA boundB
    _ = 2^(r*r+1)*L := by rw [pow_succ]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : r*r+1 ≤ (r+1)^2))

/-- The requested estimate with E = 1 for orders p^a l, under either normal-complement or normal-Sylow criterion. -/
theorem two_prime_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) (criterion : ¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    g (p^a*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  have hk : 0 < p^a := pow_pos hp.pos _
  have hcop : ¬ l ∣ p^a := fun h =>
    hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp (hl.dvd_of_dvd_pow h))
  apply le_trans _ (normal_hall_bound hp hl hne ha hr)
  classical
  apply le_of_eq
  unfold g
  congr 1
  apply congrArg
  ext G
  constructor
  · intro hG
    refine ⟨hG, ?_⟩
    have transfer := normal_hall_of_sylow_count hk hl hcop G hG
    rcases criterion with haut | hres
    · exact Or.inl (transfer (Or.inr ((hp.coprime_iff_not_dvd.mpr haut).pow_left a)))
    let _ : Fact l.Prime := ⟨hl⟩
    let P : Sylow l G := default
    have hP : Nat.card P = l := by
      rw [P.card_eq_multiplicity, hG, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ l ∣ p from fun h =>
        hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp h)), hl.factorization]
    have ind := (P : Subgroup G).index_mul_card
    change P.index * Nat.card P = Nat.card G at ind
    rw [hP, hG] at ind
    have hdiv := (Nat.eq_of_mul_eq_mul_right hl.pos ind) ▸ P.card_dvd_index
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow hp).mp hdiv
    by_cases hz : i = 0
    · exact Or.inr (by simpa [hz] using he)
    by_cases heq : i = a
    · exact Or.inl (transfer (Or.inl (heq ▸ he)))
    exact (hres i (Nat.pos_of_ne_zero hz) (lt_of_le_of_ne hi heq)
      (he ▸ card_sylow_modEq_one l G)).elim
  · exact fun h => h.1

/-- Every odd order p^a l with a at most three satisfies the desired estimate. -/
theorem small_exponent_bound {p l r a : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (hop : Odd p) (hol : Odd l) (ha : 0 < a) (ha3 : a ≤ 3) (hr : p^a*l < 2^r) :
    g (p^a*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  apply two_prime_bound hp hl hne _ ha hr
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · right
    obtain ⟨u, hu⟩ := hop
    obtain ⟨v, hv⟩ := hol
    have gap : p+1 < l := by omega
    have ppos := hp.one_lt
    have small₁ : ¬ l ∣ p-1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    have small₂ : ¬ l ∣ p+1 := Nat.not_dvd_of_pos_of_lt (by omega) gap
    intro i hi hle he
    have hdvd := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp.pos)).mp he.symm
    have hi2 : i ≤ 2 := by omega
    interval_cases i
    · exact small₁ (by simpa using hdvd)
    · have factor : p^2-1 = (p-1)*(p+1) := by
        have h := Nat.sub_add_cancel (show 1 ≤ p by omega)
        have h' := Nat.sub_add_cancel (show 1 ≤ p^2 from Nat.pow_pos hp.pos)
        nlinarith [congrArg (fun x : ℕ => x * (p+1)) h]
      exact (hl.dvd_mul.mp (factor ▸ hdvd)).elim small₁ small₂
  · left
    exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hl.one_lt) (by omega)

/-- Specialization to odd orders p² l. -/
theorem square_prime_bound {p l r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (hop : Odd p) (hol : Odd l) (hr : p^2*l < 2^r) :
    g (p^2*l) ≤ 2^((r+1)^2) *
      ∏ b ∈ (p^2*l).primeFactors, g (b^(p^2*l).factorization b) :=
  small_exponent_bound hp hl hne hop hol (by decide) (by decide) hr

/-- An abelian Sylow subgroup of prime index is normal or has a normal complement. -/
theorem normal_hall_of_abelian {p l a : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (G : FiniteGrp.{0}) (hg : Nat.card G = p^a*l) (P : Sylow p G) [IsMulCommutative P] :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1 := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact l.Prime := ⟨hl⟩
  have hk := pow_pos hp.pos a
  have hP : Nat.card P = p^a := by
    rw [P.card_eq_multiplicity, hg, Nat.factorization_mul hk.ne' hl.ne_zero,
      Finsupp.add_apply, Nat.factorization_pow_self hp, Nat.factorization_eq_zero_of_not_dvd
        (fun h => hne ((Nat.prime_dvd_prime_iff_eq hp hl).mp h)), add_zero]
  have ind := (P : Subgroup G).index_mul_card
  change P.index * Nat.card P = Nat.card G at ind
  rw [hP, hg, Nat.mul_comm (p^a) l] at ind
  have index := Nat.eq_of_mul_eq_mul_right hk ind
  rcases (Nat.dvd_prime hl).mp (index ▸ P.card_dvd_index) with one | full
  · let _ : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp one).1
    exact Or.inl ⟨P, Sylow.normal_of_subsingleton P, hP⟩
  · have size := (Subgroup.normalizer (P : Set G)).index_mul_card
    rw [← P.card_eq_index_normalizer, full, hg, Nat.mul_comm (p^a) l] at size
    have eq := Subgroup.eq_of_le_of_card_ge P.le_normalizer
      ((Nat.eq_of_mul_eq_mul_left hl.pos size).le.trans hP.ge)
    have central : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) :=
      eq.ge.trans P.le_centralizer
    let N := (MonoidHom.transferSylow P central).ker
    have comp : N.IsComplement' (P : Subgroup G) :=
      MonoidHom.ker_transferSylow_isComplement' P central
    have hn : Nat.card N = l := comp.index_eq_card.symm.trans index
    let Q := Sylow.ofCard (p := l) N (by
      rw [hn, hg, Nat.factorization_mul hk.ne' hl.ne_zero]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ l ∣ p from fun h =>
        hne.symm ((Nat.prime_dvd_prime_iff_eq hl hp).mp h)), hl.factorization])
    let _ := Q.unique_of_normal (by change N.Normal; infer_instance)
    exact Or.inr (Nat.card_unique)

/-- At prime index, the abelian Sylow case satisfies the estimate with E = 1. -/
theorem abelian_sylow_bound {p l a r : ℕ} (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l)
    (ha : 0 < a) (hr : p^a*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ ∃ P : Sylow p G, IsMulCommutative P}).ncard ≤
      2^((r+1)^2) * ∏ b ∈ (p^a*l).primeFactors, g (b^(p^a*l).factorization b) := by
  apply le_trans _ (normal_hall_bound hp hl hne ha hr)
  apply Set.ncard_le_ncard _ ((finite_classes _).subset (Set.image_mono (fun _ h => h.1)))
  rintro _ ⟨G, ⟨hg, P, hc⟩, rfl⟩
  exact ⟨G, ⟨hg, normal_hall_of_abelian hp hl hne G hg P⟩, rfl⟩

/-- Count complementary cyclic and nilpotent Hall factors when either factor is normal. -/
theorem cyclic_nilpotent_hall_bound {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^((r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let W (G : FiniteGrp.{0}) := Group.IsSolvable G ∧ Group.IsNilpotent G
  let L := ∏ p ∈ q.primeFactors, g (p^q.factorization p)
  let S (normalNilpotent : Bool) (k : Fin (q+1)) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ N P : Subgroup G, (if normalNilpotent then N.Normal else P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧
      Nat.card N = k.val ∧ Nat.card P = q/k.val ∧ W (FiniteGrp.of N)}
  let I := {k : Fin (q+1) // 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  have bound (b : Bool) (i : I) : (S b i.val).ncard ≤ 2^(r*r)*L := by
    obtain ⟨k, hk, hb, eq, cop⟩ := i
    have parts : (∏ p ∈ k.val.primeFactors, g (p^k.val.factorization p)) ≤ L := by
      have sub : k.val.primeFactors ⊆ q.primeFactors := by
        rw [← congrArg Nat.primeFactors eq, Nat.primeFactors_mul hk.ne' hb.ne']
        exact Finset.subset_union_left
      calc
        _ = ∏ p ∈ k.val.primeFactors, g (p^q.factorization p) := by
          apply Finset.prod_congr rfl
          intro p hp
          have notdvd : ¬ p ∣ q/k.val := fun h => (Nat.prime_of_mem_primeFactors hp).not_dvd_one
            (cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) h)
          rw [← congrArg Nat.factorization eq, Nat.factorization_mul hk.ne' hb.ne', Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd notdvd, add_zero]
        _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' sub fun p hp _ =>
          positive_count (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
    have hkr : k.val < 2^r := (Nat.le_of_lt_succ k.isLt).trans_lt hr
    have overhead (u : ℕ) (hu : u ≤ 2^r) : u^(Nat.log 2 k.val) ≤ 2^(r*r) := by
      calc
        _ ≤ (2^r)^(Nat.log 2 k.val) := Nat.pow_le_pow_left hu _
        _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hk.ne' hkr).le
        _ = _ := (pow_mul ..).symm
    have cost (u : ℕ) (hu : u ≤ 2^r) := (Nat.mul_le_mul ((nilpotent_bound k.val).trans parts)
      (overhead u hu)).trans (Nat.mul_comm ..).le
    cases b
    · exact (cyclic_kernel_count hb W).trans (cost _ ((Nat.div_le_self ..).trans hr.le))
    · exact (cyclic_split_count hb W).trans (cost _ hkr.le)
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))} ⊆
      ⋃ z : Bool × I, S z.1 z.2.val := by
    rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hc, hnil, cop⟩, rfl⟩
    have eq := comp.card_mul_card.trans hg
    have hk : 0 < Nat.card N := Nat.card_pos
    have hb : 0 < Nat.card P := Nat.card_pos
    have div : q / Nat.card N = Nat.card P := by rw [← eq, Nat.mul_div_cancel_left _ hk]
    let k : Fin (q+1) := ⟨Nat.card N, by have := (Nat.le_mul_of_pos_right (Nat.card N) hb).trans eq.le; omega⟩
    let i : I := ⟨k, hk, div.symm ▸ hb, div.symm ▸ eq, div.symm ▸ cop⟩
    rcases hn with hn | hp
    · refine Set.mem_iUnion.mpr ⟨(true, i), G, ⟨N, P, hn, comp, hc, rfl, div.symm, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
    · refine Set.mem_iUnion.mpr ⟨(false, i), G, ⟨N, P, hp, comp, hc, rfl, div.symm, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
  have finite (z : Bool × I) : (S z.1 z.2.val).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨N, P, _, comp, _, hn, hp, _⟩
    exact comp.card_mul_card.symm.trans ((congrArg₂ (· * ·) hn hp).trans z.2.property.2.2.1)))
  calc
    _ ≤ (⋃ z : Bool × I, S z.1 z.2.val).ncard := Set.ncard_le_ncard cover (Set.finite_iUnion finite)
    _ ≤ ∑ z : Bool × I, (S z.1 z.2.val).ncard := Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _ : Bool × I, 2^(r*r)*L := Finset.sum_le_sum fun z _ => bound z.1 z.2
    _ = (2 * Fintype.card I) * (2^(r*r)*L) := by simp
    _ ≤ (2 * 2^r) * (2^(r*r)*L) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by
      have h := Fintype.card_subtype_le (fun k : Fin (q+1) => 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val))
      simpa [I] using h.trans (by simpa using hr : Fintype.card (Fin (q+1)) ≤ 2^r)))
    _ = 2^(r+r*r+1)*L := by rw [pow_succ, pow_add]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : r+r*r+1 ≤ (r+1)^2))

/-- Count homomorphisms by evaluating on a generating set of minimum size. -/
lemma rank_hom_count (G A : Type*) [Group G] [Group A] [Finite G] [Finite A] :
    Nat.card (G →* A) ≤ Nat.card A ^ Group.rank G := by
  classical
  obtain ⟨t, size, gen⟩ := Group.rank_spec G
  let restrict (f : G →* A) (x : t) := f x
  have inj : Function.Injective restrict := by
    intro f g h
    apply MonoidHom.eq_of_eqOn_dense gen
    exact fun x hx => congrFun h ⟨x, hx⟩
  simpa [Nat.card_fun, size] using Nat.card_le_card_of_injective restrict inj

lemma sylow_product_coprime {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (cop : k.Coprime l) :
    (∏ p ∈ (k*l).primeFactors, g (p^(k*l).factorization p)) =
      (∏ p ∈ k.primeFactors, g (p^k.factorization p)) * ∏ p ∈ l.primeFactors, g (p^l.factorization p) := by
  have part {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) (p : ℕ) (hp : p ∈ a.primeFactors) :
      (a*b).factorization p = a.factorization p := by
    have nd : ¬ p ∣ b := fun hh => (Nat.prime_of_mem_primeFactors hp).not_dvd_one
      (h ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hh)
    simp [Nat.factorization_mul ha.ne' hb.ne', Nat.factorization_eq_zero_of_not_dvd nd]
  rw [Nat.primeFactors_mul hk.ne' hl.ne', Finset.prod_union cop.disjoint_primeFactors]
  congr 1
  · exact Finset.prod_congr rfl fun p hp => by rw [part hk hl cop p hp]
  · exact Finset.prod_congr rfl fun p hp => by rw [Nat.mul_comm k l, part hl hk cop.symm p hp]

/-- Count nilpotent Hall extensions whose generator images fit the quadratic exponent. -/
theorem hall_action_bound {q r d : ℕ} (hd : 0 < d) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*d) ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^(d*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let W (G : FiniteGrp.{0}) := Group.IsSolvable G ∧ Group.IsNilpotent G
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ W G}
  let K {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  have rep {n : ℕ} (x : O n) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order {n : ℕ} (x : O n) : Nat.card (K x) = n := x.property.choose_spec.1.1
  let (n : ℕ) : Finite (O n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  let T (i : I) := (x : O i.val.val × O (q/i.val.val)) ×
    {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)}
  let autFin (H : FiniteGrp.{0}) : Finite (MulAut H) :=
    Finite.of_injective (fun a : MulAut H => (a : H → H)) (fun _ _ h => DFunLike.ext' h)
  let actFin (H J : FiniteGrp.{0}) : Finite (H →* MulAut J) :=
    Finite.of_injective (fun a : H →* MulAut J => (a : H → MulAut J)) (fun _ _ h => DFunLike.ext' h)
  let (i : I) : Finite (T i) := inferInstanceAs (Finite (Sigma _))
  let decode (z : (i : I) × T i) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    let x := z.2.1
    let a := z.2.2.val
    let _ : Finite (SemidirectProduct (K x.1) (K x.2) a) :=
      Finite.of_equiv (K x.1 × K x.2) SemidirectProduct.equivProd.symm
    exact Quotient.mk _ (FiniteGrp.of (SemidirectProduct (K x.1) (K x.2) a))
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*d) ∧ (Nat.card N).Coprime (Nat.card P))} ⊆ Set.range decode := by
    rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, rank, cop⟩, rfl⟩
    have eq := comp.card_mul_card.trans hg
    have hk : 0 < Nat.card N := Nat.card_pos
    have hb : 0 < Nat.card P := Nat.card_pos
    have div : q / Nat.card N = Nat.card P := by rw [← eq, Nat.mul_div_cancel_left _ hk]
    let k : Fin (q+1) := ⟨Nat.card N, by have := (Nat.le_mul_of_pos_right (Nat.card N) hb).trans eq.le; omega⟩
    let i : I := ⟨k, hk, div.symm ▸ hb, div.symm ▸ eq, div.symm ▸ cop⟩
    let x : O k.val := ⟨Quotient.mk _ (FiniteGrp.of N), FiniteGrp.of N, ⟨rfl, inferInstanceAs (Group.IsSolvable N), hnil⟩, rfl⟩
    let y : O (q/k.val) := ⟨Quotient.mk _ (FiniteGrp.of P), FiniteGrp.of P, ⟨div.symm, inferInstanceAs (Group.IsSolvable P), hpnil⟩, rfl⟩
    let fn : N ≃* K x := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep x)))).groupIsoToMulEquiv.symm
    let fp : P ≃* K y := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep y)))).groupIsoToMulEquiv.symm
    let a : P →* MulAut N := N.normalizerMonoidHom.comp (Subgroup.inclusion (N.normalizer_eq_top ▸ le_top))
    let e := (SemidirectProduct.mulEquivSubgroup comp).symm.trans (SemidirectProduct.congr' fn fp)
    refine ⟨⟨i, ⟨x,y⟩, ⟨MonoidHom.comp (MulAut.congr fn) (a.comp fp.symm), by simpa only [← Group.rank_congr fn, ← Group.rank_congr fp, ← Nat.card_congr fn.toEquiv] using rank⟩⟩, Quotient.sound ?_⟩
    exact ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) e.symm.toGrpIso⟩
  have bound (i : I) : Nat.card (T i) ≤ L q * 2^(r*r*d) := by
    let k := i.val.val
    let l := q/k
    have hk : 0 < k := i.property.1
    have hl : 0 < l := i.property.2.1
    have eq : k*l = q := i.property.2.2.1
    let _ := Fintype.ofFinite (O k × O l)
    have cnt (x : O k × O l) : Nat.card {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} ≤ 2^(r*r*d) := by
      by_cases hd : Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)
      · apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        apply (rank_hom_count (K x.2) (MulAut (K x.1))).trans
        have inj : Function.Injective (fun a : MulAut (K x.1) => a.toMonoidHom) := by
          intro a b h
          exact DFunLike.ext' (congrArg (fun f : K x.1 →* K x.1 => (f : K x.1 → K x.1)) h)
        let _ : Finite (K x.1 →* K x.1) := Finite.of_injective (fun f : K x.1 →* K x.1 => (f : K x.1 → K x.1)) (fun _ _ h => DFunLike.ext' h)
        have ba := (Nat.card_le_card_of_injective _ inj).trans (rank_hom_count (K x.1) (K x.1))
        exact (Nat.pow_le_pow_left ba _).trans ((pow_mul ..).symm.le.trans hd)
      · let _ : IsEmpty {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} := ⟨fun a => hd a.property⟩
        simp
    calc
      _ = ∑ x : O k × O l, Nat.card {a : K x.2 →* MulAut (K x.1) // Nat.card (K x.1) ^ (Group.rank (K x.1) * Group.rank (K x.2)) ≤ 2^(r*r*d)} := Nat.card_sigma
      _ ≤ ∑ _ : O k × O l, 2^(r*r*d) := Finset.sum_le_sum fun x _ => cnt x
      _ = (Nat.card (O k) * Nat.card (O l)) * 2^(r*r*d) := by simp [← Nat.card_eq_fintype_card, Nat.card_prod]
      _ ≤ _ := Nat.mul_le_mul_right _ (by rw [← eq]; unfold L; rw [sylow_product_coprime hk hl i.property.2.2.2]; exact Nat.mul_le_mul (nilpotent_bound k) (nilpotent_bound l))
  let _ := Fintype.ofFinite I
  have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((i : I) × T i) := Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = ∑ i : I, Nat.card (T i) := Nat.card_sigma
    _ ≤ ∑ _ : I, L q * 2^(r*r*d) := Finset.sum_le_sum fun i _ => bound i
    _ = Nat.card I * (L q * 2^(r*r*d)) := by simp [Nat.card_eq_fintype_card]
    _ ≤ 2^r * (L q * 2^(r*r*d)) := Nat.mul_le_mul_right _ ni
    _ = 2^(r+r*r*d) * L q := by rw [pow_add]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith [Nat.mul_le_mul_left r hd, Nat.zero_le (r*d)] : r+r*r*d ≤ d*(r+1)^2))

/-- A rank bound on either factor controls split extensions of two nilpotent Hall factors. -/
theorem bounded_rank_hall_bound {q r d : ℕ} (hd : 0 < d) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ min (Group.rank N) (Group.rank P) ≤ d ∧ (Nat.card N).Coprime (Nat.card P))}).ncard ≤
      2^(d*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  apply le_trans _ (hall_action_bound hd hr)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
  rintro _ ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, hmin, cop⟩, rfl⟩
  refine ⟨G, ⟨hg, hs, N, P, hn, comp, hnil, hpnil, ?_, cop⟩, rfl⟩
  have rank_le (H : Subgroup G) : Group.rank H ≤ r := by
    let _ := Fintype.ofFinite H
    obtain ⟨t, _, ht, size⟩ := thin_generators (Finset.univ : Finset H)
    rw [Finset.coe_univ, Subgroup.closure_univ] at ht size
    rw [Subgroup.card_top] at size
    have hcard : Nat.card H ≤ Nat.card G := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    exact (Group.rank_le ht).trans ((Nat.le_log_of_pow_le (by decide) size).trans
      (Nat.log_lt_of_lt_pow Nat.card_pos.ne' (hcard.trans_lt (hg ▸ hr))).le)
  have prod : Group.rank N * Group.rank P ≤ r*d := by
    rcases min_le_iff.mp hmin with h | h
    · exact (Nat.mul_le_mul h (rank_le P)).trans (Nat.mul_comm ..).le
    · exact Nat.mul_le_mul (rank_le N) h
  have nk : Nat.card N ≤ 2^r :=
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective : Nat.card N ≤ Nat.card G).trans (hg ▸ hr.le)
  calc
    _ ≤ (2^r)^(Group.rank N * Group.rank P) := Nat.pow_le_pow_left nk _
    _ ≤ (2^r)^(r*d) := Nat.pow_le_pow_right (by positivity) prod
    _ = _ := by rw [← pow_mul, Nat.mul_assoc]

/-- For a split diagonal action, multiplicities of the one-dimensional actions
determine the middle group up to isomorphism. Both bounds count fixed factors. -/
theorem diagonal_class_bound (C H : FiniteGrp.{0}) (t : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
        (∀ h v i, a h v i = χ i h (v i)) ∧
        Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}).ncard ≤
      min ((Nat.card (H →* MulAut C))^t) ((t+1)^(Nat.card (H →* MulAut C))) := by
  classical
  let A := H →* MulAut C
  let _ : Finite (MulAut C) := Finite.of_injective (fun a : MulAut C => (a : C → C))
    (fun _ _ h => DFunLike.ext' h)
  let _ : Finite A := Finite.of_injective (fun f : A => (f : H → MulAut C))
    (fun _ _ h => DFunLike.ext' h)
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (χ : Fin t → A) (a : H →* MulAut (Fin t → C)),
      (∀ h v i, a h v i = χ i h (v i)) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose χ a diag iso using fun x : S => x.property.choose_spec.1
  have same (x y : S) (e : Fin t ≃ Fin t) (matchChar : ∀ i, χ y (e i) = χ x i) : x = y := by
    let perm : (Fin t → C) ≃* (Fin t → C) :=
      { Equiv.arrowCongr e (Equiv.refl C) with map_mul' := fun _ _ => rfl }
    have commute (h : H) : (a x h).trans perm = perm.trans (a y h) := by
      ext v j
      change a x h v (e.symm j) = a y h (perm v) j
      rw [diag x, diag y, ← matchChar (e.symm j), e.apply_symm_apply]
      rfl
    let mid := SemidirectProduct.congr perm (MulEquiv.refl H) commute
    let giso := (iso x).some.trans (mid.trans (iso y).some.symm)
    apply Subtype.ext
    rw [← rep x, ← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) giso.toGrpIso⟩
  let count (x : S) (b : A) : Fin (t+1) :=
    ⟨Nat.card {i // χ x i = b}, Nat.lt_succ_of_le (by
      simpa using Nat.card_le_card_of_injective (fun i : {i // χ x i = b} => i.val) Subtype.val_injective)⟩
  have inj : Function.Injective count := by
    intro x y h
    have eq (b : A) : Nat.card {i // χ x i = b} = Nat.card {i // χ y i = b} :=
      congrArg Fin.val (congrFun h b)
    let fibers (b : A) : {i // χ x i = b} ≃ {i // χ y i = b} :=
      (Finite.equivFinOfCardEq (eq b)).trans (Finite.equivFinOfCardEq rfl).symm
    exact same x y (Equiv.ofFiberEquiv fibers) (Equiv.ofFiberEquiv_map fibers)
  change Nat.card S ≤ _
  apply le_min
  · have hi : Function.Injective χ := fun {x y} h => same x y (Equiv.refl _) (fun i => congrFun h.symm i)
    simpa [Nat.card_fun, A] using Nat.card_le_card_of_injective χ hi
  · simpa [Nat.card_fun, A] using Nat.card_le_card_of_injective count inj

/-- Restriction to the ground field bounds the length of an independent family of simple summands. -/
lemma simple_summand_count (F A M : Type*) [Field F] [Ring A] [Algebra F A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M] [Module.Finite F M]
    (s : Set (Submodule A M)) (ind : sSupIndep s) (simple : ∀ m ∈ s, IsSimpleModule A m) :
    s.Finite ∧ Nat.card s ≤ Module.finrank F M := by
  classical
  have nz (m : s) : ∃ v : M, v ∈ m.val ∧ v ≠ 0 := by
    let _ := simple m.val m.property
    let _ := IsSimpleModule.nontrivial A m.val
    obtain ⟨v, hv⟩ := exists_ne (0 : m.val)
    exact ⟨v, v.property, fun h => hv (Subtype.ext h)⟩
  choose v hv hn using nz
  have hind : iSupIndep (fun m : s => m.val.restrictScalars F) := by
    apply iSupIndep_def.mpr
    intro i
    simpa only [← Submodule.restrictScalars_iSup, Submodule.disjoint_restrictScalars_iff] using
      (iSupIndep_def.mp ((sSupIndep_iff s).mp ind) i)
  have lin := hind.linearIndependent _ hv hn
  let _ : Finite s := lin.finite
  let _ := Fintype.ofFinite s
  exact ⟨Set.toFinite _, by simpa [Nat.card_eq_fintype_card] using lin.fintype_card_le_finrank⟩

/-- A catalogue of simple group-algebra modules, valid over a nonsplitting field. -/
theorem simple_group_algebra_catalogue (F H : Type) [Field F] [Group H] [Finite H]
    [NeZero (Nat.card H : F)] :
    ∃ s : Finset (Ideal (MonoidAlgebra F H)), s.card ≤ Nat.card H ∧
      (∀ I ∈ s, IsSimpleModule (MonoidAlgebra F H) I) ∧
      ∀ (V : Type) [AddCommGroup V] [Module (MonoidAlgebra F H) V] [IsSimpleModule (MonoidAlgebra F H) V],
        ∃ I ∈ s, Nonempty (V ≃ₗ[MonoidAlgebra F H] I) := by
  classical
  let A := MonoidAlgebra F H
  let _ := Fintype.ofFinite H
  let basis := MonoidAlgebra.basis H F
  let _ : Module.Finite F A := Module.Finite.of_basis basis
  obtain ⟨s, ind, top, simple⟩ := IsSemisimpleModule.exists_sSupIndep_sSup_simples_eq_top A A
  obtain ⟨hs, size⟩ := simple_summand_count F A A s ind simple
  refine ⟨hs.toFinset, ?_, fun I h => simple I (hs.mem_toFinset.mp h), ?_⟩
  · have dim : Module.finrank F A = Fintype.card H := Module.finrank_eq_card_basis basis
    simpa [← Set.ncard_eq_toFinset_card s hs, Set.ncard_def, dim,
      Nat.card_eq_fintype_card] using size
  · intro V _ _ _
    obtain ⟨I, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule A V
    let _ : IsSimpleModule A I := e.isSimpleModule_iff.mp inferInstance
    let _ (m : s) : IsSimpleModule A m := simple m.val m.property
    obtain ⟨J, hJ, ⟨f⟩⟩ := I.linearEquiv_of_sSup_eq_top s top
    exact ⟨J, hs.mem_toFinset.mpr hJ, ⟨e.trans f⟩⟩

/-- Write a finite-dimensional module as a list of catalogue entries of length at most its dimension. -/
lemma module_catalogue_code (F A V : Type) [Field F] [Ring A] [Algebra F A]
    [AddCommGroup V] [Module A V] [Module F V] [IsScalarTower F A V] [Module.Finite F V]
    [IsSemisimpleModule A V] (c : Finset (Ideal A))
    (cover : ∀ (M : Type) [AddCommGroup M] [Module A M] [IsSimpleModule A M],
      ∃ I ∈ c, Nonempty (M ≃ₗ[A] I)) :
    ∃ n ≤ Module.finrank F V, ∃ f : Fin n → c, Nonempty (V ≃ₗ[A] ((i : Fin n) → (f i).val)) := by
  classical
  obtain ⟨s, e, ind, simple⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp A V
  obtain ⟨finite, bound⟩ := simple_summand_count F A V s ind (fun m hm => simple ⟨m,hm⟩)
  let _ := finite.fintype
  let _ (m : s) : IsSimpleModule A m.val := simple m
  choose ideal mem iso using fun m : s => cover m.val
  let b := Finite.equivFin s
  let f (i : Fin (Nat.card s)) : c := ⟨ideal (b.symm i), mem _⟩
  let u := (e.trans DFinsupp.linearEquivFunOnFintype).trans (LinearEquiv.piCongrRight fun m => (iso m).some)
  exact ⟨_, bound, f, ⟨u.trans (LinearEquiv.piCongrLeft' A _ b)⟩⟩

/-- Count pairwise nonisomorphic group-algebra modules of dimension at most t. -/
theorem coprime_module_family_bound (F H : Type) [Field F] [Group H] [Finite H]
    [NeZero (Nat.card H : F)] {ι : Type*} (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module (MonoidAlgebra F H) (V i)]
    [∀ i, Module F (V i)] [∀ i, IsScalarTower F (MonoidAlgebra F H) (V i)]
    [∀ i, Module.Finite F (V i)] (t : ℕ) (dim : ∀ i, Module.finrank F (V i) ≤ t)
    (distinct : ∀ i j, Nonempty (V i ≃ₗ[MonoidAlgebra F H] V j) → i = j) :
    Finite ι ∧ Nat.card ι ≤ (Nat.card H + 1)^t := by
  classical
  let A := MonoidAlgebra F H
  obtain ⟨c, size, _, cover⟩ := simple_group_algebra_catalogue F H
  choose n hn f iso using fun i => module_catalogue_code F A (V i) c cover
  let code (i : ι) : (k : Fin (t+1)) × (Fin k.val → c) :=
    ⟨⟨n i, Nat.lt_succ_of_le ((hn i).trans (dim i))⟩, f i⟩
  let model (z : (k : Fin (t+1)) × (Fin k.val → c)) := (j : Fin z.1.val) → z.2 j |>.val
  have inj : Function.Injective code := by
    intro i j h
    have transport (z w : (k : Fin (t+1)) × (Fin k.val → c)) (hzw : z = w) :
        Nonempty (model z ≃ₗ[A] model w) := by
      subst w
      exact ⟨LinearEquiv.refl A _⟩
    have bridge := transport _ _ h
    exact distinct i j ⟨(iso i).some.trans (bridge.some.trans (iso j).some.symm)⟩
  have sum_bound (m : ℕ) : (∑ k : Fin (m+1), c.card^k.val) ≤ (c.card+1)^m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_succ, pow_succ]
      simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ, ← Finset.sum_mul]
      have one : 1 ≤ (c.card+1)^m := Nat.pow_pos (by omega)
      nlinarith [Nat.mul_le_mul_right c.card ih]
  refine ⟨Finite.of_injective code inj, (Nat.card_le_card_of_injective code inj).trans ?_⟩
  rw [Nat.card_sigma]
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card (α := ↥c), Fintype.card_coe] using
    (sum_bound t).trans (Nat.pow_le_pow_left (Nat.add_le_add_right size 1) t)

/-- Summing translates of a map produces an intertwiner. -/
lemma average_intertwines {R H : Type*} [Ring R] [Group H] [Fintype H]
    (a b : H →* R) (T : R) (g : H) :
    b g * (∑ h : H, b h * T * a h⁻¹) = (∑ h : H, b h * T * a h⁻¹) * a g := by
  let f (h : H) := b h * T * a h⁻¹ * a g
  calc
    _ = ∑ h : H, f (g*h) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      have cancel : a ((g*h)⁻¹) * a g = a h⁻¹ := by rw [← a.map_mul]; simp
      simp only [f, mul_assoc, cancel, map_mul]
    _ = ∑ h : H, f h := Equiv.sum_comp (Equiv.mulLeft g) f
    _ = _ := (Finset.sum_mul ..).symm

/-- Lift a specified invertible intertwiner modulo p by averaging a normalized entrywise lift. -/
theorem prime_power_intertwiner {p n : ℕ} [Fact p.Prime] (hn : 0 < n)
    {I H : Type*} [Fintype I] [DecidableEq I] [Group H] [Fintype H]
    (cop : ¬ p ∣ Fintype.card H)
    (a b : H →* Matrix I I (ZMod (p^n)))
    (T : Matrix I I (ZMod p)) (unitT : IsUnit T)
    (inter : ∀ h, (b h).map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) * T =
      T * (a h).map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p))) :
    ∃ U : Matrix I I (ZMod (p^n)), IsUnit U ∧
      U.map (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) = T ∧ ∀ g, b g * U = U * a g := by
  classical
  let φ := ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)
  let ψ : Matrix I I (ZMod (p^n)) →+* Matrix I I (ZMod p) := φ.mapMatrix
  let c : ZMod p := Fintype.card H
  have hc : c ≠ 0 := fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h)
  let V : Matrix I I (ZMod (p^n)) := fun i j => (ZMod.castHom_surjective (dvd_pow_self p hn.ne') (c⁻¹ * T i j)).choose
  have hv : ψ V = c⁻¹ • T := by
    ext i j
    exact (ZMod.castHom_surjective (dvd_pow_self p hn.ne') (c⁻¹ * T i j)).choose_spec
  let U := ∑ h : H, b h * V * a h⁻¹
  have red : ψ U = T := by
    have term (h : H) : ψ (b h * V * a h⁻¹) = c⁻¹ • T := by
      simp only [map_mul, hv, Matrix.mul_smul, Matrix.smul_mul]
      change c⁻¹ • (((b h).map φ * T) * ψ (a h⁻¹)) = _
      rw [inter, mul_assoc]
      change c⁻¹ • (T * (ψ (a h) * ψ (a h⁻¹))) = _
      rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, mul_one]
    simp only [U, map_sum, term, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), smul_smul]
    change (c*c⁻¹) • T = T
    rw [mul_inv_cancel₀ hc, one_smul]
  refine ⟨U, (Matrix.isUnit_iff_isUnit_det U).mpr ?_, red, average_intertwines a b V⟩
  let _ : NeZero (p^n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hd : φ U.det ≠ 0 := by
    rw [φ.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det (ψ U)).mp (red.symm ▸ unitT)).ne_zero
  rw [← ZMod.natCast_zmod_val U.det]
  apply (ZMod.isUnit_natCast_iff_not_dvd_pow Fact.out hn).mpr
  intro h
  apply hd
  rw [← ZMod.natCast_zmod_val U.det, map_natCast, ZMod.natCast_eq_zero_iff]
  exact h

/-- Fixed complement and homocyclic kernel, including higher-dimensional irreducible representations. -/
theorem homocyclic_kernel_classes (p n t : ℕ) (hn : 0 < n) [Fact p.Prime] (H : FiniteGrp.{0})
    [NeZero (Nat.card H : ZMod p)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut (Multiplicative (Fin t → ZMod (p^n))),
        Nonempty (G ≃* SemidirectProduct _ H a)}).ncard ≤ (Nat.card H + 1)^t := by
  classical
  let _ := Fintype.ofFinite H
  let V := Fin t → ZMod (p^n)
  let K := Multiplicative V
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let integral (x : S) : Representation (ZMod (p^n)) H V :=
    { toFun := fun h => (AddMonoidHom.toMultiplicative.symm ((a x h).toMonoidHom)).toZModLinearMap (p^n)
      map_one' := by apply LinearMap.ext; intro v; change (a x 1) v = v; rw [map_one]; rfl
      map_mul' := by intro h j; apply LinearMap.ext; intro v; change (a x (h*j)) v = (a x h) ((a x j) v); rw [map_mul]; rfl }
  let φ := ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)
  let M (x : S) := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp (integral x)
  let red (x : S) := φ.mapMatrix.toMonoidHom.comp (M x)
  let ρ (x : S) : Representation (ZMod p) H (Fin t → ZMod p) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp (red x)
  change Nat.card S ≤ _
  apply (coprime_module_family_bound (ZMod p) H (fun x : S => (ρ x).asModule) t ?_ ?_).2
  · intro x
    rw [(ρ x).asModuleEquiv.finrank_eq]
    simp
  · rintro x y ⟨e⟩
    let v := (ρ x).asModuleEquiv.symm.trans ((e.restrictScalars (ZMod p)).trans (ρ y).asModuleEquiv)
    have comm (h : H) (z : Fin t → ZMod p) : v (ρ x h z) = ρ y h (v z) := by
      apply (ρ y).asModuleEquiv.symm.injective
      rw [(ρ y).asModuleEquiv_symm_map_rho]
      exact (congrArg e ((ρ x).asModuleEquiv_symm_map_rho h z)).trans (e.map_smul _ _)
    let T := LinearMap.toMatrixAlgEquiv' v.toLinearMap
    have isT : IsUnit T := LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr v.bijective)
    have intertwines (h : H) : (red y h)*T = T*(red x h) := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_mul, map_mul, Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
      exact LinearMap.ext fun z => (comm h z).symm
    have cop : ¬ p ∣ Fintype.card H := by
      rw [Fintype.card_eq_nat_card]
      exact fun h => (NeZero.ne (Nat.card H : ZMod p)) ((ZMod.natCast_eq_zero_iff ..).mpr h)
    obtain ⟨U, hU, _, lift⟩ := prime_power_intertwiner hn cop (M x) (M y) T isT intertwines
    let L := Matrix.toLinAlgEquiv' U
    let f := (LinearEquiv.ofBijective L ((Module.End.isUnit_iff _).mp
      (Matrix.isUnit_toLin'_iff.mpr hU))).toAddEquiv.toMultiplicative
    have equivariant (h : H) : (a x h).trans f = f.trans (a y h) := by
      have eq := congrArg Matrix.toLinAlgEquiv' (lift h)
      rw [map_mul, map_mul] at eq
      change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (integral y h)) * L =
        L * Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv' (integral x h)) at eq
      rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv', Matrix.toLinAlgEquiv'_toMatrixAlgEquiv'] at eq
      apply DFunLike.ext'
      funext z
      exact (DFunLike.congr_fun eq (z : V)).symm
    let mid := SemidirectProduct.congr f (MulEquiv.refl H) equivariant
    apply Subtype.ext
    rw [← rep x, ← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩

/-- For a prime-power coordinate group every coprime action is allowed.
For other coordinate orders we count actions admitting diagonal coordinates. -/
theorem homocyclic_or_diagonal_hall_bound (C : FiniteGrp.{0}) [IsCyclic C] (t l r : ℕ)
    (hl : 0 < l) (cop : l.Coprime (Nat.card C^t)) (hr : Nat.card C^t*l < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
          ((IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}).ncard ≤
      2^(r*r) * ∏ b ∈ (Nat.card C^t*l).primeFactors, g (b^(Nat.card C^t*l).factorization b) := by
  classical
  let k := Nat.card C^t
  have hk : 0 < k := pow_pos Nat.card_pos _
  let O := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {H : FiniteGrp.{0} | Nat.card H = l ∧ Group.IsSolvable H ∧ Group.IsNilpotent H}
  let K (x : O) : FiniteGrp.{0} := x.property.choose
  have rep (x : O) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = x.val :=
    x.property.choose_spec.2
  have order (x : O) : Nat.card (K x) = l := x.property.choose_spec.1.1
  let _ : Finite O := ((finite_classes l).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let _ := Fintype.ofFinite O
  let S (H : FiniteGrp.{0}) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (χ : Fin t → H →* MulAut C) (a : H →* MulAut (Fin t → C)),
      ((IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct (Fin t → C) H a)}
  have finite (x : O) : (S (K x)).Finite := (finite_classes (k*l)).subset (Set.image_mono (by
    rintro G ⟨χ,a,_,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by simp [SemidirectProduct.card, Nat.card_fun, k, order])))
  have bound (x : O) : (S (K x)).ncard ≤ 2^(r*r) := by
    by_cases hp : IsPrimePow (Nat.card C) ∧ (Nat.card C).Coprime (Nat.card (K x))
    · obtain ⟨p,n,hpprime,hn,heq⟩ := (isPrimePow_nat_iff _).mp hp.1
      let _ : Fact p.Prime := ⟨hpprime⟩
      let _ : NeZero (p^n) := ⟨pow_ne_zero _ hpprime.ne_zero⟩
      have copP := hp.2.coprime_dvd_left (heq ▸ dvd_pow_self p hn.ne')
      let _ : NeZero (Nat.card (K x) : ZMod p) := ⟨fun h =>
        (hpprime.coprime_iff_not_dvd.mp copP) ((ZMod.natCast_eq_zero_iff ..).mp h)⟩
      let u : C ≃* Multiplicative (ZMod (p^n)) := mulEquivOfCyclicCardEq (heq.symm.trans (Nat.card_zmod _).symm)
      let tag : (Fin t → Multiplicative (ZMod (p^n))) ≃* Multiplicative (Fin t → ZMod (p^n)) :=
        { Equiv.refl _ with map_mul' := fun _ _ => rfl }
      let f := (MulEquiv.piCongrRight fun _ : Fin t => u).trans tag
      apply le_trans _ (le_trans (homocyclic_kernel_classes p n t hn (K x)) ?_)
      · apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono (by
          rintro G ⟨a,⟨e⟩⟩
          exact (Nat.card_congr e.toEquiv).trans (by
            rw [SemidirectProduct.card, ← Nat.card_congr f.toEquiv, Nat.card_fun, Nat.card_fin, order]))))
        rintro _ ⟨G, ⟨_,a,_,⟨e⟩⟩,rfl⟩
        exact ⟨G, ⟨_, ⟨e.trans (SemidirectProduct.congr' f (MulEquiv.refl (K x)))⟩⟩, rfl⟩
      · have ht : t ≤ r := by
          have hpow : 2^t < 2^r := (Nat.pow_le_pow_left (by rw [← heq]; exact hpprime.two_le.trans (by simpa using Nat.pow_le_pow_right hpprime.pos hn)) t).trans_lt
            ((Nat.le_mul_of_pos_right k hl).trans_lt hr)
          by_contra! bad
          exact hpow.not_ge (Nat.pow_le_pow_right (by decide) bad.le)
        have hlr := (Nat.le_mul_of_pos_left l hk).trans_lt hr
        rw [order, pow_mul]
        exact (Nat.pow_le_pow_left (show l+1 ≤ 2^r from hlr) _).trans
          (Nat.pow_le_pow_right (by positivity) ht)
    apply le_trans _ (le_trans (diagonal_class_bound C (K x) t) ?_)
    · apply Set.ncard_le_ncard _ ((finite_classes (k*l)).subset (Set.image_mono (by
        rintro G ⟨_,a,_,⟨e⟩⟩
        exact (Nat.card_congr e.toEquiv).trans (by simp [SemidirectProduct.card, Nat.card_fun, k, order]))))
      rintro _ ⟨G, ⟨χ,a,alt,e⟩,rfl⟩
      exact ⟨G, ⟨χ,a,alt.resolve_left hp,e⟩,rfl⟩
    apply (min_le_left ..).trans
    let _ : Finite (MulAut C) := Finite.of_injective (fun a : MulAut C => (a : C → C))
      (fun _ _ h => DFunLike.ext' h)
    have h := hom_count (K x) (MulAut C)
    rw [IsCyclic.card_mulAut C, order] at h
    have hlr : l < 2^r := (Nat.le_mul_of_pos_left l hk).trans_lt hr
    calc
      _ ≤ ((Nat.card C)^(Nat.log 2 l))^t :=
        Nat.pow_le_pow_left (h.trans (Nat.pow_le_pow_left (Nat.totient_le _) _)) _
      _ = k^(Nat.log 2 l) := by dsimp [k]; rw [← pow_mul, Nat.mul_comm, pow_mul]
      _ ≤ (2^r)^(Nat.log 2 l) := Nat.pow_le_pow_left ((Nat.le_mul_of_pos_right k hl).trans hr.le) _
      _ ≤ (2^r)^r := Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hl.ne' hlr).le
      _ = _ := (pow_mul ..).symm
  have sub : l.primeFactors ⊆ (k*l).primeFactors := by
    rw [Nat.primeFactors_mul hk.ne' hl.ne']
    exact Finset.subset_union_right
  have parts : O.ncard ≤ ∏ b ∈ (k*l).primeFactors, g (b^(k*l).factorization b) := by
    apply (nilpotent_bound l).trans
    calc
      _ = ∏ b ∈ l.primeFactors, g (b^(k*l).factorization b) := by
        apply Finset.prod_congr rfl
        intro b hb
        have nd : ¬ b ∣ k := fun hh => (Nat.prime_of_mem_primeFactors hb).not_dvd_one
          (cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hb) hh)
        rw [Nat.factorization_mul hk.ne' hl.ne', Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd nd, zero_add]
      _ ≤ _ := Finset.prod_le_prod_of_subset_of_one_le' sub fun b hb _ =>
        positive_count (pow_pos (Nat.prime_of_mem_primeFactors hb).pos _)
  apply le_trans (Set.ncard_le_ncard (t := ⋃ x : O, S (K x)) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G, ⟨H, hH, hs, hn, χ, a, diag, ⟨e⟩⟩, rfl⟩
    let x : O := ⟨Quotient.mk _ H, H, ⟨hH, hs, hn⟩, rfl⟩
    let u : K x ≃* H := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact (rep x)))).groupIsoToMulEquiv
    let mid := SemidirectProduct.congr (φ₁ := a) (φ₂ := a.comp u.toMonoidHom) (MulEquiv.refl _) u.symm
      (fun h => by ext v; simp)
    exact Set.mem_iUnion.mpr ⟨x, G, ⟨fun j => (χ j).comp u.toMonoidHom, a.comp u.toMonoidHom,
      diag.imp (fun h => ⟨h.1, by simpa [order, hH] using h.2⟩) (fun hdiag h v j => hdiag (u h) v j), ⟨e.trans mid⟩⟩, rfl⟩
  · calc
      _ ≤ ∑ x : O, (S (K x)).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : O, 2^(r*r) := Finset.sum_le_sum fun x _ => bound x
      _ = 2^(r*r)*O.ncard := by simp [← Nat.card_eq_fintype_card, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ parts

/-- A coprime semidirect product with nontrivial nilpotent kernel has a normal
nilpotent Hall subgroup, also after transport to an isomorphic group. -/
lemma semidirect_nilpotent_hall_witness {G K H : Type*} [Group G] [Group K] [Group H]
    [Finite G] [Finite K] [Finite H] [Group.IsNilpotent K] (a : H →* MulAut K)
    (e : G ≃* K ⋊[a] H) (big : 1 < Nat.card K) (cop : (Nat.card K).Coprime (Nat.card H)) :
    ∃ N : Subgroup G, N.Normal ∧ Group.IsNilpotent N ∧ 1 < Nat.card N ∧
      (Nat.card N).Coprime N.index := by
  let π := (SemidirectProduct.rightHom : K ⋊[a] H →* H).comp e.toMonoidHom
  let f := e.symm.toMonoidHom.comp (SemidirectProduct.inl : K →* K ⋊[a] H)
  have ker : π.ker = f.range := by
    dsimp [π,f]
    rw [MonoidHom.ker_comp_mulEquiv,MonoidHom.range_comp,SemidirectProduct.range_inl_eq_ker_rightHom]
  have iso : K ≃* π.ker := (MonoidHom.ofInjective (f := f)
    (e.symm.injective.comp SemidirectProduct.inl_injective)).trans (MulEquiv.subgroupCongr ker.symm)
  have surj : Function.Surjective π := SemidirectProduct.rightHom_surjective.comp e.surjective
  have idx : π.ker.index = Nat.card H := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr surj,Subgroup.card_top]
  refine ⟨π.ker,inferInstance,Group.nilpotent_of_mulEquiv iso,?_,?_⟩
  · rwa [← Nat.card_congr iso.toEquiv]
  · rwa [← Nat.card_congr iso.toEquiv,idx]

/-- The homocyclic kernels in the earlier Hall-action estimate already give a
nontrivial normal nilpotent Hall subgroup, regardless of the chosen action. -/
lemma homocyclic_hall_witness (G H : FiniteGrp.{0}) (c t : ℕ) (ht : 0 < t)
    (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2))))
    (e : G ≃* SemidirectProduct _ H a) (cop : (Nat.card H).Coprime ((c+2)^t)) :
    ∃ N : Subgroup G, N.Normal ∧ Group.IsNilpotent N ∧ 1 < Nat.card N ∧
      (Nat.card N).Coprime N.index := by
  have card : Nat.card (Fin t → Multiplicative (ZMod (c+2))) = (c+2)^t := by
    rw [Nat.card_fun,Nat.card_fin]
    exact congrArg (· ^ t) (Nat.card_zmod (c+2))
  apply semidirect_nilpotent_hall_witness a e
  · rw [card]
    exact one_lt_pow₀ (by omega) ht.ne'
  · rwa [card,Nat.coprime_comm]

/-- Count all homocyclic prime-power Hall kernels with nilpotent complement together with the diagonal family. -/
theorem homocyclic_or_diagonal_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ (∃ c t : ℕ, 0 < t ∧ ∃ H : FiniteGrp.{0}, Group.IsSolvable H ∧ Group.IsNilpotent H ∧
        (Nat.card H).Coprime ((c+2)^t) ∧
        ∃ (χ : Fin t → H →* MulAut (Multiplicative (ZMod (c+2))))
          (a : H →* MulAut (Fin t → Multiplicative (ZMod (c+2)))),
          ((IsPrimePow (c+2) ∧ (c+2).Coprime (Nat.card H)) ∨ (∀ h v i, a h v i = χ i h (v i))) ∧ Nonempty (G ≃* SemidirectProduct _ H a))}).ncard ≤
      2^((r+1)^2) * ∏ b ∈ q.primeFactors, g (b^q.factorization b) := by
  classical
  let J := Fin (q+1) × Fin (q+1)
  let k (j : J) := (j.1.val+2)^j.2.val
  let I := {j : J // 0 < q/k j ∧ (q/k j).Coprime (k j) ∧ k j*(q/k j) = q}
  let C (j : J) := FiniteGrp.of (Multiplicative (ZMod (j.1.val+2)))
  let (j : J) : IsCyclic (C j) := inferInstanceAs (IsCyclic (Multiplicative (ZMod (j.1.val+2))))
  have card (j : J) : Nat.card (C j) = j.1.val+2 := by
    change Nat.card (ZMod (j.1.val+2)) = _
    exact Nat.card_zmod _
  let S (i : I) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ H : FiniteGrp.{0}, Nat.card H = q/k i.val ∧ Group.IsSolvable H ∧ Group.IsNilpotent H ∧
      ∃ (χ : Fin i.val.2.val → H →* MulAut (C i.val)) (a : H →* MulAut (Fin i.val.2.val → C i.val)),
        ((IsPrimePow (i.val.1.val+2) ∧ (i.val.1.val+2).Coprime (Nat.card H)) ∨ (∀ h v j, a h v j = χ j h (v j))) ∧ Nonempty (G ≃* SemidirectProduct _ H a)}
  let L := ∏ b ∈ q.primeFactors, g (b^q.factorization b)
  have cardpow (i : I) : Nat.card (C i.val)^i.val.2.val = k i.val := by rw [card]
  have bound (i : I) : (S i).ncard ≤ 2^(r*r)*L := by
    have eq := (congrArg (· * (q/k i.val)) (cardpow i)).trans i.property.2.2
    have h := homocyclic_or_diagonal_hall_bound (C i.val) i.val.2.val (q/k i.val) r i.property.1
      ((cardpow i).symm ▸ i.property.2.1) (eq.trans_lt hr)
    rw [eq] at h
    simpa only [card] using h
  have finite (i : I) : (S i).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨H,hH,_,_,_,a,_,⟨e⟩⟩
    exact (Nat.card_congr e.toEquiv).trans (by
      rw [SemidirectProduct.card, Nat.card_fun, Nat.card_fin, cardpow, hH]; exact i.property.2.2)))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, S i) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G, ⟨hg,c,t,ht,H,hs,hn,cop,χ,a,diag,⟨e⟩⟩, rfl⟩
    have eq : (c+2)^t * Nat.card H = q := by
      have h := (Nat.card_congr e.toEquiv).symm.trans hg
      simpa [SemidirectProduct.card, Nat.card_fun, Nat.card_zmod] using h
    have hpow : 0 < (c+2)^t := by positivity
    have leq := (Nat.le_mul_of_pos_right ((c+2)^t) Nat.card_pos).trans eq.le
    have ct : c+2 ≤ (c+2)^t := by simpa using Nat.pow_le_pow_right (by omega : 0 < c+2) ht
    have tt : t < (c+2)^t := Nat.lt_pow_self (by omega)
    let j : J := (⟨c, by omega⟩, ⟨t, by omega⟩)
    have div : q/k j = Nat.card H := by change q/(c+2)^t = _; rw [← eq, Nat.mul_div_cancel_left _ hpow]
    let i : I := ⟨j, div.symm ▸ Nat.card_pos, div.symm ▸ cop, div.symm ▸ eq⟩
    exact Set.mem_iUnion.mpr ⟨i, G, ⟨H,div.symm,hs,hn,χ,a,diag,⟨e⟩⟩,rfl⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^(r+r) := by
      apply (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      simpa [J, Nat.card_prod, pow_add] using Nat.mul_le_mul (show q+1 ≤ 2^r from hr) hr
    calc
      _ ≤ ∑ i : I, (S i).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(r*r)*L := Finset.sum_le_sum fun i _ => bound i
      _ = Nat.card I * (2^(r*r)*L) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^(r+r) * (2^(r*r)*L) := Nat.mul_le_mul_right _ ni
      _ = 2^((r+r)+r*r)*L := by rw [pow_add (2:ℕ) (r+r) (r*r)]; ac_rfl
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by nlinarith : (r+r)+r*r ≤ (r+1)^2))

lemma surjective_of_surjective_mod_p {A : Type*} [AddCommGroup A] {p n : ℕ}
    (f : A →+ A) (tors : ∀ x : A, (p^n) • x = 0)
    (red : ∀ x : A, ∃ y z : A, x = f y + p • z) : Function.Surjective f := by
  have step (k : ℕ) (x : A) : ∃ y z : A, x = f y + (p^k) • z := by
    induction k with
    | zero => exact ⟨0, x, by simp⟩
    | succ k ih =>
      obtain ⟨y,z,h⟩ := ih
      obtain ⟨u,v,hz⟩ := red z
      exact ⟨y + (p^k) • u, v, by rw [h, hz, smul_add, map_add, map_nsmul,
        pow_succ, mul_smul, add_assoc]⟩
  intro x
  obtain ⟨y,z,h⟩ := step n x
  exact ⟨y, by simpa [tors] using h.symm⟩

universe u
/-- Bound the number of representations on one equal-exponent block. -/
lemma matrix_code {p : ℕ} [Fact p.Prime] {H J : Type} [Group H] [Finite H] [NeZero (Nat.card H : ZMod p)]
    [Fintype J] [DecidableEq J] {S : Type u} (a : S → H →* Matrix J J (ZMod p)) :
    ∃ (C : Type u) (_ : Finite C) (code : S → C), Nat.card C ≤ (Nat.card H+1)^Fintype.card J ∧
      ∀ i j, code i = code j → ∃ T : Matrix J J (ZMod p), IsUnit T ∧
        ∀ h, a j h * T = T * a i h := by
  classical
  let ρ (i : S) : Representation (ZMod p) H (J → ZMod p) := Matrix.toLinAlgEquiv'.toMonoidHom.comp (a i)
  let R := MonoidAlgebra (ZMod p) H
  let s : Setoid S := ⟨fun i j => Nonempty ((ρ i).asModule ≃ₗ[R] (ρ j).asModule),
    ⟨fun _ => ⟨LinearEquiv.refl _ _⟩,fun e => ⟨e.some.symm⟩,fun e f => ⟨e.some.trans f.some⟩⟩⟩
  let C := Quotient s
  have bound := coprime_module_family_bound (ZMod p) H (fun c : C => (ρ c.out).asModule) (Fintype.card J)
    (fun c => by rw [(ρ c.out).asModuleEquiv.finrank_eq]; simp) (fun i j h => by
      rw [← Quotient.out_eq i, ← Quotient.out_eq j]; exact Quotient.sound h)
  refine ⟨C,bound.1,Quotient.mk s,bound.2,?_⟩
  intro i j eq
  obtain ⟨e⟩ := Quotient.exact eq
  let v := (ρ i).asModuleEquiv.symm.trans ((e.restrictScalars (ZMod p)).trans (ρ j).asModuleEquiv)
  refine ⟨LinearMap.toMatrixAlgEquiv' v.toLinearMap,
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr v.bijective),?_⟩
  intro h
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_mul,map_mul,Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  apply LinearMap.ext
  intro x
  change ρ j h (v x) = v (ρ i h x)
  apply (ρ j).asModuleEquiv.symm.injective
  rw [(ρ j).asModuleEquiv_symm_map_rho]
  exact ((congrArg e ((ρ i).asModuleEquiv_symm_map_rho h x)).trans (e.map_smul _ _)).symm

/-- Equivalences of the diagonal blocks lift simultaneously for any cyclic exponent profile. -/
theorem profile_family_count {p : ℕ} [Fact p.Prime] {I H : Type} [Fintype I] [DecidableEq I] [Group H] [Fintype H]
    (e : I → ℕ) (cop : ¬ p ∣ Fintype.card H) {S : Type u}
    (a : S → H →* AddMonoid.End (((i : I) → ZMod (p^(e i+1)))))
    (sep : ∀ i j, (∃ U : ((i : I) → ZMod (p^(e i+1))) ≃+ ((i : I) → ZMod (p^(e i+1))), ∀ h x, a j h (U x) = U (a i h x)) → i = j) :
    Finite S ∧ Nat.card S ≤ (Nat.card H+1)^Fintype.card I := by
  classical
  let V := (i : I) → ZMod (p^(e i+1))
  let π (k : ℕ) := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero k)) (ZMod p)
  let red (x : V) (i : I) := π (e i) (x i)
  let mat (f : AddMonoid.End (V)) : Matrix I I (ZMod p) :=
    fun i j => red (f (Pi.single j 1)) i
  have action (f : AddMonoid.End (V)) (x : V) :
      red (f x) = (mat f).mulVec (red x) := by
    let (i : I) : NeZero (p^(e i+1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    have decomp : ∑ j, (x j).val • (Pi.single j 1 : V) = x := by
      funext i
      rw [Finset.sum_apply]
      change ∑ j, (x j).val • ((Pi.single j 1 : V) i) = _
      rw [Finset.sum_eq_single i]
      · simp [nsmul_eq_mul]
      · intro j _ ne; rw [Pi.single_eq_of_ne ne.symm,smul_zero]
      · simp
    have h := congrArg f decomp
    rw [map_sum] at h
    simp only [map_nsmul] at h
    funext i
    conv_lhs => rw [← h]
    change π (e i) ((∑ j, (x j).val • f (Pi.single j 1)) i) = _
    rw [Finset.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    change π (e i) ((x j).val • (f (Pi.single j 1) i)) = _ * _
    rw [map_nsmul,nsmul_eq_mul,mul_comm]
    congr 1
    change ((x j).val : ZMod p) = π (e j) (x j)
    rw [← map_natCast (π (e j)),ZMod.natCast_zmod_val]
  let reduction : AddMonoid.End (V) →+* Matrix I I (ZMod p) :=
      { toFun := mat
        map_zero' := by ext i j; exact map_zero (π (e i))
        map_one' := by
          ext i j
          change π (e i) ((Pi.single j 1 : V) i) = _
          by_cases h : i = j
          · subst j; simp [π]
          · simp [π,h]
        map_add' f g := by ext i j; exact map_add (π (e i)) _ _
        map_mul' f g := by
          ext i j
          exact congrFun (action f (g (Pi.single j 1))) i }
  have triangular (f : AddMonoid.End (V)) : (mat f).BlockTriangular e := by
    intro i j hij
    have hz : p^(e j+1) • (Pi.single j 1 : V) = 0 := by
      funext t
      change p^(e j+1) • ((Pi.single j 1 : V) t) = 0
      by_cases h : t = j
      · subst t; simp only [Pi.single_eq_same,nsmul_eq_mul,ZMod.natCast_self,zero_mul]
      · rw [Pi.single_eq_of_ne h,smul_zero]
    let y := f (Pi.single j 1) i
    have h := f.map_nsmul (p^(e j+1)) (Pi.single j 1)
    rw [hz,f.map_zero] at h
    have hy : 0 = p^(e j+1) • y := congrFun h i
    let _ : NeZero (p^(e i+1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
    have hv := ZMod.natCast_zmod_val y
    rw [nsmul_eq_mul, ← hv, ← Nat.cast_mul, eq_comm, ZMod.natCast_eq_zero_iff] at hy
    have hd := Nat.dvd_trans (Nat.pow_dvd_pow p (show e j+1+1 ≤ e i+1 by omega)) hy
    rw [pow_succ, mul_comm (p^(e j+1)) p] at hd
    change π (e i) y = 0
    rw [← hv,map_natCast,ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mul_dvd_mul_left (pow_pos (Fact.out : p.Prime).pos _) (by simpa only [mul_comm p (p^(e j+1))] using hd)
  let block (k : ℕ) : AddMonoid.End (V) →+* Matrix {i // e i = k} {i // e i = k} (ZMod p) :=
      { toFun f := (mat f).toSquareBlock e k
        map_one' := by change ((reduction) 1).toSquareBlock e k = _; rw [map_one]; exact Matrix.toBlock_one_self _
        map_zero' := by change ((reduction) 0).toSquareBlock e k = _; rw [map_zero]; rfl
        map_add' f g := by change ((reduction) (f+g)).toSquareBlock e k = _; rw [map_add]; rfl
        map_mul' f g := by
          change ((reduction) (f*g)).toSquareBlock e k = _
          rw [map_mul]
          ext i j
          let F (t : I) := mat f i.val t * mat g t j.val
          change ∑ t, F t = ∑ t : {i // e i = k}, F t.val
          let s := Finset.univ.filter fun t => e t = k
          rw [← s.sum_subtype (by simp [s]) F]
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro t _ ht
          have ne : e t ≠ k := by simpa [s] using ht
          rcases lt_or_gt_of_ne ne with h|h
          · have z := triangular f (i := i.val) (j := t) (i.property.symm ▸ h)
            simp [F,z]
          · have z := triangular g (i := t) (j := j.val) (j.property.symm ▸ h)
            simp [F,z] }
  have onto_of_blocks (f : AddMonoid.End (V)) (units : ∀ k, IsUnit (block k f)) :
      Function.Surjective f := by
    have unitM : IsUnit (mat f) := by
      apply (Matrix.isUnit_iff_isUnit_det _).mpr
      rw [(triangular f).det]
      apply isUnit_iff_ne_zero.mpr
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact IsUnit.ne_zero <| (Matrix.isUnit_iff_isUnit_det _).mp (units k)
    let n := Finset.univ.sup (fun i => e i+1)
    apply surjective_of_surjective_mod_p (p := p) (n := n) f
    · intro x
      funext i
      have hi : e i+1 ≤ n := Finset.le_sup (f := fun j => e j+1) (Finset.mem_univ i)
      change p^n • x i = 0
      rw [nsmul_eq_mul]
      have z : (↑(p^n) : ZMod (p^(e i+1))) = 0 :=
        (ZMod.natCast_eq_zero_iff ..).mpr (Nat.pow_dvd_pow p hi)
      rw [z,zero_mul]
    intro x
    obtain ⟨v,hv⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr unitM (red x)
    let y : V := fun i => (v i).val
    have hy : red y = v := by
      funext i; change π (e i) (↑(v i).val) = v i
      rw [map_natCast,ZMod.natCast_zmod_val]
    have hxy : red (f y) = red x := by rw [action,hy,hv]
    have term (i : I) : ∃ z : ZMod (p^(e i+1)), x i - f y i = p • z := by
      let _ : NeZero (p^(e i+1)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      have h0 : π (e i) (x i - f y i) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr (congrFun hxy i).symm
      have hval := ZMod.natCast_zmod_val (x i - f y i)
      rw [← hval,map_natCast,ZMod.natCast_eq_zero_iff] at h0
      obtain ⟨k,hk⟩ := h0
      exact ⟨k,by rw [nsmul_eq_mul,← Nat.cast_mul,← hk,hval]⟩
    choose z hz using term
    refine ⟨y,z,funext fun i => ?_⟩
    change x i = f y i + p • z i
    rw [← hz]; abel
  have lift_blocks (T : (k : ℕ) → Matrix {i // e i = k} {i // e i = k} (ZMod p)) :
      ∃ L : AddMonoid.End (V), ∀ k, block k L = T k := by
    classical
    let coeff (i : I) (j : {t // e t = e i}) : ZMod (p^(e i+1)) := (T (e i) ⟨i,rfl⟩ j).val
    let cast (i : I) (j : {t // e t = e i}) := ZMod.castHom
      (show p^(e i+1) ∣ p^(e j.val+1) by rw [j.property]) (ZMod (p^(e i+1)))
    let L : V →+ V :=
      { toFun := fun x i => ∑ j, coeff i j * cast i j (x j.val)
        map_zero' := by funext i; change ∑ j, coeff i j * cast i j 0 = 0; simp
        map_add' x y := by funext i; change ∑ j, coeff i j * cast i j (_ + _) = _; simp [mul_add,Finset.sum_add_distrib,V] }
    refine ⟨L,fun k => ?_⟩
    ext i j
    obtain ⟨i,hi⟩ := i
    subst k
    let f (t : {t // e t = e i}) := coeff i t * cast i t ((Pi.single j.val 1 : V) t.val)
    change π (e i) (∑ t, f t) = _
    rw [Finset.sum_eq_single j]
    · change π (e i) (coeff i j * cast i j ((Pi.single j.val 1 : V) j.val)) = _
      rw [Pi.single_eq_same,map_one,mul_one]; change π (e i) (↑(T (e i) ⟨i,rfl⟩ j).val) = _
      rw [map_natCast,ZMod.natCast_zmod_val]
    · intro t _ ne
      have h : t.val ≠ j.val := fun eq => ne (Subtype.ext eq)
      simp [f,Pi.single_eq_of_ne h]
    · simp
  have conjugate (cop : ¬ p ∣ Fintype.card H)
      (a b : H →* AddMonoid.End (V))
      (T : (k : ℕ) → Matrix {i // e i = k} {i // e i = k} (ZMod p))
      (unit : ∀ k, IsUnit (T k))
      (inter : ∀ k h, block k (b h) * T k = T k * block k (a h)) :
      ∃ U : V ≃+ V, ∀ h x, b h (U x) = U (a h x) := by
    classical
    obtain ⟨L,hL⟩ := lift_blocks T
    let U := ∑ h : H, b h * L * a h⁻¹
    have sur : Function.Surjective U := by
      apply onto_of_blocks
      intro k
      have term (h : H) : block k (b h * L * a h⁻¹) = T k := by
        rw [map_mul,map_mul,hL,inter,mul_assoc,← map_mul,← map_mul,mul_inv_cancel,map_one,map_one,mul_one]
      change IsUnit (block k (∑ h : H, b h * L * a h⁻¹))
      simp only [map_sum,term,Finset.sum_const,Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
      rw [Algebra.smul_def]
      exact ((isUnit_iff_ne_zero.mpr (fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h))).map (algebraMap (ZMod p) _)).mul (unit k)
    refine ⟨AddEquiv.ofBijective U ⟨Finite.injective_iff_surjective.mpr sur,sur⟩,?_⟩
    exact fun h x => DFunLike.congr_fun (average_intertwines a b L h) x
  let _ : NeZero (Nat.card H : ZMod p) := ⟨by rw [← Fintype.card_eq_nat_card]; exact fun h => cop ((ZMod.natCast_eq_zero_iff ..).mp h)⟩
  let K := Finset.univ.image e
  choose C fin code bound transport using fun k : K => matrix_code (fun i => (block k.val).toMonoidHom.comp (a i))
  have inj : Function.Injective (fun i k => code k i) := by
    intro i j eq
    apply sep
    have each (k : ℕ) : ∃ T : Matrix {i // e i = k} {i // e i = k} (ZMod p), IsUnit T ∧
        ∀ h, block k (a j h) * T = T * block k (a i h) := by
      by_cases hk : k ∈ K
      · exact transport ⟨k,hk⟩ i j (congrFun eq ⟨k,hk⟩)
      · have _ : IsEmpty {i // e i = k} := ⟨fun i => hk (Finset.mem_image.mpr ⟨i.val,Finset.mem_univ _,i.property⟩)⟩
        exact ⟨1,isUnit_one,fun _ => Subsingleton.elim _ _⟩
    choose T unit inter using each
    exact conjugate cop _ _ T unit inter
  refine ⟨Finite.of_injective _ inj,(Nat.card_le_card_of_injective _ inj).trans ?_⟩
  rw [Nat.card_pi]
  apply (Finset.prod_le_prod' (fun k _ => bound k)).trans
  rw [Finset.prod_pow_eq_pow_sum]
  have equiv : ((k : K) × {i // e i = k.val}) ≃ I :=
    { toFun := fun x => x.2.val
      invFun := fun i => ⟨⟨e i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩,i,rfl⟩
      left_inv := by rintro ⟨⟨k,hk⟩,i,hi⟩; change e i = k at hi; subst k; rfl
      right_inv := fun _ => rfl }
  have h := Fintype.card_congr equiv
  rw [Fintype.card_sigma] at h
  exact (congrArg ((Nat.card H+1)^·) h).le

/-- Count middle groups for one arbitrary exponent profile and fixed coprime complement. -/
theorem arbitrary_profile_classes {I : Type} [Fintype I] [DecidableEq I] (p : ℕ) (e : I → ℕ) [Fact p.Prime] (H : FiniteGrp.{0})
    (cop : ¬ p ∣ Nat.card H) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut (Multiplicative (((i : I) → ZMod (p^(e i+1))))),
        Nonempty (G ≃* SemidirectProduct _ H a)}).ncard ≤ (Nat.card H+1)^Fintype.card I := by
  classical
  let _ := Fintype.ofFinite H
  let K := Multiplicative (((i : I) → ZMod (p^(e i+1))))
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let act (x : S) : H →* AddMonoid.End (((i : I) → ZMod (p^(e i+1)))) :=
    { toFun := fun h => AddMonoidHom.toMultiplicative.symm ((a x h).toMonoidHom)
      map_one' := by apply DFunLike.ext'; funext z; change (a x 1) z = z; rw [map_one]; rfl
      map_mul' := by intro h j; apply DFunLike.ext'; funext z; change (a x (h*j)) z = (a x h) ((a x j) z); rw [map_mul]; rfl }
  change Nat.card S ≤ _
  rw [← Fintype.card_eq_nat_card (α := H)] at cop
  apply (profile_family_count e cop act ?_).2
  rintro x y ⟨U,hU⟩
  let f := U.toMultiplicative
  have comm (h : H) : (a x h).trans f = f.trans (a y h) := by
    apply DFunLike.ext'
    funext z
    exact (hU h z).symm
  let mid := SemidirectProduct.congr f (MulEquiv.refl H) comm
  apply Subtype.ext
  rw [← rep x, ← rep y]
  exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩

/-- Encode actions on one primary component up to an equivariant kernel isomorphism. -/
lemma prime_action_code (K H : FiniteGrp.{0}) [IsMulCommutative K] {p s : ℕ} [Fact p.Prime]
    (hk : Nat.card K = p^s) (cop : ¬ p ∣ Nat.card H) :
    ∃ t, 2^t ≤ Nat.card K ∧ ∃ (C : Type) (_ : Finite C) (code : (H →* MulAut K) → C),
      Nat.card C ≤ (Nat.card H+1)^t ∧ ∀ a b, code a = code b →
        ∃ U : K ≃* K, ∀ h x, b h (U x) = U (a h x) := by
  classical
  let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := IsMulCommutative.is_comm.comm }
  obtain ⟨I,fi,n,hn,⟨u⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite K
  have order : Nat.card K = ∏ i, n i := by
    rw [Nat.card_congr u.toEquiv,Nat.card_pi]
    exact Finset.prod_congr rfl fun i _ => Nat.card_zmod _
  have powers (i : I) : ∃ t, n i = p^(t+1) := by
    have dvd : n i ∣ p^s := by rw [← hk,order]; exact Finset.dvd_prod_of_mem n (Finset.mem_univ i)
    obtain ⟨t,_,ht⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp dvd
    cases t with
    | zero => have := hn i; simp_all
    | succ t => exact ⟨t,ht⟩
  choose e he using powers
  let tag : ((i : I) → Multiplicative (ZMod (p^(e i+1)))) ≃* Multiplicative (((i : I) → ZMod (p^(e i+1)))) :=
    { Equiv.refl _ with map_mul' := fun _ _ => rfl }
  let v := (u.trans (MulEquiv.piCongrRight fun i => ((ZMod.ringEquivCongr (he i)).toAddEquiv).toMultiplicative)).trans tag
  let V := (i : I) → ZMod (p^(e i+1))
  have size : 2^Fintype.card I ≤ Nat.card K := by
    rw [order,← Finset.card_univ,← Finset.prod_const]
    exact Finset.prod_le_prod' fun i _ => hn i
  let R : Setoid (H →* MulAut K) :=
    { r := fun a b => ∃ U : K ≃* K, ∀ h x, b h (U x) = U (a h x)
      iseqv := ⟨fun _ => ⟨MulEquiv.refl _,fun _ _ => rfl⟩,
        by rintro a b ⟨u,hu⟩; exact ⟨u.symm, fun h x => u.injective (by simp [← hu])⟩,
        by rintro a b c ⟨u,hu⟩ ⟨w,hw⟩; exact ⟨u.trans w,fun h x => (hw h (u x)).trans (congrArg w (hu h x))⟩⟩ }
  let C := Quotient R
  let a (i : C) := (MulAut.congr v).toMonoidHom.comp i.out
  let act (i : C) : H →* AddMonoid.End V :=
    { toFun := fun h => AddMonoidHom.toMultiplicative.symm ((a i h).toMonoidHom)
      map_one' := by apply DFunLike.ext'; funext z; change (a i 1) z = z; rw [map_one]; rfl
      map_mul' := by intro h j; apply DFunLike.ext'; funext z; change (a i (h*j)) z = (a i h) ((a i j) z); rw [map_mul]; rfl }
  let _ := Fintype.ofFinite H
  have bound := profile_family_count e (p := p) (by rwa [Fintype.card_eq_nat_card]) act (by
    rintro i j ⟨U,hU⟩
    rw [← Quotient.out_eq i,← Quotient.out_eq j]
    apply Quotient.sound
    let f := U.toMultiplicative
    refine ⟨v.trans (f.trans v.symm),fun h x => ?_⟩
    have eq := hU h (v x)
    change v (j.out h (v.symm (f (v x)))) = f (v (i.out h (v.symm (v x)))) at eq
    apply v.injective
    simpa [f] using eq)
  exact ⟨_,size,C,bound.1,Quotient.mk R,bound.2,fun _ _ h => Quotient.exact h⟩

lemma component_actions {I : Type} [Fintype I] [DecidableEq I] (P : I → Type)
    [∀ i, Group (P i)] [∀ i, Finite (P i)] (cop : Pairwise fun i j => (Nat.card (P i)).Coprime (Nat.card (P j))) :
    ∀ i, ∃ res : MulAut ((j : I) → P j) →* MulAut (P i), ∀ F x, res F (x i) = F x i := by
  classical
  intro i
  let single j := MonoidHom.mulSingle P j
  let pr := Pi.evalMonoidHom P i
  let diag (F : MulAut ((j : I) → P j)) := pr.comp (F.toMonoidHom.comp (single i))
  have apply_diag (F : MulAut ((j : I) → P j)) (x : ∀ j, P j) : F x i = diag F (x i) := by
    have on_single (j : I) (y : P j) :
        F (single j y) i = diag F ((single j y) i) := by
      by_cases e : j = i
      · subst j; simp [single,diag,pr]
      · let f := pr.comp (F.toMonoidHom.comp (single j))
        have h := Nat.dvd_gcd ((orderOf_map_dvd f y).trans (orderOf_dvd_natCard _))
          (orderOf_dvd_natCard (f y))
        rw [show (Nat.card (P j)).gcd (Nat.card (P i)) = 1 from cop e] at h
        have off := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one h)
        change F (Pi.mulSingle j y) i = 1 at off
        simpa [single,Pi.mulSingle_eq_of_ne (Ne.symm e)] using off
    have aux (s : Finset I) (y : ∀ j, P j) (hy : ∀ j ∉ s, y j = 1) :
        F y i = diag F (y i) := by
      induction s using Finset.induction_on generalizing y with
      | empty =>
        have ey : y = 1 := funext fun j => hy j (Finset.notMem_empty j)
        simp [ey]
      | @insert j s hj ih =>
        let z := Function.update y j 1
        have dz : y = single j (y j) * z := by
          funext k; by_cases ek : k = j
          · subst k; simp [single,z]
          · simp [single,z,ek]
        have hz (k : I) (hk : k ∉ s) : z k = 1 := by
          by_cases ek : k = j
          · subst k; simp [z]
          · simpa [z,ek] using hy k (by simp [ek,hk])
        calc
          F y i = F (single j (y j)) i * F z i := by
            conv_lhs => rw [dz,map_mul]
            rfl
          _ = diag F ((single j (y j)) i * z i) := by rw [map_mul,on_single,ih z hz]
          _ = diag F (y i) := congrArg (diag F) (congrFun dz.symm i)
    exact aux Finset.univ x (by simp)
  let aut (F : MulAut ((j : I) → P j)) : MulAut (P i) :=
    { diag F with
      invFun := diag F.symm
      left_inv := fun x => by
        change diag F.symm ((F (single i x)) i) = x
        rw [← apply_diag,F.symm_apply_apply]; exact Pi.mulSingle_eq_same i x
      right_inv := fun x => by
        change diag F ((F.symm (single i x)) i) = x
        rw [← apply_diag,F.apply_symm_apply]; exact Pi.mulSingle_eq_same i x }
  let res : MulAut ((j : I) → P j) →* MulAut (P i) :=
    { toFun := aut
      map_one' := by apply DFunLike.ext'; funext x; exact Pi.mulSingle_eq_same i x
      map_mul' F G := by
        apply DFunLike.ext'; funext x
        exact apply_diag F (G (single i x)) }
  exact ⟨res,fun F x => (apply_diag F x).symm⟩

lemma all_abelian_action_bound (K H : FiniteGrp.{0}) [IsMulCommutative K] {r : ℕ}
    (cop : (Nat.card K).Coprime (Nat.card H)) (hr : Nat.card K * Nat.card H < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}).ncard ≤ 2^(r*r) := by
  classical
  let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := IsMulCommutative.is_comm.comm }
  let I := ↥(Nat.card K).primeFactors
  let (i : I) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
  let P (i : I) : Sylow i.val K := default
  let v : K ≃* ((i : I) → P i) :=
    (Sylow.directProductOfNormal (G := K) fun _ => inferInstance).symm.trans (MulEquiv.piCongrRight fun i => by
      let _ := Sylow.unique_of_normal (P i) inferInstance
      exact MulEquiv.piUnique (fun Q : Sylow i.val K => Q))
  have disj : Pairwise fun i j => (Nat.card (P i)).Coprime (Nat.card (P j)) := by
    intro i j ne
    exact IsPGroup.coprime_card_of_ne i.val j.val (fun h => ne (Subtype.ext h)) _ _ (P i).isPGroup' (P j).isPGroup'
  choose res compat using component_actions (fun i => ↥(P i)) disj
  have nd (i : I) : ¬ i.val ∣ Nat.card H :=
    (Nat.prime_of_mem_primeFactors i.property).coprime_iff_not_dvd.mp
      (cop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors i.property))
  let (i : I) : IsMulCommutative (FiniteGrp.of (P i)) := ⟨⟨fun x y => @mul_comm (↥(P i)) (inferInstance : CommMagma (↥(P i))) x y⟩⟩
  choose t size C fin code bound inter using fun i : I => prime_action_code (FiniteGrp.of (P i)) H
    (P i).card_eq_multiplicity (nd i)
  have lim : ∑ i, t i ≤ r := by
    have sz : 2^(∑ i, t i) ≤ Nat.card K := by
      calc
        _ ≤ ∏ i, Nat.card (P i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_le_prod' fun i _ => size i
        _ = _ := (Nat.card_pi.symm.trans (Nat.card_congr v.toEquiv).symm)
    have hlt := sz.trans_lt ((Nat.le_mul_of_pos_right _ Nat.card_pos).trans_lt hr)
    by_contra! bad
    exact hlt.not_ge (Nat.pow_le_pow_right (by decide) bad.le)
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let act (x : S) := (MulAut.congr v).toMonoidHom.comp (a x)
  let parts (x : S) (i : I) := (res i).comp (act x)
  have inj : Function.Injective (fun x i => code i (parts x i)) := by
    intro x y eq
    choose U hU using fun i => inter i _ _ (congrFun eq i)
    let V (i : I) : ↥(P i) ≃* ↥(P i) := U i
    let f := v.trans ((MulEquiv.piCongrRight V).trans v.symm)
    have equivariant (h : H) : (a x h).trans f = f.trans (a y h) := by
      apply DFunLike.ext'; funext z
      apply v.injective
      change v (v.symm ((MulEquiv.piCongrRight V) (v ((a x h) z)))) =
        v ((a y h) (v.symm ((MulEquiv.piCongrRight V) (v z))))
      rw [v.apply_symm_apply]
      funext i
      have e := hU i h (v z i)
      change res i (act y h) (U i (v z i)) = U i (res i (act x h) (v z i)) at e
      rw [compat i (act x h) (v z)] at e
      have lhs := compat i (act y h) ((MulEquiv.piCongrRight V) (v z))
      have key := e.symm.trans lhs
      change V i (v ((a x h) (v.symm (v z))) i) = v ((a y h) (v.symm ((MulEquiv.piCongrRight V) (v z)))) i at key
      change V i (v ((a x h) z) i) = _
      simpa only [v.symm_apply_apply] using key
    let mid := SemidirectProduct.congr f (MulEquiv.refl H) equivariant
    apply Subtype.ext
    rw [← rep x,← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩
  change Nat.card S ≤ _
  apply (Nat.card_le_card_of_injective _ inj).trans
  rw [Nat.card_pi]
  apply (Finset.prod_le_prod' (fun i _ => bound i)).trans
  rw [Finset.prod_pow_eq_pow_sum,pow_mul]
  exact (Nat.pow_le_pow_left (Nat.succ_le_of_lt ((Nat.le_mul_of_pos_left _ Nat.card_pos).trans_lt hr)) _).trans
    (Nat.pow_le_pow_right (by positivity) lim)

/-- A prime-power group acting trivially on the Frattini quotient acts trivially
if its prime does not divide the order of the Frattini subgroup. -/
theorem trivial_action {G A : Type*} [Group G] [Finite G] [Group A] {l : ℕ}
    [Fact l.Prime] (ha : IsPGroup l A) (cop : ¬ l ∣ Nat.card (frattini G))
    (a : A →* MulAut G)
    (h : ∀ u x, QuotientGroup.mk' (frattini G) (a u x) = QuotientGroup.mk' (frattini G) x) :
    ∀ u x, a u x = x := by
  classical
  let f := QuotientGroup.mk' (frattini G)
  let S : Subgroup G := ⨅ u : A, (a u).toMonoidHom.eqLocus (MonoidHom.id G)
  have gen : S ⊔ frattini G = ⊤ := by
    apply top_unique
    intro x _
    let F := f ⁻¹' {f x}
    let _ : MulAction A F :=
      { smul := fun u y => ⟨a u y.val,(h u y.val).trans y.property⟩
        one_smul := fun y => Subtype.ext (by change a 1 y.val = y.val; rw [map_one]; rfl)
        mul_smul := fun u v y => Subtype.ext (by change a (u*v) y.val = a u (a v y.val); rw [map_mul]; rfl) }
    have sz : Nat.card F = Nat.card (frattini G) := by
      calc
        _ = Nat.card f.ker := Nat.card_congr (f.fiberEquivKer x)
        _ = _ := by rw [show f.ker = frattini G from QuotientGroup.ker_mk' _]
    obtain ⟨y,hy⟩ := ha.nonempty_fixed_point_of_prime_not_dvd_card F (sz ▸ cop)
    have ys : y.val ∈ S := Subgroup.mem_iInf.mpr fun u => congrArg Subtype.val (hy u)
    have eq : f x = f y.val := y.property.symm
    have div : x / y.val ∈ frattini G := QuotientGroup.eq_iff_div_mem.mp eq
    simpa using (S ⊔ frattini G).mul_mem ((le_sup_right : frattini G ≤ S ⊔ frattini G) div) ((le_sup_left : S ≤ S ⊔ frattini G) ys)
  have all := frattini_nongenerating gen
  intro u x
  exact Subgroup.mem_iInf.mp (show x ∈ S by rw [all]; trivial) u

/-- Any subgroup of automorphisms inducing the identity modulo Frattini is a p-group. -/
theorem kernel_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hg : IsPGroup p G) (K : Subgroup (MulAut G))
    (h : ∀ (u : K) x, QuotientGroup.mk' (frattini G) (u.val x) = QuotientGroup.mk' (frattini G) x) :
    IsPGroup p K := by
  classical
  apply IsPGroup.of_card_dvd_pow (n := Nat.card K)
  apply (Nat.dvd_pow_self_iff (Nat.card_pos (α := K)).ne' (Fact.out : p.Prime).ne_zero).mpr
  intro l hl
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hl
  suffices l = p by subst l; exact Nat.mem_primeFactors.mpr ⟨Fact.out,dvd_rfl,(Fact.out : p.Prime).ne_zero⟩
  by_contra ne
  let _ : Fact l.Prime := ⟨prime⟩
  let L : Sylow l K := default
  have cop := IsPGroup.coprime_card_of_ne l p ne L.toSubgroup (frattini G) L.isPGroup' (hg.to_subgroup _)
  have nd : ¬ l ∣ Nat.card (frattini G) := prime.coprime_iff_not_dvd.mp
    (cop.coprime_dvd_left (L.dvd_card_of_dvd_card dvd))
  have id := trivial_action L.isPGroup' nd (K.subtype.comp L.toSubgroup.subtype) (fun u => h u.val)
  apply L.ne_bot_of_dvd_card dvd
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro u hu
  apply Subtype.ext
  exact DFunLike.ext _ _ (id ⟨u,hu⟩)

/-- A prime-power group acting on two lifts of one homomorphism has an intertwiner
in the kernel whenever its prime does not divide the kernel order. -/
theorem conjugate_lifts {A B H : Type*} [Group A] [Group B] [Group H]
    {l : ℕ} [Fact l.Prime] (hH : IsPGroup l H) (f : A →* B)
    (cop : ¬ l ∣ Nat.card f.ker) (a b : H →* A) (eq : ∀ h, f (a h) = f (b h)) :
    ∃ u : f.ker, ∀ h, b h * u.val = u.val * a h := by
  classical
  let _ : MulAction H f.ker :=
    { smul := fun h u => ⟨b h * u.val * (a h)⁻¹, by
        change f (b h * u.val * (a h)⁻¹) = 1
        simp only [map_mul,map_inv,show f u.val = 1 from u.property,mul_one,eq,mul_inv_cancel]⟩
      one_smul := fun u => Subtype.ext (by change b 1 * u.val * (a 1)⁻¹ = u.val; simp)
      mul_smul := fun g h u => Subtype.ext (by
        change b (g*h) * u.val * (a (g*h))⁻¹ = b g * (b h * u.val * (a h)⁻¹) * (a g)⁻¹
        simp [mul_assoc]) }
  obtain ⟨u,hu⟩ := hH.nonempty_fixed_point_of_prime_not_dvd_card f.ker cop
  refine ⟨u,fun h => ?_⟩
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hu h))

theorem frattini_lifts {P H : Type*} [Group P] [Finite P] [Group H] {p l : ℕ}
    [Fact p.Prime] [Fact l.Prime] (hp : IsPGroup p P) (hl : IsPGroup l H) (ne : l ≠ p)
    (a b : H →* MulAut P) (same : ∀ h x, QuotientGroup.mk' (frattini P) (a h x) =
      QuotientGroup.mk' (frattini P) (b h x)) :
    ∃ u : MulAut P, (∀ x, QuotientGroup.mk' (frattini P) (u x) = QuotientGroup.mk' (frattini P) x) ∧
      ∀ h, b h * u = u * a h := by
  classical
  let N := frattini P
  let f : MulAut P →* MulAut (P ⧸ N) :=
    { toFun := fun u => QuotientGroup.congr N N u (Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic) u)
      map_one' := by ext x; induction x using QuotientGroup.induction_on; rfl
      map_mul' := by intro g h; ext x; induction x using QuotientGroup.induction_on; rfl }
  have fixed (u : f.ker) (x : P) : QuotientGroup.mk' N (u.val x) = QuotientGroup.mk' N x :=
    DFunLike.congr_fun (show f u.val = 1 from u.property) (QuotientGroup.mk' N x)
  obtain ⟨n,hn⟩ := (kernel_isPGroup hp f.ker fixed).exists_card_eq
  have cop : ¬ l ∣ Nat.card f.ker := by
    rw [hn]; exact fun hd => ne ((Nat.prime_dvd_prime_iff_eq (Fact.out : l.Prime) (Fact.out : p.Prime)).mp ((Fact.out : l.Prime).dvd_of_dvd_pow hd))
  obtain ⟨u,hu⟩ := conjugate_lifts hl f cop a b (fun h => by
    apply DFunLike.ext'; funext x; induction x using QuotientGroup.induction_on with
    | _ x => exact same h x)
  exact ⟨u.val,fixed u,hu⟩

/-- Conjugacy of lifts through a finite kernel of order coprime to a solvable acting group. -/
theorem solvable_lifts {A B H : Type*} [Group A] [Group B] [Group H] [Finite H]
    [Group.IsSolvable H] (f : A →* B) [Finite f.ker] (cop : (Nat.card H).Coprime (Nat.card f.ker))
    (a b : H →* A) (eq : ∀ h, f (a h) = f (b h)) :
    ∃ u : f.ker, ∀ h, b h * u.val = u.val * a h := by
  classical
  cases subsingleton_or_nontrivial H with
  | inl hs => exact ⟨1,fun h => by rw [Subsingleton.elim h 1]; simp⟩
  | inr hn =>
    have hc := Group.IsSolvable.commutator_lt_top_of_nontrivial H
    obtain ⟨M,maxi,le⟩ := (eq_top_or_exists_le_coatom (commutator H)).resolve_left hc.ne
    let _ : M.Normal := Subgroup.Normal.of_commutator_le H le
    have idx := M.one_lt_index_of_ne_top maxi.1
    obtain ⟨l,prime,dvd⟩ := Nat.exists_prime_and_dvd (by omega : M.index ≠ 1)
    let _ : Fact l.Prime := ⟨prime⟩
    let L : Sylow l H := default
    have top : M ⊔ L.toSubgroup = ⊤ := maxi.2 _ (lt_of_le_of_ne le_sup_left fun e =>
      L.not_dvd_index (dvd.trans (Subgroup.index_dvd_of_le (show L.toSubgroup ≤ M by rw [e]; exact le_sup_right))))
    obtain ⟨u,hu⟩ := solvable_lifts f (cop.coprime_dvd_left M.card_subgroup_dvd_card)
      (a.comp M.subtype) (b.comp M.subtype) (fun m => eq m)
    let _ : MulAction H f.ker :=
      { smul := fun h v => ⟨b h * v.val * (a h)⁻¹, by
          change f (b h * v.val * (a h)⁻¹) = 1
          simp only [map_mul,map_inv,show f v.val = 1 from v.property,mul_one,eq,mul_inv_cancel]⟩
        one_smul := fun v => Subtype.ext (by change b 1 * v.val * (a 1)⁻¹ = v.val; simp)
        mul_smul := fun g h v => Subtype.ext (by
          change b (g*h) * v.val * (a (g*h))⁻¹ = b g * (b h * v.val * (a h)⁻¹) * (a g)⁻¹
          simp [mul_assoc]) }
    let F := MulAction.fixedPoints M f.ker
    have iff_fixed (v : f.ker) : v ∈ F ↔ ∀ m : M, b m * v.val = v.val * a m := by
      constructor
      · intro hv m; exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (hv m))
      · intro hv m; exact Subtype.ext (mul_inv_eq_iff_eq_mul.mpr (hv m))
    let C := (Subgroup.centralizer (a.comp M.subtype).range).subgroupOf f.ker
    have comm (v : f.ker) : v ∈ C ↔ ∀ m : M, a m * v.val = v.val * a m := by
      change (∀ y ∈ (a.comp M.subtype).range, y * v.val = v.val * y) ↔ _
      exact ⟨fun h m => h _ ⟨m,rfl⟩,fun h _ ⟨m,hm⟩ => hm ▸ h m⟩
    let e : C ≃ F :=
      { toFun := fun v => ⟨u * v.val, iff_fixed _ |>.mpr fun m => by
          change b m * (u.val * v.val.val) = u.val * v.val.val * a m
          rw [← mul_assoc,show b m * u.val = u.val * a m from hu m,mul_assoc,(comm _ |>.mp v.property) m,mul_assoc]⟩
        invFun := fun v => ⟨u⁻¹ * v.val, (comm _).mpr fun m => by
          change a m * (u.val⁻¹ * v.val.val) = u.val⁻¹ * v.val.val * a m
          have h := hu m
          change b m * u.val = u.val * a m at h
          have g := (iff_fixed _ |>.mp v.property) m
          calc
            _ = u.val⁻¹ * (u.val * a m) * (u.val⁻¹ * v.val.val) := by group
            _ = _ := by rw [← h]; simp [mul_assoc,g]⟩
        left_inv := fun v => Subtype.ext (inv_mul_cancel_left ..)
        right_inv := fun v => Subtype.ext (mul_inv_cancel_left ..) }
    have nd : ¬ l ∣ Nat.card F := by
      rw [← Nat.card_congr e]
      exact prime.coprime_iff_not_dvd.mp ((cop.coprime_dvd_left (dvd.trans M.index_dvd_card)).coprime_dvd_right C.card_subgroup_dvd_card)
    obtain ⟨v,hv⟩ := L.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card F nd
    have both : v.val ∈ MulAction.fixedPoints (↥(M ⊔ L.toSubgroup)) f.ker := by
      rw [fixedPoints_subgroup_sup]
      exact ⟨v.property,fun j => congrArg Subtype.val (hv j)⟩
    rw [top] at both
    exact ⟨v.val,fun h => mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (both ⟨h,Subgroup.mem_top _⟩))⟩
termination_by Nat.card H
decreasing_by
  have := M.index_mul_card
  have pos := Nat.card_pos (α := M)
  nlinarith

theorem solvable_frattini_lifts {P H : Type*} [Group P] [Finite P] [Group H] [Finite H] [Group.IsSolvable H] {p : ℕ}
    [Fact p.Prime] (hp : IsPGroup p P) (cop : ¬ p ∣ Nat.card H)
    (a b : H →* MulAut P) (same : ∀ h x, QuotientGroup.mk' (frattini P) (a h x) =
      QuotientGroup.mk' (frattini P) (b h x)) :
    ∃ u : MulAut P, (∀ x, QuotientGroup.mk' (frattini P) (u x) = QuotientGroup.mk' (frattini P) x) ∧
      ∀ h, b h * u = u * a h := by
  classical
  let N := frattini P
  let f : MulAut P →* MulAut (P ⧸ N) :=
    { toFun := fun u => QuotientGroup.congr N N u (Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic) u)
      map_one' := by ext x; induction x using QuotientGroup.induction_on; rfl
      map_mul' := by intro g h; ext x; induction x using QuotientGroup.induction_on; rfl }
  have fixed (u : f.ker) (x : P) : QuotientGroup.mk' N (u.val x) = QuotientGroup.mk' N x :=
    DFunLike.congr_fun (show f u.val = 1 from u.property) (QuotientGroup.mk' N x)
  obtain ⟨n,hn⟩ := (kernel_isPGroup hp f.ker fixed).exists_card_eq
  have ck : (Nat.card H).Coprime (Nat.card f.ker) := by
    rw [hn]; exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr cop).symm.pow_right n
  obtain ⟨u,hu⟩ := solvable_lifts f ck a b (fun h => by
    apply DFunLike.ext'; funext x; induction x using QuotientGroup.induction_on with
    | _ x => exact same h x)
  exact ⟨u.val,fixed u,hu⟩

theorem quotient_commutative (P : Type*) [Group P] [Finite P] [Group.IsNilpotent P] :
    IsMulCommutative (P ⧸ frattini P) := by
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  apply le_iInf; intro M; apply le_iInf; intro hM
  change IsCoatom M at hM
  let _ : M.Normal := ((Group.isNilpotent_of_finite_tfae (G := P)).out 0 2 rfl rfl).mp ‹_› M hM
  obtain ⟨x,hx⟩ := SetLike.exists_not_mem_of_ne_top M hM.1
  have lt : M < M ⊔ Subgroup.zpowers x := lt_of_le_of_ne le_sup_left (fun eq =>
    hx (Subgroup.zpowers_le.mp (eq.symm ▸ (le_sup_right : Subgroup.zpowers x ≤ M ⊔ Subgroup.zpowers x))))
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (hM.2 _ lt) inferInstance
/-- A primary component uses at most log₂ |P| factors in the action-code bound. -/
lemma primary_component_code (P H : FiniteGrp.{0}) [Group.IsSolvable H] {p : ℕ}
    [Fact p.Prime] (hp : IsPGroup p P) (cop : ¬ p ∣ Nat.card H) :
    ∃ (D : Type) (_ : Finite D) (encode : (H →* MulAut P) → D),
      Nat.card D ≤ ((Nat.card H+1)*Nat.card P)^(Nat.log 2 (Nat.card P)) ∧
      ∀ i j, encode i = encode j → ∃ u : MulAut P, ∀ h x, j h (u x) = u (i h x) := by
  classical
  let N := frattini P
  let Q := P ⧸ N
  let _ : Finite Q := inferInstanceAs (Finite (P ⧸ N))
  let q : P →* Q := QuotientGroup.mk' N
  let _ : Group.IsNilpotent P := hp.isNilpotent
  let _ : IsMulCommutative (FiniteGrp.of Q) := quotient_commutative P
  have qle : Nat.card Q ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos N.card_quotient_dvd_card
  have hk := (hp.to_quotient N).exists_card_eq
  obtain ⟨s,hs⟩ := hk
  obtain ⟨t,ht,C,fin,code,bc,inter⟩ := prime_action_code (FiniteGrp.of Q) H hs cop
  let f : MulAut P →* MulAut Q :=
    { toFun := fun u => QuotientGroup.congr N N u (Subgroup.characteristic_iff_map_eq.mp frattini_characteristic u)
      map_one' := by ext x; induction x using QuotientGroup.induction_on; rfl
      map_mul' := by intro g h; ext x; induction x using QuotientGroup.induction_on; rfl }
  let S := H →* MulAut P
  let b (i : S) := f.comp i
  let c (i : S) := code (b i)
  let base (i : S) : S := (show ∃ j, c j = c i from ⟨i,rfl⟩).choose
  have samebase {i j : S} (e : c i = c j) : base i = base j := by simp only [base,e]
  choose U hU using fun i : S => inter (b i) (b (base i)) (Exists.choose_spec (show ∃ j, c j = c i from ⟨i,rfl⟩)).symm
  let _ : Finite (Q →* Q) := Finite.of_injective (fun g : Q →* Q => (g : Q → Q)) DFunLike.coe_injective
  have aut : Nat.card (MulAut Q) ≤ Nat.card Q ^ Nat.log 2 (Nat.card Q) :=
    (Nat.card_le_card_of_injective MulEquiv.toMonoidHom MulEquiv.toMonoidHom_injective).trans (hom_count Q Q)
  refine ⟨C × MulAut Q,inferInstance,(fun i => (c i,(U i : MulAut Q))),?_,?_⟩
  · rw [Nat.card_prod,mul_pow]
    have tle := (Nat.le_log_of_pow_le (by decide : 1 < 2) ht).trans (Nat.log_mono_right qle)
    exact Nat.mul_le_mul (bc.trans (Nat.pow_le_pow_right (by omega) tle))
      (aut.trans ((Nat.pow_le_pow_left qle _).trans (Nat.pow_le_pow_right Nat.card_pos (Nat.log_mono_right qle))))
  · intro i j eq
    have e := samebase (congrArg Prod.fst eq)
    have v : (U i : MulAut Q) = U j := congrArg Prod.snd eq
    have same (h : H) (x : P) : q (i h x) = q (j h x) := by
      apply (U i).injective
      change U i (b i h (q x)) = U i (b j h (q x))
      have hi := hU i h (q x)
      have hj := hU j h (q x)
      change U i = U j at v
      rw [e,v] at hi
      rw [v]
      exact hi.symm.trans hj
    obtain ⟨u,_,hu⟩ := solvable_frattini_lifts hp cop i j same
    exact ⟨u,fun h x => DFunLike.congr_fun (hu h) x⟩

lemma nilpotent_kernel_log_bound (K H : FiniteGrp.{0}) [Group.IsNilpotent K] [Group.IsSolvable H] {r : ℕ}
    (cop : (Nat.card K).Coprime (Nat.card H)) (hr : Nat.card K * Nat.card H < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}).ncard ≤ 2^((r+1)*Nat.log 2 (Nat.card K)) := by
  classical
  let I := ↥(Nat.card K).primeFactors
  let (i : I) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
  let P (i : I) : Sylow i.val K := default
  let v : K ≃* ((i : I) → P i) :=
    (Sylow.directProductOfNormal (G := K) fun _ => inferInstance).symm.trans (MulEquiv.piCongrRight fun i => by
      let _ := Sylow.unique_of_normal (P i) inferInstance
      exact MulEquiv.piUnique (fun Q : Sylow i.val K => Q))
  have disj : Pairwise fun i j => (Nat.card (P i)).Coprime (Nat.card (P j)) := by
    intro i j ne
    exact IsPGroup.coprime_card_of_ne i.val j.val (fun h => ne (Subtype.ext h)) _ _ (P i).isPGroup' (P j).isPGroup'
  choose res compat using component_actions (fun i => ↥(P i)) disj
  have nd (i : I) : ¬ i.val ∣ Nat.card H :=
    (Nat.prime_of_mem_primeFactors i.property).coprime_iff_not_dvd.mp
      (cop.coprime_dvd_left (Nat.dvd_of_mem_primeFactors i.property))
  choose C fin code bound inter using fun i : I => primary_component_code (FiniteGrp.of (P i)) H
    (p := i.val) (P i).isPGroup' (nd i)
  let t (i : I) := Nat.log 2 (Nat.card (P i))
  have size (i : I) : 2^t i ≤ Nat.card (P i) := Nat.pow_log_le_self _ Nat.card_pos.ne'
  have lim : ∑ i, t i ≤ Nat.log 2 (Nat.card K) := by
    have sz : 2^(∑ i, t i) ≤ Nat.card K := by
      calc
        _ ≤ ∏ i, Nat.card (P i) := by
          rw [← Finset.prod_pow_eq_pow_sum]
          exact Finset.prod_le_prod' fun i _ => size i
        _ = _ := (Nat.card_pi.symm.trans (Nat.card_congr v.toEquiv).symm)
    exact Nat.le_log_of_pow_le (by decide) sz
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}
  let G (x : S) : FiniteGrp.{0} := x.property.choose
  have rep (x : S) : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (G x) = x.val := x.property.choose_spec.2
  choose a iso using fun x : S => x.property.choose_spec.1
  let act (x : S) := (MulAut.congr v).toMonoidHom.comp (a x)
  let parts (x : S) (i : I) := (res i).comp (act x)
  have inj : Function.Injective (fun x i => code i (parts x i)) := by
    intro x y eq
    choose U hU using fun i => inter i _ _ (congrFun eq i)
    let V (i : I) : ↥(P i) ≃* ↥(P i) := U i
    let f := v.trans ((MulEquiv.piCongrRight V).trans v.symm)
    have equivariant (h : H) : (a x h).trans f = f.trans (a y h) := by
      apply DFunLike.ext'; funext z
      apply v.injective
      change v (v.symm ((MulEquiv.piCongrRight V) (v ((a x h) z)))) =
        v ((a y h) (v.symm ((MulEquiv.piCongrRight V) (v z))))
      rw [v.apply_symm_apply]
      funext i
      have e := hU i h (v z i)
      change res i (act y h) (U i (v z i)) = U i (res i (act x h) (v z i)) at e
      rw [compat i (act x h) (v z)] at e
      have lhs := compat i (act y h) ((MulEquiv.piCongrRight V) (v z))
      have key := e.symm.trans lhs
      change V i (v ((a x h) (v.symm (v z))) i) = v ((a y h) (v.symm ((MulEquiv.piCongrRight V) (v z)))) i at key
      change V i (v ((a x h) z) i) = _
      simpa only [v.symm_apply_apply] using key
    let mid := SemidirectProduct.congr f (MulEquiv.refl H) equivariant
    apply Subtype.ext
    rw [← rep x,← rep y]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (((iso x).some.trans (mid.trans (iso y).some.symm)).toGrpIso)⟩
  change Nat.card S ≤ _
  apply (Nat.card_le_card_of_injective _ inj).trans
  rw [Nat.card_pi]
  have term (i : I) : Nat.card (C i) ≤ (2^(r+1))^(t i) := by
    apply (bound i).trans (Nat.pow_le_pow_left _ _)
    have le := Nat.le_of_dvd Nat.card_pos (P i).toSubgroup.card_subgroup_dvd_card
    change (Nat.card H+1)*Nat.card (P i) ≤ 2^(r+1)
    have hle := Nat.mul_le_mul_left (Nat.card H) le
    have klt := (Nat.le_mul_of_pos_right (Nat.card K) (Nat.card_pos (α := H))).trans_lt hr
    rw [Nat.mul_comm (Nat.card H) (Nat.card K)] at hle
    rw [Nat.add_mul,one_mul,pow_succ]; omega
  apply (Finset.prod_le_prod' (fun i _ => term i)).trans
  rw [Finset.prod_pow_eq_pow_sum,pow_mul]
  exact Nat.pow_le_pow_right (by positivity) lim

lemma nilpotent_kernel_action_bound (K H : FiniteGrp.{0}) [Group.IsNilpotent K] [Group.IsSolvable H] {r : ℕ}
    (cop : (Nat.card K).Coprime (Nat.card H)) (hr : Nat.card K * Nat.card H < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut K, Nonempty (G ≃* SemidirectProduct K H a)}).ncard ≤ 2^((r+1)*r) := by
  apply (nilpotent_kernel_log_bound K H cop hr).trans
  apply Nat.pow_le_pow_right (by decide)
  exact Nat.mul_le_mul_left _ (Nat.log_lt_of_lt_pow Nat.card_pos.ne'
    ((Nat.le_mul_of_pos_right _ Nat.card_pos).trans_lt hr)).le

/-- Bound the split products for a fixed primary kernel and fixed solvable coprime complement. -/
theorem primary_kernel_action_count (P H : FiniteGrp.{0}) [Group.IsSolvable H] {p r : ℕ}
    [Fact p.Prime] (hp : IsPGroup p P) (cop : ¬ p ∣ Nat.card H)
    (hr : Nat.card P * Nat.card H < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut P, Nonempty (G ≃* SemidirectProduct P H a)}).ncard ≤
      2^((r+1)*r) := by
  let _ : Group.IsNilpotent P := hp.isNilpotent
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  apply nilpotent_kernel_action_bound _ _ _ hr
  rw [hk]
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr cop).pow_left k

/-- Count split extensions for a fixed pair of groups of distinct prime-power orders. -/
theorem two_primary_action_count (P H : FiniteGrp.{0}) {p l r : ℕ}
    [Fact p.Prime] [Fact l.Prime] (hp : IsPGroup p P) (hl : IsPGroup l H) (ne : l ≠ p)
    (hr : Nat.card P * Nat.card H < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ a : H →* MulAut P, Nonempty (G ≃* SemidirectProduct P H a)}).ncard ≤
      2^((r+1)*r) := by
  let _ : Group.IsNilpotent H := hl.isNilpotent
  obtain ⟨m,hm⟩ := hl.exists_card_eq
  have cop : ¬ p ∣ Nat.card H := by
    rw [hm]; exact fun hd => ne ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : l.Prime)).mp ((Fact.out : p.Prime).dvd_of_dvd_pow hd)).symm
  exact primary_kernel_action_count _ _ hp cop hr

/-- Sum over kernel and complement isomorphism classes using the coprime Sylow product. -/
theorem nilpotent_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ K H : FiniteGrp.{0}, Group.IsNilpotent K ∧
        Group.IsNilpotent H ∧
        (Nat.card K).Coprime (Nat.card H) ∧ ∃ f : H →* MulAut K, Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^((r+1)^2) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G ∧ Group.IsNilpotent G}
  let K {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  let H {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  have kc {n} (x : O n) : Nat.card (K x) = n := x.property.choose_spec.1.1
  have hc {n} (x : O n) : Nat.card (H x) = n := x.property.choose_spec.1.1
  let (n : ℕ) : Finite (O n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 0 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  let X (i : I) := O i.val.val × O (q/i.val.val)
  let S (i : I) (x : X i) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H x.2 →* MulAut (K x.1), Nonempty (G ≃* SemidirectProduct _ _ a)}
  have finite (i : I) (x : X i) : (S i x).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨a,⟨u⟩⟩
    exact (Nat.card_congr u.toEquiv).trans (by rw [SemidirectProduct.card,kc,hc]; exact i.property.2.2.1)))
  have inner (i : I) : (⋃ x : X i, S i x).ncard ≤ 2^((r+1)*r)*L q := by
    let _ := Fintype.ofFinite (X i)
    have cnt (x : X i) : (S i x).ncard ≤ 2^((r+1)*r) := by
      have cp : (Nat.card (K x.1)).Coprime (Nat.card (H x.2)) := by rw [kc,hc]; exact i.property.2.2.2
      have sz : Nat.card (K x.1) * Nat.card (H x.2) < 2^r := by rw [kc,hc,i.property.2.2.1]; exact hr
      let _ : Group.IsSolvable (H x.2) := x.2.property.choose_spec.1.2.1
      let _ : Group.IsNilpotent (K x.1) := x.1.property.choose_spec.1.2.2
      exact nilpotent_kernel_action_bound _ _ cp sz
    have sz : Nat.card (X i) ≤ L q := by
      rw [← i.property.2.2.1]; unfold L; rw [sylow_product_coprime i.property.1 i.property.2.1 i.property.2.2.2]
      change Nat.card (O _ × O _) ≤ _
      rw [Nat.card_prod]
      exact Nat.mul_le_mul (nilpotent_bound _) (nilpotent_bound _)
    calc
      _ ≤ ∑ x : X i, (S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : X i, 2^((r+1)*r) := Finset.sum_le_sum fun x _ => cnt x
      _ = 2^((r+1)*r)*Nat.card (X i) := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_left _ sz
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, ⋃ x : X i, S i x) ?_
    (Set.finite_iUnion fun i => Set.finite_iUnion (finite i))) ?_
  · rintro _ ⟨G,⟨hg,N,P,comm,nil,cop,a,⟨u⟩⟩,rfl⟩
    let _ : Group.IsNilpotent N := comm
    let _ : Group.IsNilpotent P := nil
    have sol : Group.IsSolvable P := inferInstance
    have eq := ((Nat.card_congr u.toEquiv).symm.trans hg)
    rw [SemidirectProduct.card] at eq
    have leq := (Nat.le_mul_of_pos_right (Nat.card N) (Nat.card_pos (α := P))).trans eq.le
    have div : q/Nat.card N = Nat.card P := by rw [← eq,Nat.mul_div_cancel_left _ Nat.card_pos]
    let i : I := ⟨⟨Nat.card N,by omega⟩,Nat.card_pos,div.symm ▸ Nat.card_pos,div.symm ▸ eq,div.symm ▸ cop⟩
    let x : X i := (⟨Quotient.mk _ N,N,⟨rfl,inferInstance,comm⟩,rfl⟩,⟨Quotient.mk _ P,P,⟨div.symm,sol,nil⟩,rfl⟩)
    have kn : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x.1) = Quotient.mk _ N := x.1.property.choose_spec.2
    have hp : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (H x.2) = Quotient.mk _ P := x.2.property.choose_spec.2
    let f := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact kn))).groupIsoToMulEquiv.symm
    let h := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact hp))).groupIsoToMulEquiv.symm
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x,G,⟨_,⟨u.trans (SemidirectProduct.congr' f h)⟩⟩,rfl⟩⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (⋃ x : X i, S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^((r+1)*r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^((r+1)*r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^((r+1)*r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by rw [← mul_assoc,← pow_add]; apply Nat.mul_le_mul_right; apply Nat.pow_le_pow_right (by decide); nlinarith


/-- Count the groups with a nontrivial nilpotent Hall kernel using the solvable count at smaller orders. -/
theorem solvable_hall_induction_step {q r E : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ K H : FiniteGrp.{0}, Group.IsNilpotent K ∧
        1 < Nat.card K ∧ Group.IsSolvable H ∧
        (Nat.card K).Coprime (Nat.card H) ∧ ∃ f : H →* MulAut K, Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^(E*(r+1)^2-5) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G ∧ Group.IsNilpotent G}
  let T (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}
  let (n : ℕ) : Finite (T n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let K {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  let H {n : ℕ} (x : T n) : FiniteGrp.{0} := x.property.choose
  have kc {n} (x : O n) : Nat.card (K x) = n := x.property.choose_spec.1.1
  have hc {n} (x : T n) : Nat.card (H x) = n := x.property.choose_spec.1.1
  let (n : ℕ) : Finite (O n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 1 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  let X (i : I) := O i.val.val × T (q/i.val.val)
  let S (i : I) (x : X i) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ a : H x.2 →* MulAut (K x.1), Nonempty (G ≃* SemidirectProduct _ _ a)}
  have finite (i : I) (x : X i) : (S i x).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨a,⟨u⟩⟩
    exact (Nat.card_congr u.toEquiv).trans (by rw [SemidirectProduct.card,kc,hc]; exact i.property.2.2.1)))
  have inner (i : I) : (⋃ x : X i, S i x).ncard ≤ 2^(E*(r+1)^2-5-r)*L q := by
    let _ := Fintype.ofFinite (X i)
    let k := i.val.val
    let h := q/k
    let d := Nat.log 2 k
    have hk : 1 < k := i.property.1
    have hh : 0 < h := i.property.2.1
    have eq : k*h = q := i.property.2.2.1
    have small : h < q := by rw [← eq]; nlinarith
    have dpos : 1 ≤ d := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ k by omega))
    have kd : 2^d ≤ k := Nat.pow_log_le_self _ (by omega)
    have dr : d ≤ r := (Nat.log_lt_of_lt_pow (by omega) ((Nat.le_mul_of_pos_right k hh).trans_lt (eq ▸ hr))).le
    let s := r-d
    have split : s+d = r := Nat.sub_add_cancel dr
    have shr : h < 2^s := by
      by_contra! bad
      have z := Nat.mul_le_mul kd bad
      rw [← pow_add, Nat.add_comm d s, split, eq] at z
      omega
    have budget : r + ((r+1)*d + E*(s+1)^2) + 5 ≤ E*(r+1)^2 := by
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le dpos
      obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le hE
      rw [← split,hj,hc]; ring_nf; omega
    have cnt (x : X i) : (S i x).ncard ≤ 2^((r+1)*d) := by
      have cp : (Nat.card (K x.1)).Coprime (Nat.card (H x.2)) := by rw [kc,hc]; exact i.property.2.2.2
      have sz : Nat.card (K x.1) * Nat.card (H x.2) < 2^r := by rw [kc,hc,i.property.2.2.1]; exact hr
      let _ : Group.IsSolvable (H x.2) := x.2.property.choose_spec.1.2
      let _ : Group.IsNilpotent (K x.1) := x.1.property.choose_spec.1.2.2
      simpa only [kc] using nilpotent_kernel_log_bound _ _ cp sz
    have countH := ih h small s (odd.of_dvd_nat ⟨k,by rw [← eq,Nat.mul_comm]⟩) shr
    have sz : Nat.card (X i) ≤ 2^(E*(s+1)^2)*L q := by
      change Nat.card (O k × T h) ≤ _
      rw [Nat.card_prod]
      calc
        _ ≤ L k * (2^(E*(s+1)^2)*L h) := Nat.mul_le_mul (nilpotent_bound _) countH
        _ = 2^(E*(s+1)^2)*(L k * L h) := by ring
        _ = _ := by congr 1; exact (eq ▸ sylow_product_coprime (by omega : 0 < k) hh i.property.2.2.2).symm
    calc
      _ ≤ ∑ x : X i, (S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : X i, 2^((r+1)*d) := Finset.sum_le_sum fun x _ => cnt x
      _ = 2^((r+1)*d)*Nat.card (X i) := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
      _ ≤ 2^((r+1)*d)*(2^(E*(s+1)^2)*L q) := Nat.mul_le_mul_left _ sz
      _ ≤ _ := by rw [← mul_assoc,← pow_add]; exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, ⋃ x : X i, S i x) ?_
    (Set.finite_iUnion fun i => Set.finite_iUnion (finite i))) ?_
  · rintro _ ⟨G,⟨hg,N,P,comm,large,sol,cop,a,⟨u⟩⟩,rfl⟩
    let _ : Group.IsNilpotent N := comm
    have eq := ((Nat.card_congr u.toEquiv).symm.trans hg)
    rw [SemidirectProduct.card] at eq
    have leq := (Nat.le_mul_of_pos_right (Nat.card N) (Nat.card_pos (α := P))).trans eq.le
    have div : q/Nat.card N = Nat.card P := by rw [← eq,Nat.mul_div_cancel_left _ Nat.card_pos]
    let i : I := ⟨⟨Nat.card N,by omega⟩,large,div.symm ▸ Nat.card_pos,div.symm ▸ eq,div.symm ▸ cop⟩
    let x : X i := (⟨Quotient.mk _ N,N,⟨rfl,inferInstance,comm⟩,rfl⟩,⟨Quotient.mk _ P,P,⟨div.symm,sol⟩,rfl⟩)
    have kn : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x.1) = Quotient.mk _ N := x.1.property.choose_spec.2
    have hp : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (H x.2) = Quotient.mk _ P := x.2.property.choose_spec.2
    let f := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact kn))).groupIsoToMulEquiv.symm
    let h := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact hp))).groupIsoToMulEquiv.symm
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x,G,⟨_,⟨u.trans (SemidirectProduct.congr' f h)⟩⟩,rfl⟩⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (⋃ x : X i, S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(E*(r+1)^2-5-r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^(E*(r+1)^2-5-r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^(E*(r+1)^2-5-r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by
        rw [← mul_assoc,← pow_add]
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        have := Nat.mul_le_mul_right ((r+1)^2) hE
        have : r+5 ≤ 6*(r+1)^2 := by nlinarith
        omega


/-- Mark a generator of a cyclic direct factor to recover the original quotient. -/
lemma cyclic_padding {n k : ℕ} (hk : 0 < k) : g n ≤ (n*k)*g (n*k) := by
  classical
  let T := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = n*k}
  let _ : Finite T := (finite_classes _).to_subtype
  let R (x : T) : FiniteGrp.{0} := x.property.choose
  let decode (z : (x : T) × R x) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    let N := Subgroup.zpowers z.2
    if hn : N.Normal then
      exact Quotient.mk _ (FiniteGrp.of (R z.1 ⧸ N))
    else exact Quotient.mk _ (R z.1)
  let _ : NeZero k := ⟨hk.ne'⟩
  let C := Multiplicative (ZMod k)
  obtain ⟨c,hc⟩ := IsCyclic.exists_generator (α := C)
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = n} ⊆ Set.range decode := by
    rintro _ ⟨G,hg,rfl⟩
    let X := FiniteGrp.of (G × C)
    have sz : Nat.card X = n*k := by
      change Nat.card (G × C) = _
      rw [Nat.card_prod,show Nat.card G = n from hg,show Nat.card C = k from Nat.card_zmod _]
    let x : T := ⟨Quotient.mk _ X,X,sz,rfl⟩
    let iso := Classical.choice (Quotient.exact (show Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (R x) = Quotient.mk _ X from x.property.choose_spec.2))
    let e : R x ≃* G × C := ((inducedFunctor FiniteGrp.toGrp).mapIso iso).groupIsoToMulEquiv
    let f := (MonoidHom.fst G C).comp e.toMonoidHom
    let z := e.symm (1,c)
    have ker : Subgroup.zpowers z = f.ker := by
      apply le_antisymm (Subgroup.zpowers_le.mpr (by change (e (e.symm (1,c))).1 = 1; simp))
      intro y hy
      change (e y).1 = 1 at hy
      obtain ⟨m,hm⟩ := hc (e y).2
      refine ⟨m,e.injective ?_⟩
      rw [map_zpow,show e z = (1,c) from e.apply_symm_apply _]
      exact Prod.ext (by simpa using hy.symm) hm
    have normal : (Subgroup.zpowers z).Normal := ker ▸ inferInstance
    let u := (QuotientGroup.quotientMulEquivOfEq ker).trans (QuotientGroup.quotientKerEquivOfSurjective f
      (fun y => ⟨e.symm (y,1),by change (e (e.symm (y,1))).1 = y; simp⟩))
    refine ⟨⟨x,z⟩,?_⟩
    simp only [decode,dif_pos normal]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) u.toGrpIso⟩
  calc
    _ ≤ (Set.range decode).ncard := Set.ncard_le_ncard cover (Set.finite_range _)
    _ ≤ Nat.card ((x : T) × R x) := Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))
    _ = _ := by
      let _ := Fintype.ofFinite T
      rw [Nat.card_sigma]
      have sz (x : T) : Nat.card (R x) = n*k := x.property.choose_spec.1
      simp only [sz,Finset.sum_const,Finset.card_univ,smul_eq_mul]
      change Fintype.card T * (n*k) = (n*k)*Nat.card T
      rw [Nat.card_eq_fintype_card,Nat.mul_comm]
lemma sylow_product_dvd_bound {h q : ℕ} (hh : 0 < h) (hq : 0 < q) (dv : h ∣ q) :
    (∏ p ∈ h.primeFactors, g (p^h.factorization p)) ≤ q * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  have sub := Nat.primeFactors_mono dv hq.ne'
  have term (p : ℕ) (hp : p ∈ h.primeFactors) :
      g (p^h.factorization p) ≤ p^q.factorization p * g (p^q.factorization p) := by
    have le := (Nat.factorization_le_iff_dvd hh.ne' hq.ne').mpr dv p
    obtain ⟨d,ed⟩ := Nat.exists_eq_add_of_le le
    rw [ed,pow_add]
    exact cyclic_padding (pow_pos (Nat.prime_of_mem_primeFactors hp).pos d)
  calc
    _ ≤ ∏ p ∈ h.primeFactors, p^q.factorization p * g (p^q.factorization p) :=
      Finset.prod_le_prod' term
    _ ≤ ∏ p ∈ q.primeFactors, p^q.factorization p * g (p^q.factorization p) :=
      Finset.prod_le_prod_of_subset_of_one_le' sub fun p hp _ =>
        Nat.mul_pos (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _) (positive_count (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      exact congrArg (· * _) (Nat.prod_factorization_pow_eq_self hq.ne')


/-- Record a cyclic quotient extension using an action of the infinite cyclic group
and the power of a lift of a generator. -/
theorem cyclic_chosen_lift_model {K G : Type*} [Group K] [Group G] (N : Subgroup G)
    [N.Normal] (e : K ≃* N) (t : G)
    (hv : ∀ x : G ⧸ N, x ∈ Subgroup.zpowers (QuotientGroup.mk' N t)) :
    ∃ (a : Multiplicative ℤ →* MulAut K) (b : K),
      a (Multiplicative.ofAdd 1) = ((MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := N))) t ∧
      (a (Multiplicative.ofAdd 1))^N.index = MulAut.conj b ∧
      Nonempty (G ≃* ((K ⋊[a] Multiplicative ℤ) ⧸ Subgroup.normalClosure
        { (⟨b⁻¹,Multiplicative.ofAdd (N.index : ℤ)⟩ : K ⋊[a] Multiplicative ℤ) })) := by
  classical
  let q := QuotientGroup.mk' N
  let v := q t
  have ht : q t = v := rfl
  have ord : orderOf v = N.index := orderOf_eq_card_of_forall_mem_zpowers hv
  let τ := zpowersHom G t
  let i := N.subtype.comp e.toMonoidHom
  have ii : Function.Injective i := Subtype.val_injective.comp e.injective
  let α := MulAut.conjNormal (H := N)
  let a := ((MulAut.congr e.symm).toMonoidHom.comp α).comp τ
  have compat (j : Multiplicative ℤ) : i.comp (a j).toMonoidHom = (MulAut.conj (τ j)).toMonoidHom.comp i := by
    ext x
    change (e (e.symm (α (τ j) (e x)))).val = _
    rw [e.apply_symm_apply]; rfl
  let F := SemidirectProduct.lift i τ compat
  have onto : Function.Surjective F := by
    intro x
    obtain ⟨m,hm⟩ := hv (q x)
    have mem : x / t^m ∈ N := by apply QuotientGroup.eq_iff_div_mem.mp; change q x = q (t^m); rw [map_zpow,show q t = v from ht]; exact hm.symm
    refine ⟨⟨e.symm ⟨_,mem⟩,Multiplicative.ofAdd m⟩,?_⟩
    change (e (e.symm ⟨x/t^m,mem⟩)).val * t^m = x
    simp
  have tm : t^N.index ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (t^N.index) = 1
    rw [map_pow,show q t = v from ht,← ord,pow_orderOf_eq_one]
  let b := e.symm ⟨_,tm⟩
  let w : K ⋊[a] Multiplicative ℤ := ⟨b⁻¹,Multiplicative.ofAdd (N.index : ℤ)⟩
  have ib : i b = t^N.index := congrArg Subtype.val (e.apply_symm_apply _)
  have fw : F w = 1 := by change i b⁻¹ * t^(N.index : ℤ) = 1; rw [map_inv,ib,zpow_natCast,inv_mul_cancel]
  have kernel : Subgroup.normalClosure {w} = F.ker := by
    apply le_antisymm (Subgroup.normalClosure_le_normal (by simpa using fw : ({w} : Set _) ⊆ F.ker))
    intro z hz
    change i z.left * t^z.right.toAdd = 1 at hz
    have qz := congrArg q hz
    have qi : q (i z.left) = 1 := (QuotientGroup.eq_one_iff _).mpr (e z.left).property
    rw [map_mul,qi,one_mul,map_zpow,show q t = v from ht,map_one] at qz
    obtain ⟨j,hj⟩ := orderOf_dvd_iff_zpow_eq_one.mpr qz
    rw [ord] at hj
    have eq : z = w^j := by
      have right : z.right = (w^j).right := by
        change z.right = (SemidirectProduct.rightHom (w^j))
        rw [map_zpow]
        exact congrArg Multiplicative.ofAdd (hj.trans (Int.mul_comm ..))
      apply SemidirectProduct.ext _ right
      apply ii
      have fw' := show F (w^j) = 1 by rw [map_zpow,fw,one_zpow]
      change i (w^j).left * t^(w^j).right.toAdd = 1 at fw'
      exact mul_right_cancel ((right ▸ hz).trans fw'.symm)
    rw [eq]
    exact (Subgroup.normalClosure {w}).zpow_mem (Subgroup.subset_normalClosure (Set.mem_singleton w)) _
  have power : (a (Multiplicative.ofAdd 1))^N.index = MulAut.conj b := by
    ext x
    apply ii
    have h := DFunLike.congr_fun (compat (Multiplicative.ofAdd (N.index : ℤ))) x
    change i (a (Multiplicative.ofAdd (N.index : ℤ)) x) = t^(N.index : ℤ) * i x * (t^(N.index : ℤ))⁻¹ at h
    rw [MonoidHom.apply_mint _ a,show (Multiplicative.ofAdd (N.index : ℤ)).toAdd = (N.index : ℤ) from rfl,zpow_natCast] at h
    change i (((a (Multiplicative.ofAdd 1))^N.index) x) = i (b*x*b⁻¹)
    simpa only [map_mul,map_inv,ib,zpow_natCast] using h
  have generator : a (Multiplicative.ofAdd 1) = ((MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := N))) t := by
    change ((MulAut.congr e.symm).toMonoidHom.comp α) (t^(1 : ℤ)) = _
    rw [zpow_one]
  exact ⟨a,b,generator,power,⟨(QuotientGroup.quotientKerEquivOfSurjective F onto).symm.trans
    (QuotientGroup.quotientMulEquivOfEq kernel.symm)⟩⟩

theorem cyclic_quotient_power_model {K G : Type*} [Group K] [Group G] (N : Subgroup G)
    [N.Normal] [IsCyclic (G ⧸ N)] (e : K ≃* N) :
    ∃ (a : Multiplicative ℤ →* MulAut K) (b : K),
      (a (Multiplicative.ofAdd 1))^N.index = MulAut.conj b ∧
      Nonempty (G ≃* ((K ⋊[a] Multiplicative ℤ) ⧸ Subgroup.normalClosure
        { (⟨b⁻¹,Multiplicative.ofAdd (N.index : ℤ)⟩ : K ⋊[a] Multiplicative ℤ) })) := by
  obtain ⟨v,hv⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective N v
  obtain ⟨a,b,_,power,model⟩ := cyclic_chosen_lift_model N e t (ht.symm ▸ hv)
  exact ⟨a,b,power,model⟩

theorem cyclic_quotient_model {K G : Type*} [Group K] [Group G] (N : Subgroup G)
    [N.Normal] [IsCyclic (G ⧸ N)] (e : K ≃* N) :
    ∃ (a : Multiplicative ℤ →* MulAut K) (b : K),
      Nonempty (G ≃* ((K ⋊[a] Multiplicative ℤ) ⧸ Subgroup.normalClosure
        { (⟨b⁻¹,Multiplicative.ofAdd (N.index : ℤ)⟩ : K ⋊[a] Multiplicative ℤ) })) := by
  obtain ⟨a,b,_,h⟩ := cyclic_quotient_power_model N e
  exact ⟨a,b,h⟩

/-- A nonempty fiber of the inner automorphism map embeds in the center. -/
lemma inner_power_fiber_bound (K : FiniteGrp.{0}) (u : MulAut K) :
    Nat.card {b : K // MulAut.conj b = u} ≤ Nat.card (Subgroup.center K) := by
  classical
  let X := {b : K // MulAut.conj b = u}
  by_cases inhabited : Nonempty X
  · let b := inhabited.some
    let f (x : X) : Subgroup.center K := ⟨b.val⁻¹*x.val,by
      have h : MulAut.conj (b.val⁻¹*x.val) = 1 := by rw [map_mul,map_inv,b.property,x.property,inv_mul_cancel]
      apply Subgroup.mem_center_iff.mpr
      intro y
      have hy := DFunLike.congr_fun h y
      change (b.val⁻¹*x.val)*y*(b.val⁻¹*x.val)⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm⟩
    apply Nat.card_le_card_of_injective f
    intro x y h
    exact Subtype.ext (mul_left_cancel (congrArg Subtype.val h : b.val⁻¹*x.val = b.val⁻¹*y.val))
  · let _ : IsEmpty X := not_nonempty_iff.mp inhabited
    change Nat.card X ≤ _
    simp

lemma inner_automorphisms_normal (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).range.Normal := by
  constructor
  rintro _ ⟨b,rfl⟩ g
  refine ⟨g b,?_⟩
  ext x
  change g b * x * (g b)⁻¹ = g (b * g.symm x * b⁻¹)
  simp

lemma outer_classes_le_eligible (K : Type*) [Group K] [Finite K] (m : ℕ)
    [(MulAut.conj : K →* MulAut K).range.Normal] :
    (ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^m = 1}).ncard ≤
    (ConjClasses.mk '' {t : MulAut K | ∃ b, MulAut.conj b = t^m}).ncard := by
  classical
  let I := (MulAut.conj : K →* MulAut K).range
  let π := QuotientGroup.mk' I
  let _ : Finite (ConjClasses (MulAut K)) := Finite.of_surjective _ ConjClasses.mk_surjective
  let S := ConjClasses.mk '' {t : MulAut K | ∃ b, MulAut.conj b = t^m}
  have sub : ConjClasses.mk '' {x : MulAut K ⧸ I | x^m = 1} ⊆ ConjClasses.map π '' S := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective I x
    have hp : π (u^m) = 1 := by rw [map_pow,show π u = x from hu]; exact hx
    obtain ⟨b,hb⟩ := (QuotientGroup.eq_one_iff _).mp hp
    exact ⟨_,⟨u,⟨b,hb⟩,rfl⟩,congrArg ConjClasses.mk hu⟩
  exact (Set.ncard_le_ncard sub (Set.Finite.image _ (Set.toFinite S))).trans (Set.ncard_image_le (Set.toFinite S))

/-- A surjection maps the center onto the target precisely when the center and
the kernel together generate the source. -/
lemma center_maps_onto_iff {P Q : Type*} [Group P] [Group Q] (f : P →* Q)
    (onto : Function.Surjective f) :
    (Subgroup.center P).map f = ⊤ ↔ Subgroup.center P ⊔ f.ker = ⊤ := by
  rw [← Subgroup.comap_map_eq,← Subgroup.comap_top f]
  exact (Subgroup.comap_injective onto).eq_iff.symm

lemma center_sup_of_commutative {P : Type*} [Group P] (comm : IsMulCommutative P)
    (H : Subgroup P) : Subgroup.center P ⊔ H = ⊤ := by
  have top : Subgroup.center P = ⊤ := top_unique fun x _ =>
    Subgroup.mem_center_iff.mpr fun y => comm.is_comm.comm y x
  rw [top,top_sup_eq]

/-- For a normal kernel it suffices to test the center condition on one Sylow subgroup. -/
lemma sylow_center_sup_iff_all {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [hN : N.Normal] :
    (∃ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ↔
      ∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤ := by
  constructor
  · rintro ⟨P,hP⟩ Q
    obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq G P Q
    let e := P.equivSMul g
    have hz : (Subgroup.center P).map e.toMonoidHom ≤ Subgroup.center (g • P : Sylow p G) := by
      rintro _ ⟨z,hz,rfl⟩
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨x,rfl⟩ := e.surjective y
      change e x * e z = e z * e x
      simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hz x)
    have hk : (N.subgroupOf P.toSubgroup).map e.toMonoidHom ≤ N.subgroupOf (g • P).toSubgroup := by
      rintro _ ⟨x,hx,rfl⟩
      exact hN.conj_mem x.val hx g
    apply top_unique
    calc
      ⊤ = (⊤ : Subgroup P).map e.toMonoidHom := (Subgroup.map_top_of_surjective _ e.surjective).symm
      _ = _ := congrArg (Subgroup.map e.toMonoidHom) hP.symm
      _ ≤ _ := by rw [Subgroup.map_sup]; exact sup_le_sup hz hk
  · intro h
    exact ⟨default,h _⟩

/-- A central cyclic direct factor illustrates the center-surjectivity condition
even when the other factor is nonabelian. -/
lemma second_factor_center_surjects (D C : Type*) [Group D] [CommGroup C] :
    (Subgroup.center (D × C)).map (MonoidHom.snd D C) = ⊤ := by
  apply top_unique
  intro c _
  refine ⟨(1,c),Subgroup.mem_center_iff.mpr ?_,rfl⟩
  intro x
  exact Prod.ext (by simp) (mul_comm _ _)

/-- A Sylow subgroup projects onto a quotient of order a power of the same prime. -/
lemma sylow_projection_surjective {G : Type*} [Group G] [Finite G] {p a : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (idx : N.index = p^a) (P : Sylow p G) :
    Function.Surjective ((QuotientGroup.mk' N).comp P.toSubgroup.subtype) := by
  let q := QuotientGroup.mk' N
  let Q := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have htop : IsPGroup p (⊤ : Subgroup (G ⧸ N)) :=
    (IsPGroup.of_card (G := G ⧸ N) idx).to_subgroup _
  have top_eq : (⊤ : Subgroup (G ⧸ N)) = Q.toSubgroup := Q.is_maximal' htop le_top
  intro y
  have mem : y ∈ P.toSubgroup.map q := by
    change y ∈ Q.toSubgroup
    rw [← top_eq]
    trivial
  obtain ⟨t,ht,eq⟩ := mem
  exact ⟨⟨t,ht⟩,eq⟩

/-- At prime index, a single element of the Sylow center outside the kernel
is necessary and sufficient for the center to cover the quotient. -/
lemma sylow_center_sup_prime_index_iff {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (N : Subgroup G) [N.Normal] (idx : N.index = p) (P : Sylow p G) :
    Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤ ↔
      ∃ z : P, z ∈ Subgroup.center P ∧ z.val ∉ N := by
  classical
  let f := (QuotientGroup.mk' N).comp P.toSubgroup.subtype
  have onto : Function.Surjective f := sylow_projection_surjective N (idx.trans (pow_one p).symm) P
  have ker : f.ker = N.subgroupOf P.toSubgroup := by
    ext z
    exact QuotientGroup.eq_one_iff z.val
  have card : Nat.card (G ⧸ N) = p := idx
  let _ : Fact (Nat.card (G ⧸ N)).Prime := ⟨card ▸ hp.out⟩
  let _ : Nontrivial (G ⧸ N) := Finite.one_lt_card_iff_nontrivial.mp (card ▸ hp.out.one_lt)
  rw [← ker,← center_maps_onto_iff f onto]
  have witnesses : (∃ z : P, z ∈ Subgroup.center P ∧ z.val ∉ N) ↔ ¬ Subgroup.center P ≤ f.ker := by
    rw [ker,SetLike.le_def]
    push Not
    rfl
  rw [witnesses,← Subgroup.map_eq_bot_iff]
  constructor
  · intro h
    rw [h]
    exact top_ne_bot
  · intro h
    exact ((Subgroup.center P).map f).eq_bot_or_eq_top_of_prime_card.resolve_left h

/-- Lift from the center of an ambient Sylow subgroup containing the prescribed kernel p-subgroup. -/
lemma central_sylow_quotient_lift {K G : Type*} [Group K] [Group G] [Finite G]
    {p a : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal] (idx : N.index = p^a)
    (e : K ≃* N) (S : Subgroup K) (hS : IsPGroup p S)
    (central : ∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) (v : G ⧸ N) :
    ∃ t : G, QuotientGroup.mk' N t = v ∧
      ∀ x ∈ S, (MulAut.congr e.symm (MulAut.conjNormal (H := N) t)) x = x := by
  let i := N.subtype.comp e.toMonoidHom
  obtain ⟨P,hP⟩ := (hS.map i).exists_le_sylow
  let f := (QuotientGroup.mk' N).comp P.toSubgroup.subtype
  have onto : Function.Surjective f := sylow_projection_surjective N idx P
  have ker : f.ker = N.subgroupOf P.toSubgroup := by
    ext u
    exact QuotientGroup.eq_one_iff u.val
  have full : (Subgroup.center P).map f = ⊤ := (center_maps_onto_iff f onto).mpr (ker ▸ central P)
  obtain ⟨t,ht,eq⟩ := (show v ∈ (Subgroup.center P).map f by rw [full]; trivial)
  refine ⟨t.val,eq,?_⟩
  intro x hx
  have mem : i x ∈ P := hP ⟨x,hx,rfl⟩
  have commute : t.val * i x = i x * t.val := congrArg Subtype.val
    ((Subgroup.mem_center_iff.mp ht (⟨i x,mem⟩ : P)).symm)
  apply e.injective
  change e (e.symm _) = e x
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change t.val * i x * t.val⁻¹ = i x
  rw [commute,mul_inv_cancel_right]

/-- A generator of a prime-power quotient lifts to an element centralizing any prescribed
kernel p-subgroup if the ambient Sylow p-subgroups are abelian. -/
lemma exists_pointwise_fixed_quotient_lift {K G : Type*} [Group K] [Group G] [Finite G]
    {p a : ℕ} [Fact p.Prime] (N : Subgroup G) [N.Normal] (idx : N.index = p^a)
    (e : K ≃* N) (S : Subgroup K) (hS : IsPGroup p S)
    (comm : ∀ P : Sylow p G, IsMulCommutative P) (v : G ⧸ N) :
    ∃ t : G, QuotientGroup.mk' N t = v ∧
      ∀ x ∈ S, (MulAut.congr e.symm (MulAut.conjNormal (H := N) t)) x = x :=
  central_sylow_quotient_lift N idx e S hS
    (fun P => center_sup_of_commutative (comm P) _) v

/-- Count cyclic extensions using any set of outer classes covering chosen generator lifts. -/
lemma filtered_outer_cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ)
    [(MulAut.conj : K →* MulAut K).range.Normal] (F : Set FiniteGrp.{0})
    (D : Set (ConjClasses (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)))
    (cover : ∀ G ∈ F, ∃ (N : Subgroup G) (_ : N.Normal) (e : K ≃* N)
        (v : G ⧸ N) (t : G), N.index = m ∧ (∀ x, x ∈ Subgroup.zpowers v) ∧
        QuotientGroup.mk' N t = v ∧
        ConjClasses.mk (QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
          (MulAut.congr e.symm (MulAut.conjNormal (H := N) t))) ∈ D) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' F).ncard ≤
      ((ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^m = 1}) ∩ D).ncard
        * Nat.card (Subgroup.center K) := by
  classical
  let I := (MulAut.conj : K →* MulAut K).range
  let O := MulAut K ⧸ I
  let π := QuotientGroup.mk' I
  let repr (c : ConjClasses O) := (ConjClasses.mk_surjective c).choose
  let rep (c : ConjClasses O) := (QuotientGroup.mk'_surjective I (repr c)).choose
  have proj (c : ConjClasses O) : π (rep c) = repr c := (QuotientGroup.mk'_surjective I _).choose_spec
  let _ : Finite (ConjClasses O) := Finite.of_surjective _ ConjClasses.mk_surjective
  let X (c : ConjClasses O) := {b : K // MulAut.conj b = rep c ^ m}
  let C := (ConjClasses.mk '' {t : O | t^m = 1}) ∩ D
  let Code := (c : C) × X c.val
  let action (c : ConjClasses O) := zpowersHom _ (rep c)
  let Q (c : Code) := (K ⋊[action c.1.val] Multiplicative ℤ) ⧸ Subgroup.normalClosure
    {(⟨c.2.val⁻¹,Multiplicative.ofAdd (m : ℤ)⟩ : K ⋊[action c.1.val] Multiplicative ℤ)}
  let decode (c : Code) : Quotient (isIsomorphicSetoid FiniteGrp.{0}) := by
    if h : Finite (Q c) then exact Quotient.mk _ (FiniteGrp.of (Q c))
    else exact Quotient.mk _ K
  apply le_trans (Set.ncard_le_ncard (t := Set.range decode) ?_ (Set.finite_range _))
    ((Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := decode))).trans ?_)
  swap
  · let _ := Fintype.ofFinite C
    change Nat.card ((c : C) × X c.val) ≤ _
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _ : C, Nat.card (Subgroup.center K) :=
        Finset.sum_le_sum fun c _ => inner_power_fiber_bound K _
      _ = _ := by change _ = Nat.card C * _; simp [Nat.card_eq_fintype_card]
  rintro _ ⟨G,hG,rfl⟩
  obtain ⟨N,hn,e,v,t₀,idx,hv,ht₀,hD⟩ := cover G hG
  let _ : N.Normal := hn
  let ρ := ((MulAut.congr e.symm).toMonoidHom.comp (MulAut.conjNormal (H := N)))
  let u := ρ t₀
  let c := ConjClasses.mk (π u)
  have cl : ConjClasses.mk (π u) = ConjClasses.mk (repr c) := (ConjClasses.mk_surjective c).choose_spec.symm
  obtain ⟨g,hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp cl)
  obtain ⟨f,hf₀⟩ := QuotientGroup.mk'_surjective I g
  have same : π (f⁻¹ * rep c * f) = π u := by
    rw [map_mul,map_mul,map_inv,proj,show π f = g from hf₀,← hg]
    group
  obtain ⟨k,hk⟩ := (QuotientGroup.eq_iff_div_mem.mp same : (f⁻¹ * rep c * f) / u ∈ I)
  let lift := (e k).val * t₀
  have sameLift : QuotientGroup.mk' N lift = v := by
    change QuotientGroup.mk' N ((e k).val * t₀) = v
    have one : QuotientGroup.mk' N (e k).val = 1 := (QuotientGroup.eq_one_iff _).mpr (e k).property
    rw [map_mul,one,one_mul,ht₀]
  have kernelAct : ρ (e k).val = MulAut.conj k := by
    ext x
    change e.symm (MulAut.conjNormal (e k).val (e x)) = k*x*k⁻¹
    rw [MulAut.conjNormal_val]
    simp [MulAut.conj_apply]
  obtain ⟨a,b,gen,power,⟨iso⟩⟩ := cyclic_chosen_lift_model N e lift (sameLift.symm ▸ hv)
  rw [idx] at iso power
  let t := a (Multiplicative.ofAdd 1)
  have ht : t = f⁻¹ * rep c * f := by
    change a (Multiplicative.ofAdd 1) = _
    rw [gen]
    change ρ ((e k).val * t₀) = _
    rw [map_mul,kernelAct,show MulAut.conj k = (f⁻¹ * rep c * f) / u from hk]
    exact div_mul_cancel _ _
  have hf : f*t*f⁻¹ = rep c := by rw [ht]; group
  have acts (j : Multiplicative ℤ) : MulAut.conj f (a j) = action c j := by
    rw [MonoidHom.apply_mint _ a j,map_zpow]
    change (f*t*f⁻¹)^j.toAdd = (rep c)^j.toAdd
    rw [hf]
  let F : (K ⋊[a] Multiplicative ℤ) ≃* (K ⋊[action c] Multiplicative ℤ) :=
    SemidirectProduct.congr f (MulEquiv.refl _) (by
      intro j
      ext x
      have z := DFunLike.congr_fun (acts j) (f x)
      simpa [MulAut.conj_apply] using z)
  let w : K ⋊[a] Multiplicative ℤ := ⟨b⁻¹,Multiplicative.ofAdd (m : ℤ)⟩
  let w' : K ⋊[action c] Multiplicative ℤ := ⟨(f b)⁻¹,Multiplicative.ofAdd (m : ℤ)⟩
  have fw : F w = w' := by
    apply SemidirectProduct.ext
    · exact map_inv f b
    · rfl
  have rel : (Subgroup.normalClosure {w}).map F.toMonoidHom = Subgroup.normalClosure {w'} := by
    rw [Subgroup.map_normalClosure _ _ F.surjective,Set.image_singleton]
    exact congrArg (fun x => Subgroup.normalClosure {x}) fw
  have transformed : MulAut.conj (f b) = rep c ^ m := by
    have eq : MulAut.conj f t = rep c := hf
    rw [← eq,← map_pow,show t^m = MulAut.conj b from power]
    ext x
    change f b * x * (f b)⁻¹ = f (b * f.symm x * b⁻¹)
    simp
  have eligible : (repr c)^m = 1 := by
    rw [← proj,← map_pow,← transformed]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨f b,rfl⟩
  let code : Code := ⟨⟨c,⟨repr c,eligible,(ConjClasses.mk_surjective c).choose_spec⟩,hD⟩,⟨f b,transformed⟩⟩
  let u : G ≃* Q code := iso.trans (QuotientGroup.congr _ _ F rel)
  have fin : Finite (Q code) := Finite.of_equiv G u.toEquiv
  refine ⟨code,?_⟩
  simp only [decode,dif_pos fin]
  exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp) u.symm.toGrpIso⟩

/-- For a cyclic quotient it suffices to record the conjugacy class of the
action of a lifted generator and one element recording its power. -/
lemma outer_cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ)
    [(MulAut.conj : K →* MulAut K).range.Normal] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ (ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^m = 1}).ncard*Nat.card (Subgroup.center K) := by
  rw [← Set.inter_univ (ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^m = 1})]
  apply filtered_outer_cyclic_quotient_count
  rintro G ⟨N,hn,cyc,idx,⟨e⟩⟩
  let _ : N.Normal := hn
  let _ : IsCyclic (G ⧸ N) := cyc
  obtain ⟨v,hv⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨t,ht⟩ := QuotientGroup.mk'_surjective N v
  exact ⟨N,hn,e,v,t,idx,hv,ht,Set.mem_univ _⟩

private lemma abelian_sylow_count_le_central_lift_count (K : FiniteGrp.{0}) (p a : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ (∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧ Nonempty (K ≃* N)}).ncard := by
  apply Set.ncard_le_ncard (Set.image_mono ?_)
    ((finite_classes ((p^a)*Nat.card K)).subset (Set.image_mono ?_))
  · rintro G ⟨comm,N,hn,cyc,idx,e⟩
    exact ⟨N,hn,cyc,idx,fun P => center_sup_of_commutative (comm P) _,e⟩
  · rintro G ⟨N,_,_,idx,_,⟨e⟩⟩
    change Nat.card G = _
    rw [← N.index_mul_card,idx,Nat.card_congr e.toEquiv]

/-- Count extensions whose Sylow centers supply lifts from the cyclic quotient. -/
lemma central_lift_filtered_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) [(MulAut.conj : K →* MulAut K).range.Normal] :
    let π := QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ (∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧ Nonempty (K ≃* N)}).ncard ≤
      ((ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^(p^a) = 1}) ∩
        ((fun f : MulAut K => ConjClasses.mk (π f)) '' {f | ∀ x ∈ S, f x = x})).ncard
        * Nat.card (Subgroup.center K) := by
  dsimp only
  apply filtered_outer_cyclic_quotient_count
  rintro G ⟨N,hn,cyc,idx,central,⟨e⟩⟩
  let _ : N.Normal := hn
  let _ : IsCyclic (G ⧸ N) := cyc
  obtain ⟨v,hv⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  obtain ⟨t,ht,fixed⟩ := central_sylow_quotient_lift N idx e S.toSubgroup S.isPGroup' central v
  exact ⟨N,hn,e,v,t,idx,hv,ht,_,fixed,rfl⟩

/-- With abelian ambient Sylow p-subgroups, only outer classes represented by an
automorphism fixing the prescribed kernel Sylow subgroup pointwise can occur. -/
lemma abelian_sylow_filtered_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) [(MulAut.conj : K →* MulAut K).range.Normal] :
    let π := QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ P : Sylow p G, IsMulCommutative P) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      ((ConjClasses.mk '' {t : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | t^(p^a) = 1}) ∩
        ((fun f : MulAut K => ConjClasses.mk (π f)) '' {f | ∀ x ∈ S, f x = x})).ncard
        * Nat.card (Subgroup.center K) := by
  exact (abelian_sylow_count_le_central_lift_count K p a).trans (central_lift_filtered_extension_count K a S)

/-- Specifying the images of the generators outside the kernel Sylow subgroup bounds
the realized outer classes in the abelian ambient Sylow case. -/
lemma relative_generator_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) (t : Finset K)
    (gen : S.toSubgroup ⊔ Subgroup.closure (t : Set K) = ⊤) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      Nat.card K ^ t.card * Nat.card (Subgroup.center K) := by
  classical
  let _ := inner_automorphisms_normal K
  let π := QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
  let A := fixingSubgroup (MulAut K) (S : Set K)
  let F (f : A) := ConjClasses.mk (π f.val)
  apply (abelian_sylow_filtered_extension_count K a S).trans
  apply Nat.mul_le_mul_right
  apply le_trans _ (pointwise_stabilizer_relative_generator_bound S.toSubgroup t gen)
  apply le_trans (Set.ncard_le_ncard (t := Set.range F) ?_ (Set.finite_range F))
    (Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := F)))
  rintro _ ⟨_,f,hf,rfl⟩
  exact ⟨⟨f,(mem_fixingSubgroup_iff _).mpr hf⟩,rfl⟩

/-- The Sylow index alone gives a numerical extension bound, including nonsplit extensions. -/
lemma sylow_index_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      Nat.card K ^ Nat.log 2 S.toSubgroup.index * Nat.card (Subgroup.center K) := by
  obtain ⟨t,gen,size⟩ := exists_relative_generators_le_log_index S.toSubgroup
  exact (relative_generator_extension_count K a S t gen).trans
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right Nat.card_pos size))

lemma eligible_cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ (ConjClasses.mk '' {t : MulAut K | ∃ b, MulAut.conj b = t^m}).ncard*Nat.card (Subgroup.center K) := by
  let _ := inner_automorphisms_normal K
  exact (outer_cyclic_quotient_count K m).trans (Nat.mul_le_mul_right _ (outer_classes_le_eligible K m))

/-- In a finite cyclic group the classes killed by m are bounded by gcd(|O|,m). -/
lemma cyclic_outer_class_bound (O : Type*) [Group O] [Finite O] [IsCyclic O] (m : ℕ) :
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤ (Nat.card O).gcd m := by
  classical
  let _ : CommGroup O := IsCyclic.commGroup
  apply (Set.ncard_image_le (Set.toFinite _)).trans_eq
  exact IsCyclic.card_powMonoidHom_ker (G := O) m

/-- A cyclic outer automorphism group has precisely gcd(|Out K|,m) elements killed by m. -/
lemma cyclic_outer_fixed_kernel_count (K : FiniteGrp.{0}) (m : ℕ)
    [(MulAut.conj : K →* MulAut K).range.Normal]
    [IsCyclic (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤
      (MulAut.conj : K →* MulAut K).range.index.gcd m * Nat.card (Subgroup.center K) := by
  exact (outer_cyclic_quotient_count K m).trans
    (Nat.mul_le_mul_right _ (cyclic_outer_class_bound _ m))

/-- Nontrivial kernels with cyclic outer automorphism group always fit the
coefficient-two induction budget for a nontrivial cyclic quotient. -/
lemma cyclic_outer_induction_budget (K : Type*) [Group K] [Finite K] (m : ℕ)
    [(MulAut.conj : K →* MulAut K).range.Normal]
    [IsCyclic (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)]
    (hm : 1 < m) (hk : 1 < Nat.card K) :
    (ConjClasses.mk '' {x : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | x^m = 1}).ncard *
      Nat.card (Subgroup.center K) ≤ Nat.card K^(2 * Nat.log 2 m + 1) := by
  have d : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ m by omega))
  have cost : m ≤ Nat.card K^(2 * Nat.log 2 m) := calc
    m ≤ 2^(Nat.log 2 m + 1) := (Nat.lt_pow_succ_log_self (by decide) m).le
    _ ≤ 2^(2 * Nat.log 2 m) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ _ := Nat.pow_le_pow_left hk _
  rw [pow_succ]
  exact Nat.mul_le_mul (((cyclic_outer_class_bound _ m).trans (Nat.gcd_le_right _ (by omega))).trans cost)
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- Count m-torsion using the quotient by m-th powers, which has the same
cardinality as the kernel and is generated by at most rank(A) elements. -/
lemma abelian_torsion_rank_count (A : Type*) [CommGroup A] [Finite A] {m : ℕ} (hm : 0 < m) :
    Nat.card {x : A // x^m = 1} ≤ m ^ Group.rank A := by
  let f := powMonoidHom (α := A) m
  let Q := A ⧸ f.range
  have card : Nat.card f.ker = Nat.card Q := (Subgroup.index_range (f := f)).symm
  have torsion (x : Q) : x^m = 1 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective f.range x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨a,rfl⟩
  change Nat.card f.ker ≤ _
  rw [card]
  exact (Nat.le_of_dvd (pow_pos hm _) (card_dvd_exponent_pow_rank' Q torsion)).trans
    (Nat.pow_le_pow_right hm (Group.rank_le_of_surjective _ (QuotientGroup.mk'_surjective f.range)))

/-- Replacing m by its gcd with the exponent preserves all m-torsion. -/
lemma abelian_torsion_gcd_rank_count (A : Type*) [CommGroup A] [Finite A] {m : ℕ} (hm : 0 < m) :
    Nat.card {x : A // x^m = 1} ≤ (m.gcd (Monoid.exponent A))^Group.rank A := by
  let d := m.gcd (Monoid.exponent A)
  have sub : {x : A | x^m = 1} ⊆ {x : A | x^d = 1} := fun x hx =>
    orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (Monoid.order_dvd_exponent x))
  exact (Set.ncard_le_ncard sub).trans (abelian_torsion_rank_count A (Nat.gcd_pos_of_pos_left _ hm))

/-- Only the common part of m and the exponent of an abelian outer group
contributes to its admissible conjugacy classes. -/
lemma abelian_outer_class_bound (O : Type*) [Group O] [Finite O] [IsMulCommutative O]
    {m : ℕ} (hm : 0 < m) :
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤ (m.gcd (Monoid.exponent O)) ^ Group.rank O := by
  let _ : CommGroup O := { (inferInstance : Group O) with mul_comm := IsMulCommutative.is_comm.comm }
  exact (Set.ncard_image_le (Set.toFinite _)).trans (abelian_torsion_gcd_rank_count O hm)

/-- Cyclic quotient extensions with an abelian outer automorphism group.
The estimate applies to every positive quotient order, including nonsplit extensions. -/
lemma abelian_outer_fixed_kernel_count (K : FiniteGrp.{0}) {m : ℕ} (hm : 0 < m)
    [(MulAut.conj : K →* MulAut K).range.Normal]
    [IsMulCommutative (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤
      let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
      (m.gcd (Monoid.exponent O))^Group.rank O * Nat.card (Subgroup.center K) := by
  exact (outer_cyclic_quotient_count K m).trans (Nat.mul_le_mul_right _ (abelian_outer_class_bound _ hm))

/-- Above a fixed quotient element, any two lifts killed by m differ by
an m-torsion element of the central subgroup. -/
lemma central_power_fiber_bound (G : Type*) [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (central : A ≤ Subgroup.center G) (m : ℕ) (y : G ⧸ A) :
    Nat.card {x : G // QuotientGroup.mk' A x = y ∧ x^m = 1} ≤
      Nat.card {a : A // a^m = 1} := by
  classical
  let X := {x : G // QuotientGroup.mk' A x = y ∧ x^m = 1}
  by_cases inhabited : Nonempty X
  · let b := inhabited.some
    let diff (x : X) : A := ⟨x.val / b.val, QuotientGroup.eq_iff_div_mem.mp
      (x.property.1.trans b.property.1.symm)⟩
    have prod (x : X) : (diff x).val * b.val = x.val := div_mul_cancel _ _
    have power (x : X) : (diff x)^m = 1 := by
      apply Subtype.ext
      change (diff x).val^m = 1
      have comm : Commute (diff x).val b.val :=
        (Subgroup.mem_center_iff.mp (central (diff x).property) b.val).symm
      have eq := comm.mul_pow m
      rw [prod,x.property.2,b.property.2,mul_one] at eq
      exact eq.symm
    let f (x : X) : {a : A // a^m = 1} := ⟨diff x,power x⟩
    apply Nat.card_le_card_of_injective f
    intro x z eq
    have h : (diff x).val = (diff z).val := congrArg (fun u : {a : A // a^m = 1} => u.val.val) eq
    exact Subtype.ext ((prod x).symm.trans ((congrArg (· * b.val) h).trans (prod z)))
  · let _ : IsEmpty X := not_nonempty_iff.mp inhabited
    change Nat.card X ≤ _
    simp

/-- Central lifting costs at most the m-torsion of the central subgroup
per eligible conjugacy class of the quotient, even for nonsplit extensions. -/
lemma central_torsion_class_lift (G : Type*) [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (central : A ≤ Subgroup.center G) (m : ℕ) :
    (ConjClasses.mk '' {x : G | x^m = 1}).ncard ≤
      (ConjClasses.mk '' {y : G ⧸ A | y^m = 1}).ncard * Nat.card {a : A // a^m = 1} := by
  classical
  let π := QuotientGroup.mk' A
  let C := ConjClasses.mk '' {y : G ⧸ A | y^m = 1}
  let _ : Finite (ConjClasses (G ⧸ A)) := Finite.of_surjective _ ConjClasses.mk_surjective
  let _ : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  let _ := Fintype.ofFinite C
  let rep (c : C) := c.property.choose
  let S (c : C) := ConjClasses.mk '' {x : G | π x = rep c ∧ x^m = 1}
  have cover : ConjClasses.mk '' {x : G | x^m = 1} ⊆ ⋃ c : C, S c := by
    rintro _ ⟨x,hx,rfl⟩
    have hp : (π x)^m = 1 := by rw [← map_pow,show x^m = 1 from hx,map_one]
    let c : C := ⟨_,π x,hp,rfl⟩
    have eq : ConjClasses.mk (π x) = ConjClasses.mk (rep c) := c.property.choose_spec.2.symm
    obtain ⟨v,hv⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp eq)
    obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective A v
    let z := MulAut.conj u x
    have proj : π z = rep c := by
      change π (u*x*u⁻¹) = _
      rw [map_mul,map_mul,map_inv,show π u = v from hu,hv]
    have hz : z^m = 1 := by change (MulAut.conj u x)^m = 1; rw [← map_pow,show x^m = 1 from hx,map_one]
    exact Set.mem_iUnion.mpr ⟨c,z,⟨proj,hz⟩,(ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨u,rfl⟩)).symm⟩
  calc
    _ ≤ (⋃ c : C, S c).ncard := Set.ncard_le_ncard cover
    _ ≤ ∑ c : C, (S c).ncard := Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _ : C, Nat.card {a : A // a^m = 1} := Finset.sum_le_sum fun c _ =>
      (Set.ncard_image_le (Set.toFinite _)).trans (central_power_fiber_bound G A central m (rep c))
    _ = _ := by change _ = Nat.card C * _; simp [Nat.card_eq_fintype_card]

/-- A central subgroup of order coprime to m preserves the number of conjugacy
classes killed by m. A lift can be corrected by a central m-th root. -/
lemma central_coprime_torsion_class_count (G : Type*) [Group G] [Finite G] (A : Subgroup G)
    [A.Normal] (central : A ≤ Subgroup.center G) (m : ℕ) (cop : (Nat.card A).Coprime m) :
    (ConjClasses.mk '' {x : G | x^m = 1}).ncard =
      (ConjClasses.mk '' {y : G ⧸ A | y^m = 1}).ncard := by
  classical
  let π := QuotientGroup.mk' A
  let S := ConjClasses.mk '' {x : G | x^m = 1}
  let _ : Finite (ConjClasses G) := Finite.of_surjective _ ConjClasses.mk_surjective
  apply Nat.le_antisymm
  · have h : {a : A | a^m = 1} = {1} := by
      ext a
      change a^m = 1 ↔ a = 1
      constructor
      · intro ha
        apply (powCoprime cop).injective
        simpa only [powCoprime_apply,one_pow] using ha
      · rintro rfl
        exact one_pow _
    have one : Nat.card {a : A // a^m = 1} = 1 := by
      change {a : A | a^m = 1}.ncard = 1
      rw [h,Set.ncard_singleton]
    simpa only [one,mul_one] using central_torsion_class_lift G A central m
  · have sub : ConjClasses.mk '' {y : G ⧸ A | y^m = 1} ⊆ ConjClasses.map π '' S := by
      rintro _ ⟨y,hy,rfl⟩
      obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective A y
      have mem : x^m ∈ A := (QuotientGroup.eq_one_iff _).mp (by
        change π (x^m) = 1
        rw [map_pow,show π x = y from hx]; exact hy)
      let t : A := ⟨x^m,mem⟩
      obtain ⟨b,hb⟩ := (powCoprime cop).surjective t⁻¹
      have root : b.val^m = (x^m)⁻¹ := congrArg Subtype.val hb
      have comm : Commute b.val x := (Subgroup.mem_center_iff.mp (central b.property) x).symm
      have lifted : (b.val*x)^m = 1 := by rw [comm.mul_pow,root,inv_mul_cancel]
      have same : π (b.val*x) = y := by
        have z : π b.val = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
        rw [map_mul,z,one_mul]; exact hx
      exact ⟨_,⟨b.val*x,lifted,rfl⟩,congrArg ConjClasses.mk same⟩
    exact (Set.ncard_le_ncard sub ((Set.toFinite S).image _)).trans (Set.ncard_image_le (Set.toFinite S))

/-- For a central-by-abelian group the two torsion factors can be bounded
separately, retaining their individual exponents. -/
lemma class_two_outer_class_bound (O : Type*) [Group O] [Finite O] (m : ℕ) (hm : 0 < m)
    [IsMulCommutative (O ⧸ Subgroup.center O)] :
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤
      (m.gcd (Monoid.exponent (O ⧸ Subgroup.center O)))^Group.rank (O ⧸ Subgroup.center O) *
      (m.gcd (Monoid.exponent (Subgroup.center O)))^Group.rank (Subgroup.center O) := by
  let Z := Subgroup.center O
  let _ : CommGroup Z := { (inferInstance : Group Z) with mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp a.property b.val).symm }
  exact (central_torsion_class_lift O Z le_rfl m).trans
    (Nat.mul_le_mul (abelian_outer_class_bound _ hm) (abelian_torsion_gcd_rank_count Z hm))

/-- Fixed kernel and cyclic quotient with a class-at-most-two outer automorphism group. -/
lemma class_two_outer_fixed_kernel_count (K : FiniteGrp.{0}) {m : ℕ} (hm : 0 < m)
    [(MulAut.conj : K →* MulAut K).range.Normal]
    (comm : let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
            IsMulCommutative (O ⧸ Subgroup.center O)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤
      let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
      let Z := Subgroup.center O
      ((m.gcd (Monoid.exponent (O ⧸ Z)))^Group.rank (O ⧸ Z) *
        (m.gcd (Monoid.exponent Z))^Group.rank Z) * Nat.card (Subgroup.center K) := by
  let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
  let _ : IsMulCommutative (O ⧸ Subgroup.center O) := comm
  exact (outer_cyclic_quotient_count K m).trans (Nat.mul_le_mul_right _ (class_two_outer_class_bound O m hm))

/-- Transport the count of conjugacy classes killed by m through a group isomorphism. -/
lemma torsion_class_count_congr {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) (m : ℕ) :
    (ConjClasses.mk '' {x : G | x^m = 1}).ncard = (ConjClasses.mk '' {x : H | x^m = 1}).ncard := by
  classical
  have bound {X Y : Type u} [Group X] [Group Y] [Finite X] (f : X ≃* Y) :
      (ConjClasses.mk '' {y : Y | y^m = 1}).ncard ≤ (ConjClasses.mk '' {x : X | x^m = 1}).ncard := by
    let _ : Finite (ConjClasses X) := Finite.of_surjective _ ConjClasses.mk_surjective
    let S := ConjClasses.mk '' {x : X | x^m = 1}
    have sub : ConjClasses.mk '' {y : Y | y^m = 1} ⊆ ConjClasses.map f.toMonoidHom '' S := by
      rintro _ ⟨y,hy,rfl⟩
      have hx : (f.symm y)^m = 1 := by rw [← map_pow,show y^m = 1 from hy,map_one]
      exact ⟨_,⟨f.symm y,hx,rfl⟩,congrArg ConjClasses.mk (f.apply_symm_apply y)⟩
    exact (Set.ncard_le_ncard sub ((Set.toFinite S).image _)).trans (Set.ncard_image_le (Set.toFinite S))
  exact Nat.le_antisymm (bound e.symm) (bound e)

/-- Removing the center of an upper-central quotient advances the series by one. -/
private lemma upper_central_successor_equiv (O : Type*) [Group O] (n : ℕ) :
    let Q (i : ℕ) := O ⧸ Subgroup.upperCentralSeries O i
    Nonempty ((Q n ⧸ Subgroup.center (Q n)) ≃* Q (n+1)) := by
  let U := Subgroup.upperCentralSeries O
  let Q (i : ℕ) := O ⧸ U i
  let Z (i : ℕ) := Subgroup.center (Q i)
  have step : U (n+1) = (Z n).comap (QuotientGroup.mk' (U n)) :=
    Subgroup.upperCentralSeriesStep_eq_comap_center (U n)
  have mapped : (U (n+1)).map (QuotientGroup.mk' (U n)) = Z n := by
    rw [step,Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
  have le : U n ≤ U (n+1) := by
    rw [step]
    intro x hx
    change QuotientGroup.mk' (U n) x ∈ Z n
    rw [show QuotientGroup.mk' (U n) x = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
    exact (Z n).one_mem
  let e : Q n ⧸ Z n ≃* Q (n+1) :=
    (QuotientGroup.quotientMulEquivOfEq mapped.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient (U n) (U (n+1)) le)
  exact ⟨e⟩

/-- The upper central series gives a product bound up to any depth. The unprocessed
quotient stays explicit, so the estimate also applies when the series does not exhaust O. -/
lemma upper_central_torsion_partial (O : Type u) [Group O] [Finite O] {m : ℕ} (hm : 0 < m) (n : ℕ) :
    let Q (i : ℕ) := O ⧸ Subgroup.upperCentralSeries O i
    let Z (i : ℕ) := Subgroup.center (Q i)
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤
      (ConjClasses.mk '' {x : Q n | x^m = 1}).ncard *
        ∏ i ∈ Finset.range n, (m.gcd (Monoid.exponent (Z i)))^Group.rank (Z i) := by
  classical
  let U := Subgroup.upperCentralSeries O
  let Q (i : ℕ) := O ⧸ U i
  let Z (i : ℕ) := Subgroup.center (Q i)
  let b (X : Type u) [Group X] := (ConjClasses.mk '' {x : X | x^m = 1}).ncard
  let weight (i : ℕ) := (m.gcd (Monoid.exponent (Z i)))^Group.rank (Z i)
  change b O ≤ b (Q n) * ∏ i ∈ Finset.range n, weight i
  induction n with
  | zero =>
    rw [Finset.prod_range_zero,mul_one]
    exact (torsion_class_count_congr (QuotientGroup.quotientBot (G := O)) m).symm.le
  | succ n ih =>
    obtain ⟨e⟩ := upper_central_successor_equiv O n
    let _ : CommGroup (Z n) := { (inferInstance : Group (Z n)) with
      mul_comm := fun a c => Subtype.ext (Subgroup.mem_center_iff.mp a.property c.val).symm }
    have layer : b (Q n) ≤ b (Q (n+1)) * weight n := by
      have h := central_torsion_class_lift (Q n) (Z n) le_rfl m
      rw [torsion_class_count_congr e m] at h
      exact h.trans (Nat.mul_le_mul_left _ (abelian_torsion_gcd_rank_count (Z n) hm))
    exact ih.trans ((Nat.mul_le_mul_right _ layer).trans_eq (by rw [Finset.prod_range_succ]; ring))

/-- An initial segment of central layers of orders coprime to m may be
removed without changing the eligible-class count. -/
lemma upper_central_coprime_class_count (O : Type u) [Group O] [Finite O] (m n : ℕ)
    (cop : ∀ i < n, (Nat.card (Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i))).Coprime m) :
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard =
      (ConjClasses.mk '' {x : O ⧸ Subgroup.upperCentralSeries O n | x^m = 1}).ncard := by
  let Q (i : ℕ) := O ⧸ Subgroup.upperCentralSeries O i
  let b (X : Type u) [Group X] := (ConjClasses.mk '' {x : X | x^m = 1}).ncard
  change b O = b (Q n)
  induction n with
  | zero => exact (torsion_class_count_congr (QuotientGroup.quotientBot (G := O)) m).symm
  | succ n ih =>
    obtain ⟨e⟩ := upper_central_successor_equiv O n
    calc
      b O = b (Q n) := ih (fun i hi => cop i (by omega))
      _ = b (Q n ⧸ Subgroup.center (Q n)) :=
        central_coprime_torsion_class_count (Q n) _ le_rfl m (cop n (by omega))
      _ = b (Q (n+1)) := torsion_class_count_congr e m

/-- Once the upper central series reaches the group, the last quotient has one class. -/
lemma nilpotent_outer_series_count (O : Type*) [Group O] [Finite O] [Group.IsNilpotent O]
    {m : ℕ} (hm : 0 < m) :
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤
      ∏ i ∈ Finset.range (Group.nilpotencyClass O),
        let Z := Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i)
        (m.gcd (Monoid.exponent Z))^Group.rank Z := by
  classical
  let n := Group.nilpotencyClass O
  let Q := O ⧸ Subgroup.upperCentralSeries O n
  have trivial : Subsingleton Q := by
    dsimp [Q,n]; rw [Subgroup.upperCentralSeries_nilpotencyClass]
    exact QuotientGroup.subsingleton_quotient_top
  have one : (ConjClasses.mk '' {x : Q | x^m = 1}).ncard ≤ 1 := by
    apply (Set.ncard_image_le (Set.toFinite _)).trans
    exact Set.ncard_le_one_iff_subsingleton.mpr (fun _ _ _ _ => Subsingleton.elim ..)
  apply (upper_central_torsion_partial O hm n).trans
  exact (Nat.mul_le_mul_right _ one).trans_eq (one_mul _)

/-- Layers whose exponent is coprime to m cost no rank in the cyclic-quotient induction. -/
lemma nilpotent_outer_active_rank_bound (O : Type*) [Group O] [Finite O] [Group.IsNilpotent O]
    {m : ℕ} (hm : 0 < m) :
    let Z (i : ℕ) := Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i)
    (ConjClasses.mk '' {x : O | x^m = 1}).ncard ≤
      m^(∑ i ∈ Finset.range (Group.nilpotencyClass O),
        if m.Coprime (Monoid.exponent (Z i)) then 0 else Group.rank (Z i)) := by
  classical
  let Z (i : ℕ) := Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i)
  apply (nilpotent_outer_series_count O hm).trans
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod'
  intro i _
  change (m.gcd (Monoid.exponent (Z i)))^Group.rank (Z i) ≤ m^(if m.Coprime (Monoid.exponent (Z i)) then 0 else Group.rank (Z i))
  by_cases cop : m.Coprime (Monoid.exponent (Z i))
  · rw [show m.gcd (Monoid.exponent (Z i)) = 1 from cop,if_pos cop,one_pow,pow_zero]
  · simp only [if_neg cop]
    exact Nat.pow_le_pow_left (Nat.gcd_le_left _ hm) _

/-- Fixed-kernel extension count for nilpotent outer automorphism groups of arbitrary class. -/
lemma nilpotent_outer_fixed_kernel_count (K : FiniteGrp.{0}) {m : ℕ} (hm : 0 < m)
    [(MulAut.conj : K →* MulAut K).range.Normal]
    [Group.IsNilpotent (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤
      let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
      (∏ i ∈ Finset.range (Group.nilpotencyClass O),
        let Z := Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i)
        (m.gcd (Monoid.exponent Z))^Group.rank Z) * Nat.card (Subgroup.center K) :=
  (outer_cyclic_quotient_count K m).trans (Nat.mul_le_mul_right _ (nilpotent_outer_series_count _ hm))

/-- Inclusion of any Sylow subgroup covers the ambient classes killed by a power of its prime. -/
lemma prime_power_torsion_classes_le_sylow (G : Type*) [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (a : ℕ) :
    (ConjClasses.mk '' {x : G | x^(p^a) = 1}).ncard ≤
      (ConjClasses.mk '' {x : P | x^(p^a) = 1}).ncard := by
  classical
  let _ : Finite (ConjClasses P) := Finite.of_surjective _ ConjClasses.mk_surjective
  let S := ConjClasses.mk '' {x : P | x^(p^a) = 1}
  have covers : ConjClasses.mk '' {x : G | x^(p^a) = 1} ⊆
      ConjClasses.map P.toSubgroup.subtype '' S := by
    rintro _ ⟨x,hx,rfl⟩
    have hp : IsPGroup p (Subgroup.zpowers x) := IsPGroup.of_card_dvd_pow
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one (show x^(p^a) = 1 from hx))
    obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G Q P
    have mem : MulAut.conj g x ∈ P := by
      rw [← hg]
      exact ⟨x,hQ (Subgroup.mem_zpowers x),rfl⟩
    let y : P := ⟨MulAut.conj g x,mem⟩
    have hy : y^(p^a) = 1 := by
      apply Subtype.ext
      change (MulAut.conj g x)^(p^a) = 1
      rw [← map_pow,show x^(p^a) = 1 from hx,map_one]
    exact ⟨_,⟨y,hy,rfl⟩,(ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g,rfl⟩)).symm⟩
  exact (Set.ncard_le_ncard covers ((Set.toFinite S).image _)).trans
    (Set.ncard_image_le (Set.toFinite S))

/-- Bound the central-lift extension family using a Sylow subgroup of the outer stabilizer. -/
lemma central_lift_outer_sylow_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) [(MulAut.conj : K →* MulAut K).range.Normal] :
    let π := QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
    let H := (fixingSubgroup (MulAut K) (S : Set K)).map π
    ∀ P : Sylow p H, (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ (∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧ Nonempty (K ≃* N)}).ncard ≤
      (ConjClasses.mk '' {x : P | x^(p^a) = 1}).ncard * Nat.card (Subgroup.center K) := by
  classical
  intro π H P
  apply (central_lift_filtered_extension_count K a S).trans
  apply Nat.mul_le_mul_right
  apply le_trans _ (prime_power_torsion_classes_le_sylow H P a)
  let T := ConjClasses.mk '' {x : H | x^(p^a) = 1}
  let _ : Finite (ConjClasses H) := Finite.of_surjective _ ConjClasses.mk_surjective
  apply le_trans (Set.ncard_le_ncard (t := ConjClasses.map H.subtype '' T) ?_
    ((Set.toFinite T).image _)) (Set.ncard_image_le (Set.toFinite T))
  rintro _ ⟨⟨x,hx,rfl⟩,f,hf,eq⟩
  have conj := (ConjClasses.mk_eq_mk_iff_isConj.mp eq).pow (p^a)
  rw [show x^(p^a) = 1 from hx] at conj
  let y : H := ⟨π f,f,(mem_fixingSubgroup_iff _).mpr hf,rfl⟩
  have hy : y^(p^a) = 1 := Subtype.ext (isConj_one_left.mp conj)
  exact ⟨_,⟨y,hy,rfl⟩,eq⟩

/-- Localize the filtered count to a Sylow subgroup of the image in Out(K) of the
pointwise stabilizer of a kernel Sylow subgroup. -/
lemma pointwise_stabilizer_sylow_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) [(MulAut.conj : K →* MulAut K).range.Normal] :
    let π := QuotientGroup.mk' (MulAut.conj : K →* MulAut K).range
    let H := (fixingSubgroup (MulAut K) (S : Set K)).map π
    ∀ P : Sylow p H, (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      (ConjClasses.mk '' {x : P | x^(p^a) = 1}).ncard * Nat.card (Subgroup.center K) := by
  intro π H P
  exact (abelian_sylow_count_le_central_lift_count K p a).trans (central_lift_outer_sylow_count K a S P)

/-- Bound the central-lift extension family by the p-part of the outer stabilizer order times the kernel center order. -/
lemma central_lift_outer_prime_part_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ (∀ P : Sylow p G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧ Nonempty (K ≃* N)}).ncard ≤
      p ^ ((MulAut.conj : K →* MulAut K).range.subgroupOf
              (fixingSubgroup (MulAut K) (S : Set K))).index.factorization p *
        Nat.card (Subgroup.center K) := by
  classical
  let _ := inner_automorphisms_normal K
  let I := (MulAut.conj : K →* MulAut K).range
  let π := QuotientGroup.mk' I
  let A := fixingSubgroup (MulAut K) (S : Set K)
  let f := π.subgroupMap A
  let Q : Sylow p (A.map π) := default
  have ker : f.ker = I.subgroupOf A := by
    rw [show f = π.subgroupMap A from rfl, Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have index : (I.subgroupOf A).index = Nat.card (A.map π) := by
    rw [← ker,Subgroup.index_ker,MonoidHom.range_eq_top.mpr (π.subgroupMap_surjective A),Subgroup.card_top]
  apply (central_lift_outer_sylow_count K a S Q).trans
  apply Nat.mul_le_mul_right
  rw [index,← Q.card_eq_multiplicity]
  exact (Set.ncard_image_le (Set.toFinite _)).trans
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- The index of the inner automorphisms in the pointwise stabilizer equals its
outer image order. Only the p-part of that index enters this extension count. -/
lemma outer_stabilizer_prime_part_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      p ^ ((MulAut.conj : K →* MulAut K).range.subgroupOf
              (fixingSubgroup (MulAut K) (S : Set K))).index.factorization p *
        Nat.card (Subgroup.center K) := by
  exact (abelian_sylow_count_le_central_lift_count K p a).trans (central_lift_outer_prime_part_count K a S)

private lemma prime_part_index_le {A : Type*} [Group A] [Finite A] (U : Subgroup A)
    {p : ℕ} (hp : p.Prime) : p ^ U.index.factorization p ≤ p ^ (Nat.card A).factorization p := by
  have dvd := U.index_dvd_card
  exact Nat.pow_le_pow_right hp.pos ((Nat.factorization_le_iff_dvd
    (Subgroup.index_ne_zero_of_finite (H := U)) Nat.card_pos.ne').mpr dvd p)

/-- For prime-power cyclic quotients with abelian ambient Sylow p-subgroups only
the p-part of the pointwise stabilizer order contributes to the action count. -/
lemma stabilizer_prime_part_extension_count (K : FiniteGrp.{0}) {p : ℕ} [Fact p.Prime]
    (a : ℕ) (S : Sylow p K) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | (∀ Q : Sylow p G, IsMulCommutative Q) ∧
        ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      p ^ (Nat.card (fixingSubgroup (MulAut K) (S : Set K))).factorization p *
        Nat.card (Subgroup.center K) := by
  apply (outer_stabilizer_prime_part_extension_count K a S).trans
  exact Nat.mul_le_mul_right _ (prime_part_index_le _ Fact.out)

/-- Prime-power cyclic extensions, including nonsplit ones, cost only the central layers
of one Sylow subgroup of the outer automorphism group and the center of the kernel. -/
lemma prime_power_outer_sylow_fixed_kernel_count (K : FiniteGrp.{0}) {p : ℕ}
    [hp : Fact p.Prime] (a : ℕ) [(MulAut.conj : K →* MulAut K).range.Normal]
    (P : Sylow p (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = p^a ∧ Nonempty (K ≃* N)}).ncard ≤
      (∏ i ∈ Finset.range (Group.nilpotencyClass P),
        let Z := Subgroup.center (P ⧸ Subgroup.upperCentralSeries P i)
        ((p^a).gcd (Monoid.exponent Z))^Group.rank Z) * Nat.card (Subgroup.center K) := by
  let _ : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  apply (outer_cyclic_quotient_count K (p^a)).trans
  exact Nat.mul_le_mul_right _ ((prime_power_torsion_classes_le_sylow _ P a).trans
    (nilpotent_outer_series_count P (pow_pos hp.out.pos a)))

private lemma cyclic_rank_power_budget {k m t c : ℕ} (hk : 0 < k) (hm : 1 < m)
    (rk : t ≤ c * Nat.log 2 k) : m^t ≤ k^((2*c)*Nat.log 2 m) := by
  have d : 1 ≤ Nat.log 2 m := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ m by omega))
  have size : m ≤ 2^(2 * Nat.log 2 m) := (Nat.lt_pow_succ_log_self (by decide) m).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  calc
    _ ≤ (2^(2 * Nat.log 2 m))^(c * Nat.log 2 k) :=
      (Nat.pow_le_pow_left size _).trans (Nat.pow_le_pow_right (by positivity) rk)
    _ = (2^Nat.log 2 k)^((2*c)*Nat.log 2 m) := by rw [← pow_mul,← pow_mul]; congr 1; ring
    _ ≤ _ := Nat.pow_le_pow_left (Nat.pow_log_le_self _ hk.ne') _

/-- A rank bound proportional to log₂ |K| is sufficient for the cyclic-quotient
induction. The proportionality constant is uniform across orders. -/
lemma abelian_outer_induction_budget (K : Type*) [Group K] [Finite K] {m c : ℕ}
    [(MulAut.conj : K →* MulAut K).range.Normal]
    [IsMulCommutative (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range)]
    (hm : 1 < m) (rk : Group.rank (MulAut K ⧸ (MulAut.conj : K →* MulAut K).range) ≤ c * Nat.log 2 (Nat.card K)) :
    (ConjClasses.mk '' {x : MulAut K ⧸ (MulAut.conj : K →* MulAut K).range | x^m = 1}).ncard *
      Nat.card (Subgroup.center K) ≤ Nat.card K^((2*c) * Nat.log 2 m + 1) := by
  let O := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range
  have budget := cyclic_rank_power_budget (k := Nat.card K) Nat.card_pos hm rk
  rw [pow_succ]
  exact Nat.mul_le_mul (((abelian_outer_class_bound O (by omega : 0 < m)).trans
    (Nat.pow_le_pow_left (Nat.gcd_le_left _ (by omega)) _)).trans budget)
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- Coprime quotient order forces the trivial outer action. -/
lemma coprime_outer_center_count (K : FiniteGrp.{0}) (m : ℕ)
    (cop : m.Coprime (MulAut.conj : K →* MulAut K).range.index) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card (Subgroup.center K) := by
  classical
  let I := (MulAut.conj : K →* MulAut K).range
  let _ : I.Normal := inner_automorphisms_normal K
  let O := MulAut K ⧸ I
  have sub : {x : O | x^m = 1} ⊆ {1} := by
    intro x hx
    have d := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx) (orderOf_dvd_natCard x)
    rw [show m.gcd (Nat.card O) = 1 from cop] at d
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one d)
  have cnt := (Set.ncard_image_le (f := ConjClasses.mk) (Set.toFinite {x : O | x^m = 1})).trans
    (Set.ncard_le_ncard sub)
  apply (outer_cyclic_quotient_count K m).trans
  simpa using Nat.mul_le_mul_right (Nat.card (Subgroup.center K)) cnt

lemma cyclic_quotient_center_count (K : FiniteGrp.{0}) (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card (ConjClasses (MulAut K))*Nat.card (Subgroup.center K) := by
  classical
  let _ : Finite (ConjClasses (MulAut K)) := Finite.of_surjective _ ConjClasses.mk_surjective
  apply (eligible_cyclic_quotient_count K m).trans
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- If the quotient order is coprime to the outer automorphism group order,
every action with inner m-th power is inner. The whole action/power budget is at most |K|. -/
lemma coprime_outer_action_budget (K : Type*) [Group K] [Finite K] (m : ℕ)
    (cop : m.Coprime (MulAut.conj : K →* MulAut K).range.index) :
    (ConjClasses.mk '' {t : MulAut K | ∃ b, MulAut.conj b = t^m}).ncard *
      Nat.card (Subgroup.center K) ≤ Nat.card K := by
  classical
  let f : K →* MulAut K := MulAut.conj
  let I := f.range
  let _ : I.Normal := ⟨by
    rintro _ ⟨b,rfl⟩ g
    refine ⟨g b,?_⟩
    ext x
    change g b * x * (g b)⁻¹ = g (b * g.symm x * b⁻¹)
    simp⟩
  let π := QuotientGroup.mk' I
  have sub : {t : MulAut K | ∃ b, MulAut.conj b = t^m} ⊆ (I : Set (MulAut K)) := by
    rintro t ⟨b,hb⟩
    have hm : (π t)^m = 1 := by
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr ⟨b,hb⟩
    have d₁ := orderOf_dvd_of_pow_eq_one hm
    have d₂ : orderOf (π t) ∣ I.index := orderOf_dvd_natCard (π t)
    have d := Nat.dvd_gcd d₁ d₂
    rw [show m.gcd I.index = 1 from cop] at d
    exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one d))
  have count : (ConjClasses.mk '' {t : MulAut K | ∃ b, MulAut.conj b = t^m}).ncard ≤ Nat.card I :=
    (Set.ncard_image_le (Set.toFinite _)).trans (Set.ncard_le_ncard sub)
  have ker : f.ker = Subgroup.center K := by
    ext b
    constructor
    · intro hb
      apply Subgroup.mem_center_iff.mpr
      intro y
      have eq := DFunLike.congr_fun (show MulAut.conj b = 1 from hb) y
      exact (mul_inv_eq_iff_eq_mul.mp (show b*y*b⁻¹ = y from eq)).symm
    · intro hb
      change MulAut.conj b = 1
      ext y
      exact mul_inv_eq_iff_eq_mul.mpr ((Subgroup.mem_center_iff.mp hb y).symm)
  apply (Nat.mul_le_mul_right _ count).trans_eq
  change Nat.card f.range * Nat.card (Subgroup.center K) = Nat.card K
  rw [← ker,← Subgroup.index_ker]
  exact f.ker.index_mul_card

/-- For fixed kernel and cyclic quotient of order coprime to the outer automorphism
group order, there are at most |K| isomorphism classes, including nonsplit extensions. -/
lemma coprime_outer_cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ)
    (cop : m.Coprime (MulAut.conj : K →* MulAut K).range.index) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card K :=
  (eligible_cyclic_quotient_count K m).trans (coprime_outer_action_budget K m cop)

/-- For a centerless kernel, one action class suffices to determine at most one extension class. -/
lemma centerless_cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ) [Subsingleton (Subgroup.center K)] :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card (ConjClasses (MulAut K)) := by
  simpa [Nat.card_unique] using cyclic_quotient_center_count K m

lemma cyclic_quotient_conjugacy_count (K : FiniteGrp.{0}) (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card (ConjClasses (MulAut K))*Nat.card K := by
  exact (cyclic_quotient_center_count K m).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective))

/-- Count all cyclic-quotient extensions with specified kernel and quotient order,
allowing every power of a lifted generator that yields a finite extension. -/
lemma cyclic_quotient_count (K : FiniteGrp.{0}) (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card (MulAut K)*Nat.card K := by
  apply (cyclic_quotient_conjugacy_count K m).trans
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_surjective _ ConjClasses.mk_surjective)

/-- Adjoining a cyclic quotient increases the quadratic counting exponent by at most one. -/
theorem cyclic_quotient_family_bound (P : FiniteGrp.{0} → Prop) {q r A : ℕ}
    (family : ∀ n, 0 < n → n < 2^r →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G ∧ P G}).ncard ≤
        2^(A*(r+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) (hq : 0 < q) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        ∃ (N : Subgroup G) (_ : N.Normal), P (FiniteGrp.of N) ∧ IsCyclic (G ⧸ N)}).ncard ≤
      2^((A+1)*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 0 < k.val ∧ k.val ∣ q}
  let O (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G ∧ P G}
  let (n : ℕ) : Finite (O n) := ((finite_classes n).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let K {n : ℕ} (x : O n) : FiniteGrp.{0} := x.property.choose
  have kc {n} (x : O n) : Nat.card (K x) = n := x.property.choose_spec.1.1
  let S (i : I) (x : O i.val.val) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
      N.index = q/i.val.val ∧ Nonempty (K x ≃* N)}
  have finite (i : I) (x : O i.val.val) : (S i x).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨N,_,_,idx,⟨e⟩⟩
    change Nat.card G = q
    rw [← N.index_mul_card,idx,← Nat.card_congr e.toEquiv,kc,Nat.div_mul_cancel i.property.2]))
  have inner (i : I) : (⋃ x : O i.val.val, S i x).ncard ≤ 2^(r*r+A*(r+1)^2+r)*L q := by
    let _ := Fintype.ofFinite (O i.val.val)
    have small : i.val.val < 2^r := (Nat.le_of_dvd hq i.property.2).trans_lt hr
    have action (x : O i.val.val) : (S i x).ncard ≤ 2^(r*r) := by
      let _ : Finite (K x →* K x) := Finite.of_injective (fun g : K x →* K x => (g : K x → K x)) DFunLike.coe_injective
      have aut := (Nat.card_le_card_of_injective MulEquiv.toMonoidHom MulEquiv.toMonoidHom_injective).trans (hom_count (K x) (K x))
      apply (cyclic_quotient_count (K x) _).trans
      apply (Nat.mul_le_mul_right (Nat.card (K x)) aut).trans
      rw [kc,← pow_succ,pow_mul]
      exact (Nat.pow_le_pow_left small.le _).trans (Nat.pow_le_pow_right (by positivity)
        (Nat.log_lt_of_lt_pow i.property.1.ne' small))
    calc
      _ ≤ ∑ x : O i.val.val, (S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : O i.val.val, 2^(r*r) := Finset.sum_le_sum fun x _ => action x
      _ = 2^(r*r)*Nat.card (O i.val.val) := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
      _ ≤ 2^(r*r)*(2^(A*(r+1)^2)*(2^r*L q)) := by
        apply Nat.mul_le_mul_left
        apply (family i.val.val i.property.1 small).trans (Nat.mul_le_mul_left _ _)
        exact (sylow_product_dvd_bound i.property.1 hq i.property.2).trans (Nat.mul_le_mul_right _ hr.le)
      _ = _ := by simp only [pow_add]; ring
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, ⋃ x : O i.val.val, S i x) ?_
    (Set.finite_iUnion fun i => Set.finite_iUnion (finite i))) ?_
  · rintro _ ⟨G,⟨hg,hs,N,hn,prop,cyc⟩,rfl⟩
    let _ : N.Normal := hn
    let _ : Group.IsSolvable G := hs
    have dvd : Nat.card N ∣ q := hg ▸ N.card_subgroup_dvd_card
    let i : I := ⟨⟨Nat.card N,by have := Nat.le_of_dvd hq dvd; omega⟩,Nat.card_pos,dvd⟩
    let x : O i.val.val := ⟨Quotient.mk _ (FiniteGrp.of N),FiniteGrp.of N,⟨rfl,inferInstanceAs (Group.IsSolvable N),prop⟩,rfl⟩
    have rep : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K x) = Quotient.mk _ (FiniteGrp.of N) := x.property.choose_spec.2
    let e := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact rep))).groupIsoToMulEquiv
    have eq : N.index = q/Nat.card N := by rw [← hg,← N.index_mul_card,Nat.mul_div_cancel _ Nat.card_pos]
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x,G,⟨N,hn,cyc,eq,⟨e⟩⟩,rfl⟩⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (⋃ x : O i.val.val, S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(r*r+A*(r+1)^2+r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^(r*r+A*(r+1)^2+r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^(r*r+A*(r+1)^2+r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by rw [← mul_assoc,← pow_add]; apply Nat.mul_le_mul_right; apply Nat.pow_le_pow_right (by decide); nlinarith

/-- Sum the cyclic-quotient extension count over nilpotent kernels of every possible order. -/
theorem nilpotent_by_cyclic_sharp_count {q r : ℕ} (hq : 0 < q) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        ∃ (N : Subgroup G) (_ : N.Normal), Group.IsNilpotent N ∧ IsCyclic (G ⧸ N)}).ncard ≤
      2^((r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  have bound := cyclic_quotient_family_bound
    (fun G => Group.IsNilpotent G) (A := 0) (fun n _ _ => by simpa using nilpotent_bound n) hq hr
  rw [zero_add,one_mul] at bound
  exact bound

/-- Sum the cyclic-quotient extension count over nilpotent kernels of every possible order. -/
theorem nilpotent_by_cyclic_count {q r : ℕ} (hq : 0 < q) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        ∃ (N : Subgroup G) (_ : N.Normal), Group.IsNilpotent N ∧ IsCyclic (G ⧸ N)}).ncard ≤
      2^(2*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  apply (nilpotent_by_cyclic_sharp_count hq hr).trans
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- Count groups with a nilpotent subgroup beneath two successive cyclic quotients. -/
theorem two_cyclic_layers_count {q r : ℕ} (hq : 0 < q) (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        ∃ (N : Subgroup G) (_ : N.Normal), (∃ (M : Subgroup N) (_ : M.Normal), Group.IsNilpotent M ∧ IsCyclic (N ⧸ M)) ∧ IsCyclic (G ⧸ N)}).ncard ≤
      2^(2*(r+1)^2) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  apply cyclic_quotient_family_bound (fun G => ∃ (N : Subgroup G) (_ : N.Normal), Group.IsNilpotent N ∧ IsCyclic (G ⧸ N)) (A := 1) _ hq hr
  intro n hn hnr
  simpa using nilpotent_by_cyclic_sharp_count hn hnr

theorem cyclic_kernel_induction_reserve {q r E : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ 1 < Nat.card P)}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 1 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q}
  let S (i : I) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧
      Nat.card N = q/i.val.val ∧ Nat.card P = i.val.val ∧ Group.IsSolvable (FiniteGrp.of N)}
  have fin (i : I) : (S i).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨N,P,_,comp,_,hn,hp,_⟩
    exact comp.card_mul_card.symm.trans (by rw [hn,hp,Nat.mul_comm]; exact i.property.2.2)))
  have inner (i : I) : (S i).ncard ≤ 2^(E*(r+1)^2-6-r)*L q := by
    let k := i.val.val
    let h := q/k
    let d := Nat.log 2 k
    have hk : 1 < k := i.property.1
    have hh : 0 < h := i.property.2.1
    have eq : k*h = q := i.property.2.2
    have small : h < q := by rw [← eq]; nlinarith
    have dpos : 1 ≤ d := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ k by omega))
    have kd : 2^d ≤ k := Nat.pow_log_le_self _ (by omega)
    have dr : d ≤ r := (Nat.log_lt_of_lt_pow (by omega) ((Nat.le_mul_of_pos_right k hh).trans_lt (eq ▸ hr))).le
    let s := r-d
    have split : s+d = r := Nat.sub_add_cancel dr
    have shr : h < 2^s := by
      by_contra! bad
      have z := Nat.mul_le_mul kd bad
      rw [← pow_add, Nat.add_comm d s, split, eq] at z
      omega
    have budget : r + ((d+1)*r + r + E*(s+1)^2) + 6 ≤ E*(r+1)^2 := by
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le dpos
      obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le hE
      rw [← split,hj,hc]; ring_nf; omega
    have dvd : h ∣ q := ⟨k,by rw [← eq,Nat.mul_comm]⟩
    have ch := ih h small s (odd.of_dvd_nat dvd) shr
    have pad := sylow_product_dvd_bound hh odd.pos dvd
    have action : k^(Nat.log 2 h) ≤ 2^((d+1)*r) := by
      rw [pow_mul]
      exact (Nat.pow_le_pow_left (Nat.lt_pow_succ_log_self (by decide) k).le _).trans
        (Nat.pow_le_pow_right (by positivity) (Nat.log_lt_of_lt_pow hh.ne' (small.trans hr)).le)
    calc
      _ ≤ _ := cyclic_kernel_count (by omega : 0 < k) (fun G => Group.IsSolvable G)
      _ ≤ (2^(E*(s+1)^2)*L h)*2^((d+1)*r) := Nat.mul_le_mul ch action
      _ ≤ (2^(E*(s+1)^2)*(2^r*L q))*2^((d+1)*r) := by
        apply Nat.mul_le_mul_right
        apply Nat.mul_le_mul_left
        exact pad.trans (Nat.mul_le_mul_right _ hr.le)
      _ = 2^((d+1)*r+r+E*(s+1)^2)*L q := by simp only [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, S i) ?_ (Set.finite_iUnion fin)) ?_
  · rintro _ ⟨G,⟨hg,hs,N,P,norm,comp,cyc,big⟩,rfl⟩
    let _ : Group.IsSolvable G := hs
    have eq := comp.card_mul_card.trans hg
    have le := (Nat.le_mul_of_pos_left (Nat.card P) (Nat.card_pos (α := N))).trans eq.le
    have div : q/Nat.card P = Nat.card N := by rw [← eq,Nat.mul_div_cancel _ Nat.card_pos]
    let i : I := ⟨⟨Nat.card P,by omega⟩,big,div.symm ▸ Nat.card_pos,by simpa only [div,Nat.mul_comm] using eq⟩
    exact Set.mem_iUnion.mpr ⟨i,G,⟨N,P,norm,comp,cyc,div.symm,rfl,inferInstanceAs (Group.IsSolvable N)⟩,rfl⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (S i).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(E*(r+1)^2-6-r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^(E*(r+1)^2-6-r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^(E*(r+1)^2-6-r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by
        rw [← mul_assoc,← pow_add]
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        have := Nat.mul_le_mul_right ((r+1)^2) hE
        have : r+6 ≤ 6*(r+1)^2 := by nlinarith
        omega


theorem solvable_cyclic_induction_step {q r E : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ 1 < Nat.card P)}).ncard ≤
      2^(E*(r+1)^2-5) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply (cyclic_kernel_induction_reserve hr odd hE ih).trans
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))

/-- A pair of factor classes determines its product class. This complements the
coprime product recovery argument in PR #12823. -/
lemma product_class_count (k h : ℕ) (P Q : FiniteGrp.{0} → Prop) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ A B : FiniteGrp.{0}, Nat.card A = k ∧ P A ∧
        Nat.card B = h ∧ Q B ∧ Nonempty (G ≃* A × B)}).ncard ≤
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {A | Nat.card A = k ∧ P A}).ncard *
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {B | Nat.card B = h ∧ Q B}).ncard := by
  classical
  let C (n : ℕ) (F : FiniteGrp.{0} → Prop) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {A | Nat.card A = n ∧ F A}
  let (n : ℕ) (F : FiniteGrp.{0} → Prop) : Finite (C n F) := ((finite_classes n).subset (Set.image_mono fun _ hx => hx.1)).to_subtype
  let rep {n F} (x : C n F) : FiniteGrp.{0} := x.property.choose
  let prod (x : C k P × C h Q) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0})
    (FiniteGrp.of (rep x.1 × rep x.2))
  apply le_trans (Set.ncard_le_ncard (t := Set.range prod) ?_ (Set.finite_range _)) ?_
  · rintro _ ⟨G,⟨A,B,ak,pa,bh,qb,⟨e⟩⟩,rfl⟩
    let x : C k P := ⟨_,A,⟨ak,pa⟩,rfl⟩
    let y : C h Q := ⟨_,B,⟨bh,qb⟩,rfl⟩
    have ex : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep x) = Quotient.mk _ A := x.property.choose_spec.2
    have ey : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (rep y) = Quotient.mk _ B := y.property.choose_spec.2
    let f := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact ex))).groupIsoToMulEquiv
    let g' := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact ey))).groupIsoToMulEquiv
    exact ⟨⟨x,y⟩,Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      ((f.prodCongr g').trans e.symm).toGrpIso⟩⟩
  · change Nat.card (Set.range prod) ≤ Nat.card (C k P) * Nat.card (C h Q)
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

/-- Strong induction pays for both direct factors and for the choice of their orders. -/
theorem coprime_product_induction_step {q r E : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        (∃ A B : FiniteGrp.{0}, 1 < Nat.card A ∧ Nat.card A ≤ Nat.card B ∧
          (Nat.card A).Coprime (Nat.card B) ∧ Group.IsSolvable A ∧ Group.IsSolvable B ∧
          Nonempty (G ≃* A × B))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ p ∈ q.primeFactors, g (p^q.factorization p) := by
  classical
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let C (n : ℕ) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}
  let I := {k : Fin (q+1) // 1 < k.val ∧ k.val ≤ q/k.val ∧ k.val*(q/k.val) = q ∧ k.val.Coprime (q/k.val)}
  let S (i : I) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ A B : FiniteGrp.{0}, Nat.card A = i.val.val ∧ Group.IsSolvable A ∧
      Nat.card B = q/i.val.val ∧ Group.IsSolvable B ∧ Nonempty (G ≃* A × B)}
  have finite (i : I) : (S i).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨A,B,ak,_,bh,_,⟨e⟩⟩
    change Nat.card G = q
    rw [Nat.card_congr e.toEquiv,Nat.card_prod,ak,bh,i.property.2.2.1]))
  have inner (i : I) : (S i).ncard ≤ 2^(E*(r+1)^2-6-r)*L q := by
    let k := i.val.val
    let h := q/k
    have hk : 1 < k := i.property.1
    have kh : k ≤ h := i.property.2.1
    have eq : k*h = q := i.property.2.2.1
    have lk : L k * L h = L q := by
      rw [← eq]; exact (sylow_product_coprime (by omega) (by omega) i.property.2.2.2).symm
    have ok := odd.of_dvd_nat (show k ∣ q from ⟨h,eq.symm⟩)
    have oh := odd.of_dvd_nat (show h ∣ q from ⟨k,by rw [← eq,Nat.mul_comm]⟩)
    let a := Nat.log 2 k
    let b := Nat.log 2 h
    have ha : 1 ≤ a := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ k by omega))
    have hb : a ≤ b := Nat.log_mono_right kh
    have half := Nat.mul_le_mul (Nat.pow_log_le_self 2 (by omega : k ≠ 0))
      (Nat.pow_log_le_self 2 (by omega : h ≠ 0))
    rw [← pow_add,eq] at half
    have ab : a+b < r := by
      by_contra! bad
      have zz := Nat.pow_le_pow_right (by decide : 0 < 2) bad
      exact (not_lt_of_ge zz) (half.trans_lt hr)
    have countH : (C h).ncard ≤ 2^(E*(b+1+1)^2)*L h :=
      ih h (by rw [← eq]; nlinarith) _ oh (Nat.lt_pow_succ_log_self (by decide) _)
    apply le_trans (product_class_count k h (fun A => Group.IsSolvable A) (fun B => Group.IsSolvable B))
    by_cases sm : k < 8
    · have pp : IsPrimePow k := by
        obtain ⟨j,hj⟩ := ok
        have : k = 3 ∨ k = 5 ∨ k = 7 := by omega
        rcases this with z | z | z <;> rw [z] <;> exact Nat.Prime.isPrimePow (by decide)
      have term := Nat.mul_le_mul (prime_power_count pp) countH
      calc
        _ ≤ L k * (2^(E*(b+1+1)^2)*L h) := term
        _ = 2^(E*(b+1+1)^2)*L q := by rw [← lk]; ring
        _ ≤ _ := by
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by decide)
          have mono := Nat.mul_le_mul_left E (Nat.pow_le_pow_left (by omega : b+1+1 ≤ r) 2)
          obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le hE
          have budget : E*r^2+r+6 ≤ E*(r+1)^2 := by rw [hc]; ring_nf; omega
          omega
    · have a3 : 3 ≤ a := Nat.le_log_of_pow_le (by decide) (by simpa using (show 8 ≤ k by omega))
      have countK : (C k).ncard ≤ 2^(E*(a+1+1)^2)*L k :=
        ih k (by rw [← eq]; nlinarith) _ ok (Nat.lt_pow_succ_log_self (by decide) _)
      calc
        _ ≤ (2^(E*(a+1+1)^2)*L k)*(2^(E*(b+1+1)^2)*L h) := Nat.mul_le_mul countK countH
        _ = (2^(E*(a+1+1)^2)*2^(E*(b+1+1)^2))*L q := by rw [← lk]; ring
        _ ≤ _ := by
          rw [← pow_add]
          apply Nat.mul_le_mul_right
          apply Nat.pow_le_pow_right (by decide)
          obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le a3
          obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le (a3.trans hb)
          obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le ab
          obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le hE
          have budget : E*(a+1+1)^2 + E*(b+1+1)^2+r+6 ≤ E*(r+1)^2 := by
            rw [hj,hx,hy,hc]; simp only [Nat.succ_eq_add_one]; ring_nf; omega
          omega
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, S i) ?_ (Set.finite_iUnion finite)) ?_
  · rintro _ ⟨G,⟨hg,_,A,B,ha,hab,cop,sa,sb,⟨e⟩⟩,rfl⟩
    have eq := (Nat.card_congr e.toEquiv).symm.trans hg
    rw [Nat.card_prod] at eq
    have leq := (Nat.le_mul_of_pos_right (Nat.card A) (Nat.card_pos (α := B))).trans eq.le
    have div : q/Nat.card A = Nat.card B := by rw [← eq,Nat.mul_div_cancel_left _ Nat.card_pos]
    let i : I := ⟨⟨Nat.card A,by omega⟩,ha,div.symm ▸ hab,div.symm ▸ eq,div.symm ▸ cop⟩
    exact Set.mem_iUnion.mpr ⟨i,G,⟨A,B,rfl,sa,div.symm,sb,⟨e⟩⟩,rfl⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (S i).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(E*(r+1)^2-6-r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^(E*(r+1)^2-6-r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^(E*(r+1)^2-6-r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by
        rw [← mul_assoc,← pow_add]
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        have := Nat.mul_le_mul_right ((r+1)^2) hE
        have : r+6 ≤ 6*(r+1)^2 := by nlinarith
        omega

/-- Bound nonsplit cyclic extensions by the number of kernel generators. -/
lemma cyclic_quotient_rank_count (K : FiniteGrp.{0}) (m : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
        N.index = m ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card K^(Group.rank K+1) := by
  classical
  let _ : Finite (K →* K) := Finite.of_injective (fun g : K →* K => (g : K → K)) DFunLike.coe_injective
  have aut := (Nat.card_le_card_of_injective MulEquiv.toMonoidHom MulEquiv.toMonoidHom_injective).trans (rank_hom_count K K)
  exact (cyclic_quotient_count K m).trans ((Nat.mul_le_mul_right _ aut).trans_eq (pow_succ ..).symm)

/-- Sum a fixed-kernel bound over solvable kernel classes and quotient orders.
The ambient family and kernel condition can depend on the order of the cyclic quotient. -/
theorem kernel_filtered_cyclic_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (F : ℕ → (G : FiniteGrp.{0}) → Subgroup G → Prop) (C : ℕ → FiniteGrp.{0} → Prop)
    (cost : ∀ k K, C k K → (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal),
        IsCyclic (G ⧸ N) ∧ N.index = k ∧ F k G N ∧ Nonempty (K ≃* N)}).ncard ≤
          Nat.card K^(B * Nat.log 2 k+1))
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ F N.index G N ∧ C N.index (FiniteGrp.of N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  let L (n : ℕ) := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  let I := {k : Fin (q+1) // 1 < k.val ∧ 0 < q/k.val ∧ k.val*(q/k.val) = q}
  let T (i : I) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = q/i.val.val ∧ Group.IsSolvable G ∧ C i.val.val G}
  let (i : I) : Finite (T i) := ((finite_classes _).subset (Set.image_mono (fun _ h => h.1))).to_subtype
  let K (i : I) (x : T i) : FiniteGrp.{0} := x.property.choose
  have kc (i : I) (x : T i) : Nat.card (K i x) = q/i.val.val := x.property.choose_spec.1.1
  let S (i : I) (x : T i) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
      N.index = i.val.val ∧ F i.val.val G N ∧ Nonempty (K i x ≃* N)}
  have finite (i : I) (x : T i) : (S i x).Finite := (finite_classes q).subset (Set.image_mono (by
    rintro G ⟨N,_,_,idx,_,⟨e⟩⟩
    change Nat.card G = q
    rw [← N.index_mul_card,idx,← Nat.card_congr e.toEquiv,kc,i.property.2.2]))
  have inner (i : I) : (⋃ x : T i, S i x).ncard ≤ 2^(E*(r+1)^2-6-r)*L q := by
    let _ := Fintype.ofFinite (T i)
    let k := i.val.val
    let h := q/k
    let d := Nat.log 2 k
    have hk : 1 < k := i.property.1
    have hh : 0 < h := i.property.2.1
    have eq : k*h = q := i.property.2.2
    have small : h < q := by rw [← eq]; nlinarith
    have dpos : 1 ≤ d := Nat.le_log_of_pow_le (by decide) (by simpa using (show 2 ≤ k by omega))
    have kd : 2^d ≤ k := Nat.pow_log_le_self _ (by omega)
    have dr : d ≤ r := (Nat.log_lt_of_lt_pow (by omega) ((Nat.le_mul_of_pos_right k hh).trans_lt (eq ▸ hr))).le
    let s := r-d
    have split : s+d = r := Nat.sub_add_cancel dr
    have shr : h < 2^s := by
      by_contra! bad
      have z := Nat.mul_le_mul kd bad
      rw [← pow_add, Nat.add_comm d s, split, eq] at z
      omega
    have budget : r + (s*(B*d+1) + r + E*(s+1)^2) + 6 ≤ E*(r+1)^2 := by
      obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le dpos
      obtain ⟨c,hc⟩ := Nat.exists_eq_add_of_le hE
      rw [← split,hj,hc]; ring_nf; omega
    have dvd : h ∣ q := ⟨k,by rw [← eq,Nat.mul_comm]⟩
    have ch := ih h small s (odd.of_dvd_nat dvd) shr
    have countK : Nat.card (T i) ≤ 2^(E*(s+1)^2)*L h := by
      apply le_trans _ ch
      exact Set.ncard_le_ncard (Set.image_mono fun _ hg => ⟨hg.1,hg.2.1⟩)
        ((finite_classes _).subset (Set.image_mono fun _ hg => hg.1))
    have action (x : T i) : (S i x).ncard ≤ 2^(s*(B*d+1)) := by
      apply (cost k (K i x) x.property.choose_spec.1.2.2).trans
      rw [kc,pow_mul]
      exact Nat.pow_le_pow_left shr.le _
    have pad := (sylow_product_dvd_bound hh odd.pos dvd).trans (Nat.mul_le_mul_right _ hr.le)
    calc
      _ ≤ ∑ x : T i, (S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : T i, 2^(s*(B*d+1)) := Finset.sum_le_sum fun x _ => action x
      _ = 2^(s*(B*d+1))*Nat.card (T i) := by simp [Nat.card_eq_fintype_card,Nat.mul_comm]
      _ ≤ 2^(s*(B*d+1))*(2^(E*(s+1)^2)*(2^r*L q)) := Nat.mul_le_mul_left _ (countK.trans (Nat.mul_le_mul_left _ pad))
      _ = 2^(s*(B*d+1)+r+E*(s+1)^2)*L q := by simp only [pow_add]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  apply le_trans (Set.ncard_le_ncard (t := ⋃ i : I, ⋃ x : T i, S i x) ?_
    (Set.finite_iUnion fun i => Set.finite_iUnion (finite i))) ?_
  · rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,fam,rk⟩,rfl⟩
    let _ : N.Normal := hn
    let _ : Group.IsSolvable G := hs
    have eq := N.index_mul_card.trans hg
    have le := (Nat.le_mul_of_pos_right N.index (Nat.card_pos (α := N))).trans eq.le
    have div : q/N.index = Nat.card N := by rw [← eq,Nat.mul_div_cancel_left _ (by omega)]
    let i : I := ⟨⟨N.index,by omega⟩,big,div.symm ▸ Nat.card_pos,div.symm ▸ eq⟩
    let x : T i := ⟨Quotient.mk _ (FiniteGrp.of N),FiniteGrp.of N,
      ⟨div.symm,inferInstanceAs (Group.IsSolvable N),rk⟩,rfl⟩
    have rep : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (K i x) = Quotient.mk _ (FiniteGrp.of N) := x.property.choose_spec.2
    let e := ((inducedFunctor FiniteGrp.toGrp).mapIso (Classical.choice (Quotient.exact rep))).groupIsoToMulEquiv
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x,G,⟨N,hn,cyc,rfl,fam,⟨e⟩⟩,rfl⟩⟩
  · let _ := Fintype.ofFinite I
    have ni : Nat.card I ≤ 2^r := (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      (by simpa using hr : Nat.card (Fin (q+1)) ≤ 2^r)
    calc
      _ ≤ ∑ i : I, (⋃ x : T i, S i x).ncard := Set.ncard_iUnion_le_of_fintype _
      _ ≤ ∑ _ : I, 2^(E*(r+1)^2-6-r)*L q := Finset.sum_le_sum fun i _ => inner i
      _ = Nat.card I*(2^(E*(r+1)^2-6-r)*L q) := by simp [Nat.card_eq_fintype_card]
      _ ≤ 2^r*(2^(E*(r+1)^2-6-r)*L q) := Nat.mul_le_mul_right _ ni
      _ ≤ _ := by
        rw [← mul_assoc,← pow_add]
        apply Nat.mul_le_mul_right
        apply Nat.pow_le_pow_right (by decide)
        have := Nat.mul_le_mul_right ((r+1)^2) (show 6 ≤ E by omega)
        have : r+6 ≤ 6*(r+1)^2 := by nlinarith
        omega

/-- Specialization to filters on the ambient group and quotient order. -/
theorem filtered_cyclic_extension_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (F C : ℕ → FiniteGrp.{0} → Prop)
    (cost : ∀ k K, C k K → (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | F k G ∧ ∃ (N : Subgroup G) (_ : N.Normal),
        IsCyclic (G ⧸ N) ∧ N.index = k ∧ Nonempty (K ≃* N)}).ncard ≤
          Nat.card K^(B * Nat.log 2 k+1))
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ F N.index G ∧ C N.index (FiniteGrp.of N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply kernel_filtered_cyclic_induction_step hr odd hE (fun k G _ => F k G) C _ ih
  intro k K hK
  apply le_trans _ (cost k K hK)
  apply Set.ncard_le_ncard (Set.image_mono ?_) ((finite_classes (k*Nat.card K)).subset (Set.image_mono ?_))
  · rintro G ⟨N,hn,cyc,idx,fam,e⟩
    exact ⟨fam,N,hn,cyc,idx,e⟩
  · rintro G ⟨_,N,_,_,idx,⟨e⟩⟩
    change Nat.card G = _
    rw [← N.index_mul_card,idx,Nat.card_congr e.toEquiv]

/-- Induct when the kernel automorphism class count fits the quotient-order budget. -/
theorem outer_cyclic_quotient_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (MulAut.conj : N →* MulAut N).range; ∃ _ : J.Normal, (ConjClasses.mk '' {t : MulAut N ⧸ J | t^N.index = 1}).ncard * Nat.card (Subgroup.center N) ≤ Nat.card N^(B * Nat.log 2 N.index+1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  let C (k : ℕ) (K : FiniteGrp.{0}) :=
    let J := (MulAut.conj : K →* MulAut K).range
    ∃ _ : J.Normal, (ConjClasses.mk '' {t : MulAut K ⧸ J | t^k = 1}).ncard *
      Nat.card (Subgroup.center K) ≤ Nat.card K^(B * Nat.log 2 k+1)
  have cost (k : ℕ) (K : FiniteGrp.{0}) (h : C k K) :
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | ∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧
          N.index = k ∧ Nonempty (K ≃* N)}).ncard ≤ Nat.card K^(B * Nat.log 2 k+1) := by
    obtain ⟨hn,classes⟩ := h
    let _ : (MulAut.conj : K →* MulAut K).range.Normal := hn
    exact (outer_cyclic_quotient_count K k).trans classes
  apply le_trans _ (filtered_cyclic_extension_induction_step hr odd hE
    (fun _ _ => True) C (by simpa only [true_and] using cost) ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,classes⟩,rfl⟩
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,True.intro,hJ,classes⟩,rfl⟩

/-- A numerical check for the local commutativity assumption at the quotient prime. -/
lemma sylow_commutative_of_valuation_le_two {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (small : (Nat.card G).factorization p ≤ 2)
    (P : Sylow p G) : IsMulCommutative P := by
  have card := P.card_eq_multiplicity
  obtain h | h | h : (Nat.card G).factorization p = 0 ∨
      (Nat.card G).factorization p = 1 ∨ (Nat.card G).factorization p = 2 := by omega
  · rw [h,pow_zero] at card
    let _ : Subsingleton P := (Nat.card_eq_one_iff_unique.mp card).1
    exact ⟨⟨fun _ _ => Subsingleton.elim ..⟩⟩
  · rw [h,pow_one] at card
    exact (isCyclic_of_prime_card card).isMulCommutative
  · rw [h] at card
    exact IsPGroup.isMulCommutative_of_card_eq_prime_sq card

/-- Sum the fixed-kernel counts when each Sylow center covers the quotient. -/
theorem central_lift_stabilizer_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ (∃ P : Sylow N.index.minFac G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N),
      0 < a ∧ N.index = p^a ∧ p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (B * Nat.log 2 N.index + 1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  let F (k : ℕ) (G : FiniteGrp.{0}) (N : Subgroup G) :=
    ∃ P : Sylow k.minFac G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤
  let C (k : ℕ) (K : FiniteGrp.{0}) := ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p K),
      0 < a ∧ k = p^a ∧ p ^ ((MulAut.conj : K →* MulAut K).range.subgroupOf
              (fixingSubgroup (MulAut K) (S : Set K))).index.factorization p *
            Nat.card (Subgroup.center K) ≤ Nat.card K ^ (B * Nat.log 2 k + 1)
  apply kernel_filtered_cyclic_induction_step hr odd hE F C _ ih
  rintro k K ⟨p,a,hp,S,ha,rfl,size⟩
  let _ : Fact p.Prime := ⟨hp⟩
  apply le_trans _ ((central_lift_outer_prime_part_count K a S).trans size)
  · apply Set.ncard_le_ncard (Set.image_mono ?_) ((finite_classes ((p^a)*Nat.card K)).subset
      (Set.image_mono ?_))
    · rintro G ⟨N,hn,cyc,idx,fam,e⟩
      change ∃ P : Sylow (p^a).minFac G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤ at fam
      rw [hp.pow_minFac ha.ne'] at fam
      let _ : N.Normal := hn
      exact ⟨N,hn,cyc,idx,(sylow_center_sup_iff_all N).mp fam,e⟩
    · rintro G ⟨N,_,_,idx,_,⟨e⟩⟩
      change Nat.card G = _
      rw [← N.index_mul_card,idx,Nat.card_congr e.toEquiv]

/-- Only Sylow subgroups at the cyclic quotient prime need to commute in the ambient group. -/
theorem quotient_prime_stabilizer_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ (∀ P : Sylow N.index.minFac G, IsMulCommutative P) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N),
      0 < a ∧ N.index = p^a ∧ p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (B * Nat.log 2 N.index + 1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (central_lift_stabilizer_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,comm,rest⟩,rfl⟩
  let _ : Fact N.index.minFac.Prime := ⟨Nat.minFac_prime (by omega)⟩
  let P : Sylow N.index.minFac G := default
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,⟨P,center_sup_of_commutative (comm P) _⟩,rest⟩,rfl⟩

/-- An arithmetic sufficient condition for the mixed-Sylow induction step. -/
theorem small_valuation_stabilizer_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ q.factorization N.index.minFac ≤ 2 ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N),
      0 < a ∧ N.index = p^a ∧ p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (B * Nat.log 2 N.index + 1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (quotient_prime_stabilizer_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,small,rest⟩,rfl⟩
  let _ : Fact N.index.minFac.Prime := ⟨Nat.minFac_prime (by omega)⟩
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,?_,rest⟩,rfl⟩
  exact sylow_commutative_of_valuation_le_two (hg.symm ▸ small)

/-- Sum the prime-part fixed-kernel estimate over all eligible odd-order kernels. -/
theorem stabilizer_prime_part_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N),
      N.index = p^a ∧ p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (B * Nat.log 2 N.index + 1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (quotient_prime_stabilizer_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,comm,p,a,hp,S,idx,size⟩,rfl⟩
  have ha : 0 < a := by
    cases a with
    | zero => rw [pow_zero] at idx; omega
    | succ a => omega
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,comm _ (Nat.minFac_prime (by omega)),p,a,hp,S,ha,idx,size⟩,rfl⟩

/-- For abelian Sylow groups the induction charges only generators needed beyond a
kernel Sylow subgroup, in addition to the central power parameter. -/
theorem relative_generator_cyclic_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ (∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N) (t : Finset N),
      N.index = p^a ∧ S.toSubgroup ⊔ Subgroup.closure (t : Set N) = ⊤ ∧ t.card ≤ B * Nat.log 2 N.index)}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (stabilizer_prime_part_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,comm,p,a,hp,S,t,idx,gen,size⟩,rfl⟩
  let _ : Fact p.Prime := ⟨hp⟩
  let A := fixingSubgroup (MulAut N) (S : Set N)
  let P : Sylow p A := default
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,comm,p,a,hp,S,idx,?_⟩,rfl⟩
  apply (Nat.mul_le_mul_right _ (prime_part_index_le _ hp)).trans
  rw [pow_succ,← P.card_eq_multiplicity]
  exact Nat.mul_le_mul
    ((Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
      ((pointwise_stabilizer_relative_generator_bound S.toSubgroup t gen).trans
        (Nat.pow_le_pow_right Nat.card_pos size)))
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- Induct past cyclic quotients whose kernel has abelian outer automorphism
group with rank bounded by a fixed multiple of log₂ of the kernel order. -/
theorem abelian_outer_cyclic_induction_step {q r E c : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 2*c+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (MulAut.conj : N →* MulAut N).range; ∃ _ : J.Normal, IsMulCommutative (MulAut N ⧸ J) ∧ Group.rank (MulAut N ⧸ J) ≤ c * Nat.log 2 (Nat.card N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (outer_cyclic_quotient_induction_step (B := 2*c) hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,comm,rk⟩,rfl⟩
  let _ : (MulAut.conj : N →* MulAut N).range.Normal := hJ
  let _ : IsMulCommutative (MulAut N ⧸ (MulAut.conj : N →* MulAut N).range) := comm
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,abelian_outer_induction_budget N big rk⟩,rfl⟩

/-- Induct past cyclic quotients whose kernel has class-at-most-two outer automorphism
group with total central and quotient rank bounded by a fixed multiple of log₂ of the kernel order. -/
theorem class_two_outer_cyclic_induction_step {q r E c : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 2*c+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (MulAut.conj : N →* MulAut N).range; ∃ _ : J.Normal, let O := MulAut N ⧸ J; let Z := Subgroup.center O; IsMulCommutative (O ⧸ Z) ∧ Group.rank (O ⧸ Z) + Group.rank Z ≤ c * Nat.log 2 (Nat.card N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (outer_cyclic_quotient_induction_step (B := 2*c) hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,comm,rk⟩,rfl⟩
  let _ : (MulAut.conj : N →* MulAut N).range.Normal := hJ
  let O := MulAut N ⧸ (MulAut.conj : N →* MulAut N).range
  let Z := Subgroup.center O
  let _ : IsMulCommutative (O ⧸ Z) := comm
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,?_⟩,rfl⟩
  have hm : 0 < N.index := by omega
  have count := (class_two_outer_class_bound O N.index hm).trans (Nat.mul_le_mul
    (Nat.pow_le_pow_left (Nat.gcd_le_left _ hm) _) (Nat.pow_le_pow_left (Nat.gcd_le_left _ hm) _))
  rw [← pow_add] at count
  rw [pow_succ]
  exact Nat.mul_le_mul (count.trans (cyclic_rank_power_budget Nat.card_pos big rk))
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- All nilpotency classes are allowed when the total rank of layers sharing a
prime with the quotient order is controlled by the kernel order. -/
theorem nilpotent_outer_cyclic_induction_step {q r E c : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 2*c+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (MulAut.conj : N →* MulAut N).range; ∃ _ : J.Normal, let O := MulAut N ⧸ J; let Z (i : ℕ) := Subgroup.center (O ⧸ Subgroup.upperCentralSeries O i); Group.IsNilpotent O ∧ (∑ i ∈ Finset.range (Group.nilpotencyClass O), if N.index.Coprime (Monoid.exponent (Z i)) then 0 else Group.rank (Z i)) ≤ c * Nat.log 2 (Nat.card N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (outer_cyclic_quotient_induction_step (B := 2*c) hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,nil,rk⟩,rfl⟩
  let _ : (MulAut.conj : N →* MulAut N).range.Normal := hJ
  let O := MulAut N ⧸ (MulAut.conj : N →* MulAut N).range
  let _ : Group.IsNilpotent O := nil
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,?_⟩,rfl⟩
  rw [pow_succ]
  exact Nat.mul_le_mul ((nilpotent_outer_active_rank_bound O (by omega : 0 < N.index)).trans
    (cyclic_rank_power_budget Nat.card_pos big rk))
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- For a cyclic prime-power quotient, a rank budget on one outer Sylow subgroup
suffices for the induction on group order. -/
theorem prime_power_sylow_outer_cyclic_induction_step {q r E c : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 2*c+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧
        (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧
          let J := (MulAut.conj : N →* MulAut N).range
          ∃ _ : J.Normal, ∃ (p a : ℕ) (_ : p.Prime) (P : Sylow p (MulAut N ⧸ J)),
            N.index = p^a ∧
            let Z (i : ℕ) := Subgroup.center (P ⧸ Subgroup.upperCentralSeries P i)
            (∑ i ∈ Finset.range (Group.nilpotencyClass P),
              if N.index.Coprime (Monoid.exponent (Z i)) then 0 else Group.rank (Z i))
                ≤ c * Nat.log 2 (Nat.card N))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (outer_cyclic_quotient_induction_step (B := 2*c) hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,p,a,hp,P,idx,rk⟩,rfl⟩
  let _ : (MulAut.conj : N →* MulAut N).range.Normal := hJ
  let O := MulAut N ⧸ (MulAut.conj : N →* MulAut N).range
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,hJ,?_⟩,rfl⟩
  rw [pow_succ]
  have localCount : (ConjClasses.mk '' {x : O | x^N.index = 1}).ncard ≤
      (ConjClasses.mk '' {x : P | x^N.index = 1}).ncard := by
    rw [idx]
    exact prime_power_torsion_classes_le_sylow O P a
  exact Nat.mul_le_mul ((localCount.trans (nilpotent_outer_active_rank_bound P (by omega : 0 < N.index))).trans
    (cyclic_rank_power_budget Nat.card_pos big rk))
    (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

theorem eligible_cyclic_quotient_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ (ConjClasses.mk '' {t : MulAut N | ∃ b, MulAut.conj b = t^N.index}).ncard * Nat.card (Subgroup.center N) ≤ Nat.card N^(B * Nat.log 2 N.index+1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (outer_cyclic_quotient_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,classes⟩,rfl⟩
  let hI := inner_automorphisms_normal N
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,hI,(Nat.mul_le_mul_right _ (outer_classes_le_eligible N N.index)).trans classes⟩,rfl⟩

/-- A nontrivial cyclic quotient of order coprime to the outer automorphism
group order can be removed by induction, with no kernel rank assumption. -/
theorem coprime_outer_cyclic_induction_step {q r E : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : 6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ N.index.Coprime (MulAut.conj : N →* MulAut N).range.index)}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (eligible_cyclic_quotient_induction_step (B := 0) hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,cop⟩,rfl⟩
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,?_⟩,rfl⟩
  simpa only [Nat.zero_mul,Nat.zero_add,pow_one] using coprime_outer_action_budget N N.index cop

theorem center_cyclic_quotient_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ Nat.card (ConjClasses (MulAut N)) * Nat.card (Subgroup.center N) ≤ Nat.card N^(B * Nat.log 2 N.index+1))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  classical
  apply le_trans _ (eligible_cyclic_quotient_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,classes⟩,rfl⟩
  let _ : Finite (ConjClasses (MulAut N)) := Finite.of_surjective _ ConjClasses.mk_surjective
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,?_⟩,rfl⟩
  exact (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)).trans classes

theorem conjugacy_cyclic_quotient_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ Nat.card (ConjClasses (MulAut N)) ≤ Nat.card N^(B * Nat.log 2 N.index))}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (center_cyclic_quotient_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,classes⟩,rfl⟩
  refine ⟨G,⟨hg,hs,N,hn,cyc,big,?_⟩,rfl⟩
  rw [pow_succ]
  exact Nat.mul_le_mul classes (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective)

/-- Counting conjugacy classes never costs more than specifying generator images. -/
lemma automorphism_classes_le_rank (K : FiniteGrp.{0}) :
    Nat.card (ConjClasses (MulAut K)) ≤ Nat.card K ^ Group.rank K := by
  classical
  let _ : Finite (K →* K) := Finite.of_injective (fun g : K →* K => (g : K → K)) DFunLike.coe_injective
  exact (Nat.card_le_card_of_surjective _ ConjClasses.mk_surjective).trans
    ((Nat.card_le_card_of_injective MulEquiv.toMonoidHom MulEquiv.toMonoidHom_injective).trans (rank_hom_count K K))

/-- A centerless kernel can use one additional generator in the cyclic-quotient induction. -/
lemma centerless_cyclic_rank_budget (K : FiniteGrp.{0}) [Subsingleton (Subgroup.center K)]
    (d : ℕ) (rk : Group.rank K ≤ d+1) :
    Nat.card (ConjClasses (MulAut K)) * Nat.card (Subgroup.center K) ≤ Nat.card K^(d+1) := by
  simpa [Nat.card_unique] using
    (automorphism_classes_le_rank K).trans (Nat.pow_le_pow_right Nat.card_pos rk)

/-- Induct without changing E when the kernel rank is controlled by the quotient order. -/
theorem rank_cyclic_quotient_induction_step {q r E B : ℕ} (hr : q < 2^r) (odd : Odd q) (hE : B+6 ≤ E)
    (ih : ∀ n < q, ∀ s, Odd n → n < 2^s →
      (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
        2^(E*(s+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ Group.rank N ≤ B * Nat.log 2 N.index)}).ncard ≤
      2^(E*(r+1)^2-6) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (conjugacy_cyclic_quotient_induction_step hr odd hE ih)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,hs,N,hn,cyc,big,rk⟩,rfl⟩
  exact ⟨G,⟨hg,hs,N,hn,cyc,big,(automorphism_classes_le_rank (FiniteGrp.of N)).trans
    (Nat.pow_le_pow_right Nat.card_pos rk)⟩,rfl⟩



theorem abelian_or_primary_kernel_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ K H : FiniteGrp.{0}, (IsMulCommutative K ∨ IsPrimePow (Nat.card K)) ∧
        Group.IsNilpotent H ∧
        (Nat.card K).Coprime (Nat.card H) ∧ ∃ f : H →* MulAut K, Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^((r+1)^2) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (nilpotent_hall_union hr)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,K,H,typ,nil,cop,act,iso⟩,rfl⟩
  have kn : Group.IsNilpotent K := by
    rcases typ with comm | pk
    · let _ : CommGroup K := { (inferInstance : Group K) with mul_comm := comm.is_comm.comm }
      infer_instance
    · obtain ⟨p,k,hp,_,eq⟩ := (isPrimePow_nat_iff _).mp pk
      let _ : Fact p.Prime := ⟨hp⟩
      exact (IsPGroup.of_card eq.symm).isNilpotent
  exact ⟨G,⟨hg,K,H,kn,nil,cop,act,iso⟩,rfl⟩

theorem abelian_or_two_primary_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ K H : FiniteGrp.{0}, (IsMulCommutative K ∨ (IsPrimePow (Nat.card K) ∧ IsPrimePow (Nat.card H))) ∧
        Group.IsNilpotent H ∧
        (Nat.card K).Coprime (Nat.card H) ∧ ∃ f : H →* MulAut K, Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^((r+1)^2) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (abelian_or_primary_kernel_hall_union hr)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,K,H,typ,nil,cop,act,iso⟩,rfl⟩
  exact ⟨G,⟨hg,K,H,typ.imp_right And.left,nil,cop,act,iso⟩,rfl⟩

/-- Specialization to abelian kernels of arbitrary order. -/
theorem abelian_kernel_hall_union {q r : ℕ} (hr : q < 2^r) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ ∃ K H : FiniteGrp.{0}, IsMulCommutative K ∧
        Group.IsNilpotent H ∧
        (Nat.card K).Coprime (Nat.card H) ∧ ∃ f : H →* MulAut K, Nonempty (G ≃* SemidirectProduct _ H f)}).ncard ≤
      2^((r+1)^2) * ∏ z ∈ q.primeFactors, g (z^q.factorization z) := by
  apply le_trans _ (abelian_or_primary_kernel_hall_union hr)
  apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
  rintro _ ⟨G,⟨hg,K,H,comm,nil,cop,act,iso⟩,rfl⟩
  exact ⟨G,⟨hg,K,H,Or.inl comm,nil,cop,act,iso⟩,rfl⟩

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2.H2 := by
  classical
  rintro ⟨A, hA⟩ ⟨B, hB⟩
  let D := max 3 (max A B)
  have h3 : 3 ≤ D := le_max_left ..
  have h1 : 1 ≤ D := by omega
  let E := D+6
  have hE : 6 ≤ E := by dsimp [E]; omega
  refine ⟨E, fun q => ?_⟩
  induction q using Nat.strong_induction_on with | h q ih =>
  intro r odd hr
  by_cases hpp : IsPrimePow q
  · exact (prime_power_count hpp).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))
  by_cases htwo : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ (¬ p ∣ l-1 ∨ ∀ i, 0 < i → i < a → ¬ Nat.ModEq l (p^i) 1) ∧ 0 < a ∧ q = p^a*l
  · obtain ⟨p, l, a, hp, hl, hne, haut, ha, rfl⟩ := htwo
    have sub : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = p^a*l ∧ Group.IsSolvable G} ⊆
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
        {G : FiniteGrp.{0} | Nat.card G = p^a*l} := by
      rintro _ ⟨G, ⟨hG, _⟩, rfl⟩
      exact ⟨G, hG, rfl⟩
    apply (Set.ncard_le_ncard sub (finite_classes _)).trans
    apply (two_prime_bound hp hl hne haut ha hr).trans
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.le_mul_of_pos_left _ (by dsimp [E]; omega)
  let S (P : FiniteGrp.{0} → Prop) := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G ∧ P G}
  let U (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, (N.Normal ∨ P.Normal) ∧ N.IsComplement' P ∧ IsCyclic P ∧ Group.IsNilpotent N ∧ (Nat.card N).Coprime (Nat.card P))
  let V₀ (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, N.Normal ∧ N.IsComplement' P ∧ Group.IsNilpotent N ∧ Group.IsNilpotent P ∧ Nat.card N ^ (Group.rank N * Group.rank P) ≤ 2^(r*r*2) ∧ (Nat.card N).Coprime (Nat.card P))
  let V₁ (G : FiniteGrp.{0}) := (∃ (N : Subgroup G) (_ : N.Normal), (∃ (M : Subgroup N) (_ : M.Normal), Group.IsNilpotent M ∧ IsCyclic (N ⧸ M)) ∧ IsCyclic (G ⧸ N))
  let V (G : FiniteGrp.{0}) := V₀ G ∨ V₁ G
  let W₁ (G : FiniteGrp.{0}) := (∃ K : Subgroup G, K.Normal ∧ Group.IsNilpotent K ∧ 1 < Nat.card K ∧ (Nat.card K).Coprime K.index)
  let W₂ (G : FiniteGrp.{0}) := (∃ N P : Subgroup G, P.Normal ∧ N.IsComplement' P ∧ IsCyclic P ∧ 1 < Nat.card P)
  let W₃ (b : ℕ) (G : FiniteGrp.{0}) := (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧ let J := (MulAut.conj : N →* MulAut N).range; ∃ _ : J.Normal, (ConjClasses.mk '' {t : MulAut N ⧸ J | t^N.index = 1}).ncard * Nat.card (Subgroup.center N) ≤ Nat.card N^(b * Nat.log 2 N.index+1))
  let W (G : FiniteGrp.{0}) := W₁ G ∨ (W₂ G ∨ W₃ D G)
  let N₀ (G : FiniteGrp.{0}) := U G ∨ V G
  let Prod (G : FiniteGrp.{0}) := (∃ A B : FiniteGrp.{0}, 1 < Nat.card A ∧ 1 < Nat.card B ∧ (Nat.card A).Coprime (Nat.card B) ∧ Nonempty (G ≃* A × B))
  let N (G : FiniteGrp.{0}) := (N₀ G ∨ Prod G) ∨ W G
  let Z (G : FiniteGrp.{0}) := IsZGroup G
  let C (G : FiniteGrp.{0}) := ∀ p : ℕ, p.Prime → ∀ P : Sylow p G, IsMulCommutative P
  let T (G : FiniteGrp.{0}) := ∃ p : ℕ, p.Prime ∧ ∃ P : Sylow p G, ¬ IsMulCommutative P
  let F (G : FiniteGrp.{0}) := ((∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) ∧
        ∀ p l a : ℕ, (p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l) →
          ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1))
  let X (G : FiniteGrp.{0}) := ¬ F G ∧ ¬ N G ∧ ¬ Z G ∧ C G
  let Y (G : FiniteGrp.{0}) := ¬ F G ∧ ¬ N G ∧ T G
  have union_eq : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = q ∧ Group.IsSolvable G} =
      S F ∪ ((S N ∪ S Z) ∪ (S X ∪ S Y)) := by
    ext c
    constructor
    · rintro ⟨G, ⟨hq, hs⟩, rfl⟩
      by_cases hf : F G
      · exact Or.inl ⟨G, ⟨hq, hs, hf⟩, rfl⟩
      right
      by_cases hn : N G
      · exact Or.inl (Or.inl ⟨G, ⟨hq, hs, hn⟩, rfl⟩)
      by_cases hz : Z G
      · exact Or.inl (Or.inr ⟨G, ⟨hq, hs, hz⟩, rfl⟩)
      by_cases hc : C G
      · exact Or.inr (Or.inl ⟨G, ⟨hq, hs, hf, hn, hz, hc⟩, rfl⟩)
      · have ht : T G := by simpa [C, T] using hc
        exact Or.inr (Or.inr ⟨G, ⟨hq, hs, hf, hn, ht⟩, rfl⟩)
    · rintro (⟨G, ⟨hq, hs, _⟩, rfl⟩ | ((⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩) | (⟨G, ⟨hq, hs, _⟩, rfl⟩ | ⟨G, ⟨hq, hs, _⟩, rfl⟩))) <;>
        exact ⟨G, ⟨hq, hs⟩, rfl⟩
  let m := (r+1)^2
  let L := ∏ p ∈ q.primeFactors, g (p^q.factorization p)
  have posL : 0 < L := Finset.prod_pos fun p hp =>
    positive_count (pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
  have mono (a b : ℕ) (hab : a ≤ b) : 2^(a*m)*L ≤ 2^(b*m)*L :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hab))
  have za : (S Z).ncard ≤ 2^(D*m)*L := by
    calc
      _ ≤ q := cyclic_sylows_bound q
      _ ≤ 2^r := hr.le
      _ ≤ 2^(1*m) := Nat.pow_le_pow_right (by decide) (by dsimp [m]; nlinarith [Nat.zero_le (r^2)])
      _ ≤ 2^(1*m)*L := Nat.le_mul_of_pos_right _ posL
      _ ≤ _ := mono 1 D h1
  have residual_mono (b : ℕ) (hb : b ≤ D) (G : FiniteGrp.{0}) (hn : ¬ N G) :
      ¬ ((N₀ G ∨ Prod G) ∨ (W₁ G ∨ (W₂ G ∨ W₃ b G))) := by
    rintro (base | w | w | last)
    · exact hn (Or.inl base)
    · exact hn (Or.inr (Or.inl w))
    · exact hn (Or.inr (Or.inr (Or.inl w)))
    · obtain ⟨K,hK,cyc,large,hJ,classes⟩ := last
      apply hn
      refine Or.inr (Or.inr (Or.inr ⟨K,hK,cyc,large,hJ,classes.trans ?_⟩))
      exact Nat.pow_le_pow_right Nat.card_pos (Nat.succ_le_succ (Nat.mul_le_mul_right _ hb))
  let Rel (G : FiniteGrp.{0}) := (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N), N.index = p^a ∧
            p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (A * Nat.log 2 N.index + 1))
  let Mixed (G : FiniteGrp.{0}) := (∃ (N : Subgroup G) (_ : N.Normal), IsCyclic (G ⧸ N) ∧ 1 < N.index ∧
          (∃ P : Sylow N.index.minFac G, Subgroup.center P ⊔ N.subgroupOf P.toSubgroup = ⊤) ∧
          ∃ (p a : ℕ) (_ : p.Prime) (S : Sylow p N), 0 < a ∧ N.index = p^a ∧
            p ^ ((MulAut.conj : N →* MulAut N).range.subgroupOf
              (fixingSubgroup (MulAut N) (S : Set N))).index.factorization p *
            Nat.card (Subgroup.center N) ≤ Nat.card N ^ (B * Nat.log 2 N.index + 1))
  have remaining : (S (fun G => X G ∧ ¬ Rel G)).ncard ≤ 2^(D*m)*L := by
    by_cases h : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l
    · have empty : S (fun G => X G ∧ ¬ Rel G) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro _ ⟨G, ⟨hg, _, ⟨hf, _, _, hc⟩, _⟩, _⟩
        apply hf
        refine ⟨h, ?_⟩
        rintro p l a ⟨hp, hl, hne, _, hq⟩
        let _ : Fact p.Prime := ⟨hp⟩
        let P : Sylow p G := default
        let _ := hc p hp P
        exact normal_hall_of_abelian hp hl hne G (hg.trans hq) P
      simp [empty]
    · apply le_trans _ (mono _ D ((le_max_left A B).trans (le_max_right ..)))
      apply le_trans _ (hA q r odd hr hpp h)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
      rintro _ ⟨G, ⟨hg, hs, ⟨_, hn, hz, hc⟩, outside⟩, rfl⟩
      exact ⟨G, ⟨hg, hs, residual_mono A ((le_max_left A B).trans (le_max_right ..)) G hn, hz, hc, outside⟩, rfl⟩
  have other : (S (fun G => Y G ∧ ¬ Mixed G)).ncard ≤ 2^(D*m)*L := by
    have hb : B ≤ D := (le_max_right A B).trans (le_max_right ..)
    apply le_trans _ ((hB q r odd hr hpp htwo).trans (mono _ D hb))
    apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
    rintro _ ⟨G,⟨hg,hs,⟨hf,hn,ht⟩,outside⟩,rfl⟩
    exact ⟨G,⟨hg,hs,hf,residual_mono B hb G hn,ht,outside⟩,rfl⟩
  have nn₀ : (S N₀).ncard ≤ 2^(2*m+2)*L := by
    have cover : S N₀ = S U ∪ S V := by
      ext c
      constructor
      · rintro ⟨G, ⟨hg, hs, hu | hv⟩, rfl⟩
        · exact Or.inl ⟨G, ⟨hg, hs, hu⟩, rfl⟩
        · exact Or.inr ⟨G, ⟨hg, hs, hv⟩, rfl⟩
      · rintro (⟨G, ⟨hg, hs, hu⟩, rfl⟩ | ⟨G, ⟨hg, hs, hv⟩, rfl⟩)
        · exact ⟨G, ⟨hg, hs, Or.inl hu⟩, rfl⟩
        · exact ⟨G, ⟨hg, hs, Or.inr hv⟩, rfl⟩
    have hu : (S U).ncard ≤ 2^(2*m)*L :=
      (cyclic_nilpotent_hall_bound hr).trans
        (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega : m ≤ 2*m)))
    have hv₀ : (S V₀).ncard ≤ 2^(2*m)*L := hall_action_bound (by decide) hr
    have hv₁ : (S V₁).ncard ≤ 2^(2*m)*L := two_cyclic_layers_count odd.pos hr
    have hv : (S V).ncard ≤ 2^(2*m)*L + 2^(2*m)*L := by
      have sub : S V ⊆ S V₀ ∪ S V₁ := by
        rintro _ ⟨G, ⟨hg,hs,h | h⟩,rfl⟩
        · exact Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩
        · exact Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩
      have fin (F : FiniteGrp.{0} → Prop) : (S F).Finite :=
        (finite_classes q).subset (Set.image_mono (fun _ h => h.1))
      exact (Set.ncard_le_ncard sub ((fin _).union (fin _))).trans
        ((Set.ncard_union_le _ _).trans (Nat.add_le_add hv₀ hv₁))
    rw [cover]
    calc
      _ ≤ (S U).ncard + (S V).ncard := Set.ncard_union_le _ _
      _ ≤ 2^(2*m)*L + (2^(2*m)*L + 2^(2*m)*L) := Nat.add_le_add hu hv
      _ ≤ 2^(2*m+2)*L := by rw [pow_add]; nlinarith [Nat.zero_le (2^(2*m)*L)]
  have room : D*m+1 ≤ E*m-5 := by
    have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
    dsimp [E]; rw [Nat.add_mul]; omega
  have nn : (S N).ncard ≤ 2^(E*m-3)*L := by
    have fin (F : FiniteGrp.{0} → Prop) : (S F).Finite :=
      (finite_classes q).subset (Set.image_mono (fun _ h => h.1))
    have sub : S N ⊆ (S N₀ ∪ S Prod) ∪ S W := by
      rintro _ ⟨G,⟨hg,hs,(h | h) | h⟩,rfl⟩
      · exact Or.inl (Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩)
      · exact Or.inl (Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩)
      · exact Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩
    have w₁ : (S W₁).ncard ≤ 2^(E*m-5)*L := by
      apply le_trans _ (solvable_hall_induction_step hr odd hE ih)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono (fun _ h => h.1)))
      rintro _ ⟨G,⟨hg,hs,K,hn,nil,large,cop⟩,rfl⟩
      let _ : K.Normal := hn
      let _ : Group.IsSolvable G := hs
      obtain ⟨P,comp⟩ := Subgroup.exists_right_complement'_of_coprime cop
      refine ⟨G,⟨hg,FiniteGrp.of K,FiniteGrp.of P,nil,large,inferInstanceAs (Group.IsSolvable P),
        comp.symm.index_eq_card ▸ cop,_,⟨(SemidirectProduct.mulEquivSubgroup comp).symm⟩⟩,rfl⟩
    have w₂ : (S W₂).ncard ≤ 2^(E*m-6)*L := cyclic_kernel_induction_reserve hr odd hE ih
    have w₃ : (S (W₃ D)).ncard ≤ 2^(E*m-6)*L :=
      outer_cyclic_quotient_induction_step (B := D) hr odd (by dsimp [E]; omega) ih
    have w : (S W).ncard ≤ 2^(E*m-4)*L := by
      have cover : S W ⊆ S W₁ ∪ (S W₂ ∪ S (W₃ D)) := by
        rintro _ ⟨G,⟨hg,hs,h | h | h⟩,rfl⟩
        · exact Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩
        · exact Or.inr (Or.inl ⟨G,⟨hg,hs,h⟩,rfl⟩)
        · exact Or.inr (Or.inr ⟨G,⟨hg,hs,h⟩,rfl⟩)
      have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
      have em := Nat.mul_le_mul_left E hm
      have e₅ : E*m-6+1 = E*m-5 := by omega
      have e₄ : E*m-5+1 = E*m-4 := by omega
      calc
        _ ≤ (S W₁ ∪ (S W₂ ∪ S (W₃ D))).ncard := Set.ncard_le_ncard cover ((fin _).union ((fin _).union (fin _)))
        _ ≤ (S W₁).ncard + ((S W₂).ncard + (S (W₃ D)).ncard) :=
          (Set.ncard_union_le _ _).trans (Nat.add_le_add_left (Set.ncard_union_le _ _) _)
        _ ≤ 2^(E*m-5)*L + (2^(E*m-6)*L + 2^(E*m-6)*L) := Nat.add_le_add w₁ (Nat.add_le_add w₂ w₃)
        _ = _ := by rw [← e₄,pow_succ,← e₅,pow_succ]; ring
    have wp : (S Prod).ncard ≤ 2^(E*m-6)*L := by
      apply le_trans _ (coprime_product_induction_step hr odd hE ih)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
      rintro _ ⟨G,⟨hg,hs,A,B,ha,hb,cop,⟨e⟩⟩,rfl⟩
      let _ : Group.IsSolvable G := hs
      have sa : Group.IsSolvable A := Group.isSolvable_of_surjective
        (f := (MonoidHom.fst A B).comp e.toMonoidHom) (fun a => ⟨e.symm (a,1),by simp⟩)
      have sb : Group.IsSolvable B := Group.isSolvable_of_surjective
        (f := (MonoidHom.snd A B).comp e.toMonoidHom) (fun b => ⟨e.symm (1,b),by simp⟩)
      rcases le_total (Nat.card A) (Nat.card B) with hab | hba
      · exact ⟨G,⟨hg,hs,A,B,ha,hab,cop,sa,sb,⟨e⟩⟩,rfl⟩
      · exact ⟨G,⟨hg,hs,B,A,hb,hba,cop.symm,sb,sa,⟨e.trans MulEquiv.prodComm⟩⟩,rfl⟩
    have base : (S N₀ ∪ S Prod).ncard ≤ 2^(E*m-4)*L := by
      have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
      have em := Nat.mul_le_mul_left E hm
      have e₄ : E*m-5+1 = E*m-4 := by omega
      have n₀ : (S N₀).ncard ≤ 2^(E*m-5)*L := nn₀.trans (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide) (by have := Nat.mul_le_mul_right m h3; omega)))
      have np : (S Prod).ncard ≤ 2^(E*m-5)*L := wp.trans (Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide) (by omega)))
      calc
        _ ≤ _ := Set.ncard_union_le _ _
        _ ≤ _ := Nat.add_le_add n₀ np
        _ = _ := by rw [← e₄,pow_succ]; ring
    calc
      _ ≤ ((S N₀ ∪ S Prod) ∪ S W).ncard := Set.ncard_le_ncard sub (((fin _).union (fin _)).union (fin _))
      _ ≤ (S N₀ ∪ S Prod).ncard + (S W).ncard := Set.ncard_union_le _ _
      _ ≤ 2^(E*m-4)*L + 2^(E*m-4)*L := Nat.add_le_add base w
      _ = 2^((E*m-4)+1)*L := by rw [pow_succ]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  have combine (V Locus : FiniteGrp.{0} → Prop)
      (remaining : (S (fun G => V G ∧ ¬ Locus G)).ncard ≤ 2^(D*m)*L)
      (covered : (S (fun G => V G ∧ Locus G)).ncard ≤ 2^(E*m-6)*L) :
      (S V).ncard ≤ 2^(E*m-3)*L := by
    let R (G : FiniteGrp.{0}) := V G ∧ Locus G
    have fin (P : FiniteGrp.{0} → Prop) : (S P).Finite :=
      (finite_classes q).subset (Set.image_mono fun _ h => h.1)
    have cover : S V ⊆ S (fun G => V G ∧ ¬ Locus G) ∪ S R := by
      rintro _ ⟨G,⟨hg,hs,hx⟩,rfl⟩
      by_cases h : Locus G
      · exact Or.inr ⟨G,⟨hg,hs,hx,h⟩,rfl⟩
      · exact Or.inl ⟨G,⟨hg,hs,hx,h⟩,rfl⟩
    have first : D*m ≤ E*m-4 := by omega
    have second : E*m-6 ≤ E*m-4 := by omega
    apply (Set.ncard_le_ncard cover ((fin _).union (fin _))).trans
    apply (Set.ncard_union_le _ _).trans
    calc
      _ ≤ 2^(E*m-4)*L + 2^(E*m-4)*L := Nat.add_le_add
        (remaining.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) first)))
        (covered.trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) second)))
      _ = 2^(E*m-3)*L := by
        rw [show E*m-3 = (E*m-4)+1 by omega,pow_succ]; ring
  have aa : (S X).ncard ≤ 2^(E*m-3)*L := by
    let R (G : FiniteGrp.{0}) := X G ∧ Rel G
    have covered : (S R).ncard ≤ 2^(E*m-6)*L := by
      have ha : A+6 ≤ E := Nat.add_le_add_right ((le_max_left A B).trans (le_max_right ..)) 6
      apply le_trans _ (stabilizer_prime_part_induction_step hr odd ha ih)
      apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
      rintro _ ⟨G,⟨hg,hs,⟨_,_,_,comm⟩,N,hn,cyc,big,rest⟩,rfl⟩
      exact ⟨G,⟨hg,hs,N,hn,cyc,big,comm,rest⟩,rfl⟩
    exact combine X Rel remaining covered
  have bb : (S Y).ncard ≤ 2^(E*m-3)*L := by
    apply combine Y Mixed other
    have hb : B+6 ≤ E := Nat.add_le_add_right ((le_max_right A B).trans (le_max_right ..)) 6
    apply le_trans _ (central_lift_stabilizer_induction_step hr odd hb ih)
    apply Set.ncard_le_ncard _ ((finite_classes q).subset (Set.image_mono fun _ h => h.1))
    rintro _ ⟨G,⟨hg,hs,_,mixed⟩,rfl⟩
    exact ⟨G,⟨hg,hs,mixed⟩,rfl⟩
  have ff : (S F).ncard ≤ 2^(D*m)*L := by
    by_cases h : ∃ p l a : ℕ, p.Prime ∧ l.Prime ∧ p ≠ l ∧ 0 < a ∧ q = p^a*l
    · obtain ⟨p, l, a, hshape⟩ := h
      obtain ⟨hp, hl, hne, ha, hq⟩ := hshape
      have sub : S F ⊆ Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
          {G : FiniteGrp.{0} | Nat.card G = q ∧ ((∃ N : Subgroup G, N.Normal ∧ Nat.card N = p^a) ∨ Nat.card (Sylow l G) = 1)} := by
        rintro _ ⟨G, ⟨hc, _, hf⟩, rfl⟩
        exact ⟨G, ⟨hc, hf.2 p l a ⟨hp, hl, hne, ha, hq⟩⟩, rfl⟩
      apply (Set.ncard_le_ncard sub ((finite_classes q).subset
        (Set.image_mono (fun _ h => h.1)))).trans
      apply le_trans _ (mono 1 D h1)
      subst q
      simpa [m, L] using normal_hall_bound hp hl hne ha hr
    · have he : S F = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro _ ⟨G, ⟨_, _, hf⟩, _⟩
        exact h hf.1
      simp [he]
  have lift : 2^(D*m)*L ≤ 2^(E*m-3)*L := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  rw [union_eq]
  calc
    _ ≤ (S F).ncard + ((S N ∪ S Z) ∪ (S X ∪ S Y)).ncard := Set.ncard_union_le _ _
    _ ≤ (S F).ncard + ((S N ∪ S Z).ncard + (S X ∪ S Y).ncard) := Nat.add_le_add_left (Set.ncard_union_le _ _) _
    _ ≤ (S F).ncard + (((S N).ncard + (S Z).ncard) + ((S X).ncard + (S Y).ncard)) :=
      Nat.add_le_add_left (Nat.add_le_add (Set.ncard_union_le _ _) (Set.ncard_union_le _ _)) _
    _ ≤ 2^(E*m-3)*L + ((2^(E*m-3)*L + 2^(E*m-3)*L) + (2^(E*m-3)*L + 2^(E*m-3)*L)) :=
      Nat.add_le_add (ff.trans lift) (Nat.add_le_add (Nat.add_le_add nn (za.trans lift)) (Nat.add_le_add aa bb))
    _ ≤ 2^(E*m-3)*L*2^3 := by omega
    _ = 2^(E*m)*L := by
      rw [Nat.mul_right_comm,← pow_add]
      have hm : 1 ≤ m := Nat.pow_pos (Nat.succ_pos r)
      have := Nat.mul_le_mul_left E hm
      rw [Nat.sub_add_cancel (by omega : 3 ≤ E*m)]

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H2_R1_H3_R2_H2_R1
