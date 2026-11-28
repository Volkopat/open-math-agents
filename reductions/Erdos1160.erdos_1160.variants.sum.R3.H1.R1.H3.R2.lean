import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.GroupTheory.Sylow
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
-- Formalization for @michelzerasafadaum-gif.
-- Sylow-type enumeration: L. Pyber, Enumerating finite groups of given order (1993).
-- Dyadic application: N. Su and B. Xia, arXiv:2610.11092v1, Section 8.

open CategoryTheory Finset Erdos1160
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R2
private theorem coprime_map_eq_one {A B : Type*} [Group A] [Group B]
    (hc : (Nat.card A).Coprime (Nat.card B)) (f : A →* B) (x : A) : f x = 1 := by
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hc ((orderOf_map_dvd f x).trans (orderOf_dvd_natCard x))
    (orderOf_dvd_natCard (f x))

/-- Recovers the left factor of a direct product from its isomorphism type
when the orders of opposite factors are coprime in both directions. -/
private theorem recoverLeft {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    (e : A × B ≃* C × D) (hc : (Nat.card A).Coprime (Nat.card D))
    (hc' : (Nat.card C).Coprime (Nat.card B)) : Nonempty (A ≃* C) := by
  let f := (MonoidHom.fst C D).comp (e.toMonoidHom.comp (MonoidHom.inl A B))
  let g := (MonoidHom.fst A B).comp (e.symm.toMonoidHom.comp (MonoidHom.inl C D))
  have hd (x : A) : e (x,1) = (f x,1) := Prod.ext rfl
    (coprime_map_eq_one hc ((MonoidHom.snd C D).comp (e.toMonoidHom.comp (MonoidHom.inl A B))) x)
  have hd' (y : C) : e.symm (y,1) = (g y,1) := Prod.ext rfl
    (coprime_map_eq_one hc' ((MonoidHom.snd A B).comp (e.symm.toMonoidHom.comp (MonoidHom.inl C D))) y)
  refine ⟨{ toFun := f, invFun := g, map_mul' := f.map_mul, left_inv := ?_, right_inv := ?_ }⟩
  · intro x
    change (e.symm (f x,1)).1 = x
    rw [← hd, e.symm_apply_apply]
  · intro y
    change (e (g y,1)).1 = y
    rw [← hd', e.apply_symm_apply]

theorem aut_card_of_generating_pair {S : Type*} [Group S] [Finite S] {u v : S}
    (hgen : Subgroup.closure ({u,v} : Set S) = ⊤) : Nat.card (MulAut S) ≤ Nat.card S ^ 2 := by
  let code (a : MulAut S) := (a u, a v)
  have inj : Function.Injective code := by
    intro a b he
    have eq : a.toMonoidHom = b.toMonoidHom := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      intro x hx
      rcases hx with rfl|hx
      · exact congrArg Prod.fst he
      · obtain rfl : x = v := hx
        exact congrArg Prod.snd he
    ext x
    exact DFunLike.congr_fun eq x
  simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective code inj


/-- Direct products of groups of pairwise coprime orders retain each factor's isomorphism type. -/
theorem product_lower (n : ℕ) (hn : 0 < n) :
    (∏ p ∈ n.primeFactors, g (p ^ n.factorization p)) ≤ g n := by
  classical
  let OrderClasses (s : ℕ) := ↥(Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = s})
  let orderRepresentative {s : ℕ} (i : OrderClasses s) : FiniteGrp.{0} := i.property.choose
  have orderRepresentative_spec {s : ℕ} (i : OrderClasses s) :
      Nat.card (orderRepresentative i) = s ∧
        Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (orderRepresentative i) = i.val :=
    i.property.choose_spec
  have rep_distinct {n : ℕ} {i j : OrderClasses n}
      (e : Nonempty (orderRepresentative i ≃* orderRepresentative j)) : i = j := by
    obtain ⟨e⟩ := e
    apply Subtype.ext
    rw [← (orderRepresentative_spec i).2, ← (orderRepresentative_spec j).2]
    exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
      (MulEquiv.toGrpIso (X := (orderRepresentative i).toGrp) (Y := (orderRepresentative j).toGrp) e)⟩

  letI orderClassesFintype (n : ℕ) : Finite (OrderClasses n) := by
    classical
    letI (i : OrderClasses n) : Fintype (orderRepresentative i) := Fintype.ofFinite _
    let e (i : OrderClasses n) : orderRepresentative i ≃ Fin n :=
      Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, (orderRepresentative_spec i).1])
    let tbl (i : OrderClasses n) (a b : Fin n) := e i ((e i).symm a * (e i).symm b)
    apply Finite.of_injective tbl
    intro i j h
    let u := (e i).trans (e j).symm
    apply rep_distinct
    refine ⟨{ toEquiv := u, map_mul' := ?_ }⟩
    intro x y
    apply (e j).injective
    have hh := congrFun (congrFun h (e i x)) (e i y)
    simpa [tbl, u] using hh

  have coprime_product_count {n m : ℕ} (hc : n.Coprime m) :
      Nat.card (OrderClasses n) * Nat.card (OrderClasses m) ≤ Nat.card (OrderClasses (n*m)) := by
    classical
    let P (i : OrderClasses n × OrderClasses m) :=
      FiniteGrp.of (orderRepresentative i.1 × orderRepresentative i.2)
    have hs (i) : Nat.card (P i) = n*m := by
      change Nat.card (orderRepresentative i.1 × orderRepresentative i.2) = _
      rw [Nat.card_prod, (orderRepresentative_spec i.1).1, (orderRepresentative_spec i.2).1]
    let F (i : OrderClasses n × OrderClasses m) : OrderClasses (n*m) :=
      ⟨Quotient.mk _ (P i), P i, hs i, rfl⟩
    rw [← Nat.card_prod]
    apply Nat.card_le_card_of_injective F
    intro i j h
    have hh : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (P i) = Quotient.mk _ (P j) :=
      congrArg Subtype.val h
    let v : P i ≅ P j := Classical.choice (Quotient.exact hh)
    let e : (orderRepresentative i.1 × orderRepresentative i.2) ≃*
        (orderRepresentative j.1 × orderRepresentative j.2) :=
      Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso v)
    have cross (u : OrderClasses n) (v : OrderClasses m) :
        (Nat.card (orderRepresentative u)).Coprime (Nat.card (orderRepresentative v)) := by
      rwa [(orderRepresentative_spec u).1, (orderRepresentative_spec v).1]
    apply Prod.ext
    · exact rep_distinct (recoverLeft e (cross _ _) (cross _ _))
    · let swap := MulEquiv.prodComm.trans (e.trans MulEquiv.prodComm)
      exact rep_distinct (recoverLeft swap (cross _ _).symm (cross _ _).symm)

  let S := n.primeFactors
  let w (p : ℕ) := p ^ n.factorization p
  have bound (s : Finset ℕ) (hs : s ⊆ S) :
      (∏ p ∈ s, Nat.card (OrderClasses (w p))) ≤ Nat.card (OrderClasses (∏ p ∈ s, w p)) := by
    induction s using Finset.induction_on with
    | empty =>
      let G := FiniteGrp.of PUnit.{1}
      let t : OrderClasses 1 := ⟨Quotient.mk _ G, G, by change Nat.card PUnit.{1} = 1; simp, rfl⟩
      let : Nonempty (OrderClasses 1) := ⟨t⟩
      simpa using (Nat.succ_le_of_lt (Nat.card_pos (α := OrderClasses 1)))
    | @insert p s hps ih =>
      have hs' : s ⊆ S := fun j hj => hs (mem_insert_of_mem hj)
      have hp := Nat.prime_of_mem_primeFactors (hs (mem_insert_self ..))
      have cop : (w p).Coprime (∏ j ∈ s, w j) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro j hj
        have hpj : p ≠ j := fun h => hps (h ▸ hj)
        exact ((Nat.coprime_primes hp (Nat.prime_of_mem_primeFactors (hs' hj))).mpr hpj).pow_left _ |>.pow_right _
      rw [prod_insert hps, prod_insert hps]
      exact (Nat.mul_le_mul_left _ (ih hs')).trans (coprime_product_count cop)
  have hprod : (∏ p ∈ S, w p) = n := Nat.prod_factorization_pow_eq_self hn.ne'
  change (∏ p ∈ S, Nat.card (OrderClasses (w p))) ≤ Nat.card (OrderClasses n)
  simpa only [hprod] using bound S (fun _ h => h)


/-- A finite nonabelian simple group has a generating pair. -/
def H1 : Prop := ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], ¬ IsMulCommutative S →
  ∃ u v : S, Subgroup.closure ({u,v} : Set S) = ⊤

/-- At most two nonisomorphic finite nonabelian simple groups have the same order. -/
def H2 : Prop := ∀ s : ℕ, Nat.card ({z : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = s} // IsSimpleGroup z.property.choose ∧ ¬ IsMulCommutative z.property.choose}) ≤ 2

/-- Polynomial control of simple groups and their automorphisms bounds the cost of
assembling independently prescribed Sylow types into a group of mixed order. -/
def H3 : Prop :=
  let simples := fun s : ℕ => {z : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = s} // IsSimpleGroup z.property.choose ∧ ¬ IsMulCommutative z.property.choose}
  (∀ s : ℕ, Nat.card (simples s) ≤ s^2) →
  (∀ (s : ℕ) (z : simples s), Nat.card (MulAut z.val.property.choose) ≤ s^2) →
  ∃ C : ℕ, ∀ a q m : ℕ, Odd q → 2^a*q < 2^m →
    g (2^a*q) ≤ (g (2^a)*(∏ p ∈ q.primeFactors, g (p^q.factorization p)))*2^(C*(m+1)^2)

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.H3 := by
  classical
  intro pair types assembly
  let simples := fun s : ℕ => {z : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) '' {G : FiniteGrp.{0} | Nat.card G = s} // IsSimpleGroup z.property.choose ∧ ¬ IsMulCommutative z.property.choose}
  have census (s : ℕ) : Nat.card (simples s) ≤ s^2 := by
    by_cases small : s < 2
    · have : IsEmpty (simples s) := by
        constructor
        intro z
        have := z.property.1
        have h : 1 < Nat.card z.val.property.choose := Finite.one_lt_card
        rw [z.val.property.choose_spec.1] at h
        omega
      simp
    · have : 2 ≤ s := by omega
      exact (types s).trans (by nlinarith)
  have aut (s : ℕ) (z : simples s) : Nat.card (MulAut z.val.property.choose) ≤ s^2 := by
    have := z.property.1
    obtain ⟨u,v,huv⟩ := pair z.val.property.choose z.property.2
    have cardEq : Nat.card (z.val.property.choose : FiniteGrp.{0}) = s := z.val.property.choose_spec.1
    exact (aut_card_of_generating_pair huv).trans_eq (congrArg (fun x : ℕ => x^2) cardEq)
  obtain ⟨C,upper⟩ := assembly census aut
  refine ⟨C*27,?_⟩
  intro a q m hq hlt
  have qpos : 0 < q := by obtain ⟨k,hk⟩ := hq; omega
  have cap := (upper a q m hq hlt).trans (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left (g (2^a)) (product_lower q qpos)))
  calc
    _ ≤ ((g (2^a)*g q)*2^(C*(m+1)^2))^27 := Nat.pow_le_pow_left cap _
    _ = _ := by
      rw [mul_pow, mul_pow, ← pow_mul, show C * (m+1)^2 * 27 = C*27*(m+1)^2 by ring]

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R2
