import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1
import Mathlib

/-! Count solvable and nonsolvable isomorphism classes separately for each
prescribed set of Sylow types. The chief-series argument in the merged proof
by @nathanrblum-lab applies to solvable groups at every positive order.
The factor comparison and splitting of profiles come from R2 and R1 of this
same step. Credit: @Dolcruz. -/

open Erdos1160 CategoryTheory Finset

namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R3

def H1 : Prop := ∃ E : ℕ, ∀ n m : ℕ, 0 < n → n < 2^m →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}).ncard ≤
    2^(E*(m+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)

def H2 : Prop := ∃ E : ℕ, ∀ n m : ℕ, 0 < n → n < 2^m →
  (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ ¬ Group.IsSolvable G}).ncard ≤
    2^(E*(m+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p)

theorem profile_mul (g : ℕ → ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : a.Coprime b) :
    (∏ p ∈ (a*b).primeFactors, g (p ^ (a*b).factorization p)) =
      (∏ p ∈ a.primeFactors, g (p ^ a.factorization p)) *
      (∏ p ∈ b.primeFactors, g (p ^ b.factorization p)) := by
  have side {u v : ℕ} (hv : v ≠ 0) (huv : u.Coprime v) :
      ∀ p ∈ u.primeFactors, (u*v).factorization p = u.factorization p := by
    intro p hp
    have hnd : ¬ p ∣ v := fun hd => Finset.disjoint_left.mp huv.disjoint_primeFactors hp
      (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hd, hv⟩)
    rw [Nat.factorization_mul_of_coprime huv, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hnd, Nat.add_zero]
  rw [Nat.primeFactors_mul ha hb, Finset.prod_union hc.disjoint_primeFactors]
  congr 1
  · exact Finset.prod_congr rfl (fun p hp => by rw [side hb hc p hp])
  · exact Finset.prod_congr rfl (fun p hp => by rw [Nat.mul_comm a b, side ha hc.symm p hp])

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


theorem profiles_of_cases (hs : H1) (hu : H2) : ∃ E : ℕ, ∀ n m : ℕ, 0 < n → n < 2^m →
    g n ≤ 2^(E*(m+1)^2) * ∏ p ∈ n.primeFactors, g (p^n.factorization p) := by
  classical
  obtain ⟨A,sol⟩ := hs
  obtain ⟨B,nonsol⟩ := hu
  refine ⟨max A B + 1, fun n m hn hnm => ?_⟩
  let S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ Group.IsSolvable G}
  let U := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n ∧ ¬ Group.IsSolvable G}
  have cover : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n} = S ∪ U := by
    ext c
    constructor
    · rintro ⟨G,hG,rfl⟩
      by_cases h : Group.IsSolvable G
      · exact Or.inl ⟨G,⟨hG,h⟩,rfl⟩
      · exact Or.inr ⟨G,⟨hG,h⟩,rfl⟩
    · rintro (⟨G,⟨hG,_⟩,rfl⟩ | ⟨G,⟨hG,_⟩,rfl⟩) <;> exact ⟨G,hG,rfl⟩
  let F := ∏ p ∈ n.primeFactors, g (p^n.factorization p)
  have widen (x : ℕ) (hx : x ≤ max A B) :
      2^(x*(m+1)^2) * F ≤ 2^(max A B*(m+1)^2) * F :=
    Nat.mul_le_mul_right F (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hx))
  have absorb : 2 * 2^(max A B*(m+1)^2) ≤ 2^((max A B+1)*(m+1)^2) := by
    rw [Nat.mul_comm 2, ← pow_succ]
    apply Nat.pow_le_pow_right (by decide)
    nlinarith only [Nat.zero_le (m^2), Nat.zero_le m]
  unfold g
  rw [cover]
  calc
    _ ≤ S.ncard + U.ncard := Set.ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add ((sol n m hn hnm).trans (widen A (le_max_left ..)))
      ((nonsol n m hn hnm).trans (widen B (le_max_right ..)))
    _ = (2 * 2^(max A B*(m+1)^2))*F := by ring
    _ ≤ _ := Nat.mul_le_mul_right F absorb

theorem main : H1 → H2 → OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1.H3 := by
  intro hs hu
  obtain ⟨E, bound⟩ := profiles_of_cases hs hu
  refine ⟨27*E, fun a q m odd small => ?_⟩
  have hq : 0 < q := by obtain ⟨w,hw⟩ := odd; omega
  have htwo := Nat.two_pow_pos a
  have h := bound (2^a*q) m (Nat.mul_pos htwo hq) small
  rw [profile_mul g htwo.ne' hq.ne' (odd.coprime_two_left.pow_left a)] at h
  have hp := (Nat.pow_le_pow_left (h.trans (Nat.mul_le_mul_left _
    (Nat.mul_le_mul (product_lower (2^a) htwo) (product_lower q hq)))) 27)
  apply hp.trans_eq
  rw [mul_pow,mul_pow,← pow_mul]
  rw [show E*(m+1)^2*27 = (27*E)*(m+1)^2 by ring]
  exact Nat.mul_comm _ _

end OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H1_R1_H3_R3
