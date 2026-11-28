import FormalConjectures.ErdosProblems.«1160»
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Card

/-!
# Reduction Erdos1160.erdos_1160.R1 of Erdős Problem 1160

Proves Lovász direct-product cancellation for finite groups (`G × C_2 ≅ H × C_2 → G ≅ H`),
deduces `g n ≤ g (2 * n)` for all `n`, and reduces Erdős Problem 1160 to the dyadic interval
`(2 ^ (m - 1), 2 ^ m)` split into odd `n` (`H1`, Pantelidakis regime) and even `n` (`H2`, core
open case).
-/

namespace OMA.R_Erdos1160_erdos_1160_R1

def H1 : Prop :=
  ∀ n m : ℕ, 2 ≤ m → Odd n → 2 ^ (m - 1) < n → n < 2 ^ m → Erdos1160.g n ≤ Erdos1160.g (2 ^ m)

def H2 : Prop :=
  ∀ n m : ℕ, 3 ≤ m → Even n → 2 ^ (m - 1) < n → n < 2 ^ m → Erdos1160.g n ≤ Erdos1160.g (2 ^ m)

lemma monoidHom_equiv_sigma_inj (K A : Type) [Group K] [Group A] :
    Nonempty ((K →* A) ≃
      Σ N : { N : Subgroup K // N.Normal },
        letI := N.2
        { f : K ⧸ N.1 →* A // Function.Injective f }) := by
  refine ⟨{
    toFun := fun φ => ⟨⟨φ.ker, φ.normal_ker⟩, ⟨QuotientGroup.kerLift φ, QuotientGroup.kerLift_injective φ⟩⟩
    invFun := fun p =>
      letI := p.1.2
      p.2.1.comp (QuotientGroup.mk' p.1.1)
    left_inv := fun φ => by
      ext x
      rfl
    right_inv := fun ⟨⟨N, hN⟩, ⟨ψ, hψ⟩⟩ => by
      have hker : (ψ.comp (QuotientGroup.mk' N)).ker = N := by
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
        constructor
        · intro hx
          have h1 : (x : K ⧸ N) = 1 := hψ (hx.trans (map_one ψ).symm)
          exact (QuotientGroup.eq_one_iff x).mp h1
        · intro hx
          have h1 : (x : K ⧸ N) = 1 := (QuotientGroup.eq_one_iff x).mpr hx
          rw [h1, map_one]
      have hsub : (⟨(ψ.comp (QuotientGroup.mk' N)).ker, (ψ.comp (QuotientGroup.mk' N)).normal_ker⟩ :
          { N : Subgroup K // N.Normal }) = ⟨N, hN⟩ := Subtype.ext hker
      refine Sigma.ext hsub ?_
      have hcast : ∀ (M : { N : Subgroup K // N.Normal })
          (_ : M = ⟨N, hN⟩)
          (f : letI := M.2; { f : K ⧸ M.1 →* A // Function.Injective f }),
          (∀ x : K, f.1 (QuotientGroup.mk x) = ψ (QuotientGroup.mk x)) →
          HEq f (⟨ψ, hψ⟩ : { f : K ⧸ N →* A // Function.Injective f }) := by
        rintro _ rfl f hf
        refine heq_of_eq (Subtype.ext ?_)
        ext x
        exact hf x
      exact hcast _ hsub _ (fun x => rfl)
  }⟩

lemma card_inj_eq_of_card_hom_eq {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (hhom : ∀ (K : Type) [Group K] [Finite K], Nat.card (K →* G) = Nat.card (K →* H)) :
    ∀ n (K : Type) [Group K] [Finite K], Nat.card K = n →
      Nat.card { f : K →* G // Function.Injective f } =
        Nat.card { f : K →* H // Function.Injective f } := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hK
    classical
    have : Fintype K := Fintype.ofFinite K
    have : Fintype G := Fintype.ofFinite G
    have : Fintype H := Fintype.ofFinite H
    have : Finite (K →* G) := Finite.of_injective _ DFunLike.coe_injective
    have : Finite (K →* H) := Finite.of_injective _ DFunLike.coe_injective
    have : Fintype (K →* G) := Fintype.ofFinite _
    have : Fintype (K →* H) := Fintype.ofFinite _
    have : Fintype { N : Subgroup K // N.Normal } := Fintype.ofFinite _
    have : ∀ N : { N : Subgroup K // N.Normal },
        letI := N.2
        Fintype { f : K ⧸ N.1 →* G // Function.Injective f } := fun N => by
      have := N.2
      have : Finite (K ⧸ N.1 →* G) := Finite.of_injective _ DFunLike.coe_injective
      exact Fintype.ofFinite _
    have : ∀ N : { N : Subgroup K // N.Normal },
        letI := N.2
        Fintype { f : K ⧸ N.1 →* H // Function.Injective f } := fun N => by
      have := N.2
      have : Finite (K ⧸ N.1 →* H) := Finite.of_injective _ DFunLike.coe_injective
      exact Fintype.ofFinite _
    obtain ⟨eG⟩ := monoidHom_equiv_sigma_inj K G
    obtain ⟨eH⟩ := monoidHom_equiv_sigma_inj K H
    have hsum :
        ∑ N : { N : Subgroup K // N.Normal },
          Fintype.card (letI := N.2; { f : K ⧸ N.1 →* G // Function.Injective f }) =
        ∑ N : { N : Subgroup K // N.Normal },
          Fintype.card (letI := N.2; { f : K ⧸ N.1 →* H // Function.Injective f }) := by
      rw [← Fintype.card_sigma, ← Fintype.card_sigma,
          ← Fintype.card_congr eG, ← Fintype.card_congr eH,
          ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact hhom K
    let botN : { N : Subgroup K // N.Normal } := ⟨⊥, inferInstance⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ botN),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ botN)] at hsum
    have hrest :
        ∑ N ∈ Finset.univ.erase botN,
          Fintype.card (letI := N.2; { f : K ⧸ N.1 →* G // Function.Injective f }) =
        ∑ N ∈ Finset.univ.erase botN,
          Fintype.card (letI := N.2; { f : K ⧸ N.1 →* H // Function.Injective f }) := by
      refine Finset.sum_congr rfl fun N hN => ?_
      have := N.2
      have hne : N.1 ≠ ⊥ := by
        intro h
        exact (Finset.mem_erase.mp hN).1 (Subtype.ext h)
      have hcardN_gt : 1 < Nat.card N.1 := by
        have hpos : 0 < Nat.card N.1 := Nat.card_pos
        by_contra hle
        have heq1 : Nat.card N.1 = 1 := by omega
        have : Subsingleton N.1 := (Nat.card_eq_one_iff_unique.mp heq1).1
        apply hne
        ext x
        simp only [Subgroup.mem_bot]
        constructor
        · intro hx
          exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : N.1) 1)
        · intro hx
          rw [hx]
          exact N.1.one_mem
      have hlt : Nat.card (K ⧸ N.1) < n := by
        rw [← hK]
        have hmul : Nat.card (K ⧸ N.1) * Nat.card N.1 = Nat.card K := by
          rw [← Subgroup.index_eq_card, mul_comm]
          exact Subgroup.card_mul_index N.1
        have hposQ : 0 < Nat.card (K ⧸ N.1) := Nat.card_pos
        nlinarith
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact ih (Nat.card (K ⧸ N.1)) hlt (K ⧸ N.1) rfl
    have hbot :
        Fintype.card (letI := botN.2; { f : K ⧸ botN.1 →* G // Function.Injective f }) =
        Fintype.card (letI := botN.2; { f : K ⧸ botN.1 →* H // Function.Injective f }) := by
      omega
    have hqG : { f : K ⧸ (⊥ : Subgroup K) →* G // Function.Injective f } ≃
        { f : K →* G // Function.Injective f } := {
      toFun := fun f => ⟨f.1.comp (QuotientGroup.quotientBot.symm.toMonoidHom),
        f.2.comp QuotientGroup.quotientBot.symm.injective⟩
      invFun := fun f => ⟨f.1.comp (QuotientGroup.quotientBot.toMonoidHom),
        f.2.comp QuotientGroup.quotientBot.injective⟩
      left_inv := fun f => by
        ext q
        change f.1 (QuotientGroup.quotientBot.symm (QuotientGroup.quotientBot q)) = f.1 q
        rw [MulEquiv.symm_apply_apply]
      right_inv := fun f => by
        ext x
        change f.1 (QuotientGroup.quotientBot (QuotientGroup.quotientBot.symm x)) = f.1 x
        rw [MulEquiv.apply_symm_apply]
    }
    have hqH : { f : K ⧸ (⊥ : Subgroup K) →* H // Function.Injective f } ≃
        { f : K →* H // Function.Injective f } := {
      toFun := fun f => ⟨f.1.comp (QuotientGroup.quotientBot.symm.toMonoidHom),
        f.2.comp QuotientGroup.quotientBot.symm.injective⟩
      invFun := fun f => ⟨f.1.comp (QuotientGroup.quotientBot.toMonoidHom),
        f.2.comp QuotientGroup.quotientBot.injective⟩
      left_inv := fun f => by
        ext q
        change f.1 (QuotientGroup.quotientBot.symm (QuotientGroup.quotientBot q)) = f.1 q
        rw [MulEquiv.symm_apply_apply]
      right_inv := fun f => by
        ext x
        change f.1 (QuotientGroup.quotientBot (QuotientGroup.quotientBot.symm x)) = f.1 x
        rw [MulEquiv.apply_symm_apply]
    }
    have : Finite (K ⧸ (⊥ : Subgroup K) →* G) := Finite.of_injective _ DFunLike.coe_injective
    have : Finite (K ⧸ (⊥ : Subgroup K) →* H) := Finite.of_injective _ DFunLike.coe_injective
    have : Fintype { f : K ⧸ (⊥ : Subgroup K) →* G // Function.Injective f } := Fintype.ofFinite _
    have : Fintype { f : K ⧸ (⊥ : Subgroup K) →* H // Function.Injective f } := Fintype.ofFinite _
    rw [Nat.card_congr hqG.symm, Nat.card_congr hqH.symm,
        Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    convert hbot

lemma finite_group_prod_cancel {G H C : Type} [Group G] [Group H] [Group C]
    [Finite G] [Finite H] [Finite C] (e : G × C ≃* H × C) : Nonempty (G ≃* H) := by
  have hcard : Nat.card G = Nat.card H := by
    have h1 : Nat.card (G × C) = Nat.card (H × C) := Nat.card_congr e.toEquiv
    rw [Nat.card_prod, Nat.card_prod] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hhom : ∀ (K : Type) [Group K] [Finite K], Nat.card (K →* G) = Nat.card (K →* H) := by
    intro K _ _
    have eProdG : (K →* G × C) ≃ (K →* G) × (K →* C) := {
      toFun := fun f => ((MonoidHom.fst G C).comp f, (MonoidHom.snd G C).comp f)
      invFun := fun p => p.1.prod p.2
      left_inv := fun f => by ext x <;> rfl
      right_inv := fun p => by ext x <;> rfl
    }
    have eProdH : (K →* H × C) ≃ (K →* H) × (K →* C) := {
      toFun := fun f => ((MonoidHom.fst H C).comp f, (MonoidHom.snd H C).comp f)
      invFun := fun p => p.1.prod p.2
      left_inv := fun f => by ext x <;> rfl
      right_inv := fun p => by ext x <;> rfl
    }
    have eHom : (K →* G × C) ≃ (K →* H × C) := {
      toFun := fun f => e.toMonoidHom.comp f
      invFun := fun f => e.symm.toMonoidHom.comp f
      left_inv := fun f => by ext x <;> simp
      right_inv := fun f => by ext x <;> simp
    }
    have h1 : Nat.card ((K →* G) × (K →* C)) = Nat.card ((K →* H) × (K →* C)) :=
      Nat.card_congr (eProdG.symm.trans (eHom.trans eProdH))
    rw [Nat.card_prod, Nat.card_prod] at h1
    have : Finite (K →* C) := Finite.of_injective _ DFunLike.coe_injective
    have : Nonempty (K →* C) := ⟨1⟩
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hinj := card_inj_eq_of_card_hom_eq hhom (Nat.card G) G rfl
  have : Finite (G →* G) := Finite.of_injective _ DFunLike.coe_injective
  have : Nonempty { f : G →* G // Function.Injective f } := ⟨⟨MonoidHom.id G, Function.injective_id⟩⟩
  have hpos : 0 < Nat.card { f : G →* H // Function.Injective f } := by
    rw [← hinj]
    exact Nat.card_pos
  have : Nonempty { f : G →* H // Function.Injective f } := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨f, hf⟩ := Classical.arbitrary { f : G →* H // Function.Injective f }
  have hbij : Function.Bijective f := by
    have := Fintype.ofFinite G
    have := Fintype.ofFinite H
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hf, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  exact ⟨MulEquiv.ofBijective f hbij⟩

lemma finiteGrp_iso_of_mulEquiv {G H : FiniteGrp.{0}} (e : G ≃* H) : Nonempty (G ≅ H) :=
  ⟨{ hom := FiniteGrp.ofHom e.toMonoidHom
     inv := FiniteGrp.ofHom e.symm.toMonoidHom
     hom_inv_id := by ext x; exact e.symm_apply_apply x
     inv_hom_id := by ext x; exact e.apply_symm_apply x }⟩

lemma mulEquiv_of_finiteGrp_iso {G H : FiniteGrp.{0}} (e : G ≅ H) : Nonempty (G ≃* H) :=
  ⟨{ toFun := e.hom.hom.hom
     invFun := e.inv.hom.hom
     left_inv := fun x => congrArg (fun f : G ⟶ G => f.hom.hom x) e.hom_inv_id
     right_inv := fun x => congrArg (fun f : H ⟶ H => f.hom.hom x) e.inv_hom_id
     map_mul' := e.hom.hom.hom.map_mul }⟩

lemma finite_groups_of_order (k : ℕ) :
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k}).Finite := by
  classical
  let mkQ : (Fin k → Fin k → Fin k) → Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
    fun m => if h : ∃ g : Group (Fin k), g.mul = m then
      {Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) (@FiniteGrp.of (Fin k) h.choose _)}
    else ∅
  have hfin : (⋃ m : Fin k → Fin k → Fin k, mkQ m).Finite :=
    Set.finite_iUnion fun m => by
      dsimp only [mkQ]
      split_ifs
      · exact Set.finite_singleton _
      · exact Set.finite_empty
  refine hfin.subset ?_
  rintro _ ⟨G, hG, rfl⟩
  have e : G ≃ Fin k := Finite.equivFinOfCardEq hG
  let gFin : Group (Fin k) := e.symm.group
  have hex : ∃ g : Group (Fin k), g.mul = gFin.mul := ⟨gFin, rfl⟩
  refine Set.mem_iUnion.mpr ⟨gFin.mul, ?_⟩
  dsimp only [mkQ]
  rw [dif_pos hex, Set.mem_singleton_iff]
  apply Quotient.sound
  have iso : G ≃* @FiniteGrp.of (Fin k) hex.choose _ :=
    { toEquiv := e
      map_mul' := fun x y => by
        change e (x * y) = hex.choose.mul (e x) (e y)
        rw [hex.choose_spec]
        change e (x * y) = e (e.symm (e x) * e.symm (e y))
        simp }
  exact finiteGrp_iso_of_mulEquiv iso

lemma g_le_g_two_mul (n : ℕ) : Erdos1160.g n ≤ Erdos1160.g (2 * n) := by
  let S (k : ℕ) : Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})) :=
    Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = k}
  let Φ : Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) →
      Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) :=
    Quotient.lift
      (fun G => Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})
        (FiniteGrp.of (G × Multiplicative (ZMod 2))))
      (fun G H ⟨e⟩ => by
        apply Quotient.sound
        obtain ⟨eMul⟩ := mulEquiv_of_finiteGrp_iso e
        exact finiteGrp_iso_of_mulEquiv
          (eMul.prodCongr (MulEquiv.refl (Multiplicative (ZMod 2)))))
  have hmaps : Set.MapsTo Φ (S n) (S (2 * n)) := by
    rintro _ ⟨G, hG, rfl⟩
    refine ⟨FiniteGrp.of (G × Multiplicative (ZMod 2)), ?_, rfl⟩
    change Nat.card (G × Multiplicative (ZMod 2)) = 2 * n
    rw [Nat.card_prod, hG]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    rw [h2, mul_comm]
  have hinj : Set.InjOn Φ (S n) := by
    rintro _ ⟨G, _, rfl⟩ _ ⟨H, _, rfl⟩ heq
    have ⟨e⟩ := Quotient.exact heq
    obtain ⟨eMul⟩ := mulEquiv_of_finiteGrp_iso e
    obtain ⟨eGH⟩ := finite_group_prod_cancel eMul
    exact Quotient.sound (finiteGrp_iso_of_mulEquiv eGH)
  exact Set.ncard_le_ncard_of_injOn Φ hmaps hinj (finite_groups_of_order (2 * n))

theorem main : H1 → H2 → type_of% @Erdos1160.erdos_1160 := by
  intro h1 h2 n m hn hle
  suffices ∀ d : ℕ, ∀ n : ℕ, 0 < n → n ≤ 2 ^ m → 2 ^ m - n ≤ d →
      Erdos1160.g n ≤ Erdos1160.g (2 ^ m) by
    exact this (2 ^ m - n) n hn hle le_rfl
  intro d
  induction d with
  | zero =>
    intro n _ hle hdiff
    have heq : n = 2 ^ m := by omega
    rw [heq]
  | succ d ih =>
    intro n hn hle hdiff
    by_cases heq : n = 2 ^ m
    · rw [heq]
    · by_cases h2n : 2 * n ≤ 2 ^ m
      · exact (g_le_g_two_mul n).trans (ih (2 * n) (by omega) h2n (by omega))
      · have hlt : n < 2 ^ m := lt_of_le_of_ne hle heq
        have hm2 : 2 ≤ m := by
          by_contra hm
          interval_cases m <;> omega
        have hgt : 2 ^ (m - 1) < n := by
          have hpow : 2 * 2 ^ (m - 1) = 2 ^ m := by
            rw [← pow_succ', Nat.sub_add_cancel (by omega)]
          omega
        rcases Nat.even_or_odd n with heven | hodd
        · have hm3 : 3 ≤ m := by
            by_contra hm
            have hm2' : m = 2 := by omega
            subst hm2'
            obtain ⟨k, hk⟩ := heven
            omega
          exact h2 n m hm3 heven hgt hlt
        · exact h1 n m hm2 hodd hgt hlt

end OMA.R_Erdos1160_erdos_1160_R1
