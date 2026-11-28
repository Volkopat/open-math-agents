import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1
import Mathlib

/-!
Aschbacher–Guralnick's finite-group generation theorem (Theorem A in
Solvable generation of groups and Sylow subgroups of the lower central
series, Journal of Algebra 77, 1982) implies the one-extra-element
generation bound used by Roney-Dougal and Tracey, Theorem 8.4.

The hypotheses provide the conjugate Sylow pair in powers of a
nonabelian simple group and the direct-power structure of nonsolvable
minimal normal subgroups. The proof handles the finite-order induction
using quotient lifting and the proper Sylow normalizer.
-/

namespace OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1

open Subgroup

private theorem conjugate_map {G K : Type} [Group G] [Group K]
    (f : G →* K) (x : G) (S : Subgroup G) :
    (S.map (MulAut.conj x).toMonoidHom).map f =
      (S.map f).map (MulAut.conj (f x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem conjugate_mono {G : Type} [Group G] {x : G} {S H : Subgroup G}
    (hx : x ∈ H) (hS : S ≤ H) : S.map (MulAut.conj x).toMonoidHom ≤ H := by
  rintro _ ⟨a, ha, rfl⟩
  exact H.mul_mem (H.mul_mem hx (hS ha)) (H.inv_mem hx)

private theorem solvable_subgroupOf {G : Type} [Group G] (Q A : Subgroup G)
    [Group.IsSolvable Q] : Group.IsSolvable (Q.subgroupOf A) := by
  let f : Q.subgroupOf A →* Q :=
    { toFun := fun x => ⟨x.1.1,x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := f)
    (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun y : Q => (y : G)) h)))

private theorem solvable_sup_normal {G : Type} [Group G] (A Q : Subgroup G)
    [Q.Normal] [Group.IsSolvable A] [Group.IsSolvable Q] :
    Group.IsSolvable (A ⊔ Q : Subgroup G) := by
  have e := QuotientGroup.quotientInfEquivProdNormalQuotient A Q
  let _ : Group.IsSolvable (Q.subgroupOf (A ⊔ Q)) := solvable_subgroupOf Q _
  let _ : Group.IsSolvable ((A ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (A ⊔ Q)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf (A ⊔ Q))).mpr
    ⟨inferInstance,inferInstance⟩

private theorem lift_solvable_quotient {G : Type} [Group G] (M : Subgroup G) [M.Normal]
    [Group.IsSolvable M] {A : Subgroup (G ⧸ M)} (hA : Group.IsSolvable A) (x : G)
    (hgen : A ⊔ A.map (MulAut.conj (QuotientGroup.mk' M x)).toMonoidHom = ⊤) :
    ∃ S : Subgroup G, Group.IsSolvable S ∧ S ⊔ S.map (MulAut.conj x).toMonoidHom = ⊤ := by
  let φ := QuotientGroup.mk' M
  let S := A.comap φ
  have hm : M ≤ S := by
    intro y hy
    change φ y ∈ A
    have hy' : y ∈ φ.ker := (QuotientGroup.ker_mk' M).symm ▸ hy
    rw [MonoidHom.mem_ker.mp hy']
    exact A.one_mem
  let f : S →* A := (φ.comp S.subtype).codRestrict A fun y => y.2
  let _ : Group.IsSolvable A := hA
  have hS : Group.IsSolvable S := by
    apply Group.isSolvable_of_ker_le_range (Subgroup.inclusion hm) f
    intro y hy
    have hy' : φ y.1 = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
    exact ⟨⟨y.1, (QuotientGroup.ker_mk' M) ▸ MonoidHom.mem_ker.mpr hy'⟩, Subtype.ext rfl⟩
  have hmap : S.map φ = A :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have htop : (S ⊔ S.map (MulAut.conj x).toMonoidHom).map φ = ⊤ := by
    rw [Subgroup.map_sup, conjugate_map, hmap]
    exact hgen
  refine ⟨S,hS,?_⟩
  have hk : φ.ker ≤ S ⊔ S.map (MulAut.conj x).toMonoidHom := by
    rw [QuotientGroup.ker_mk' M]
    exact hm.trans le_sup_left
  rw [← Subgroup.comap_map_eq_self hk, htop, Subgroup.comap_top]

private theorem lift_solvable_normalizer {G : Type} [Group G] {Q M : Subgroup G}
    [Group.IsSolvable Q] (x : G) (hx : x ∈ M)
    (hM : Q ⊔ Q.map (MulAut.conj x).toMonoidHom = M)
    (hfratt : normalizer (Q : Set G) ⊔ M = ⊤)
    (hN : ∃ S : Subgroup (normalizer (Q : Set G)), Group.IsSolvable S ∧
      ∃ z : normalizer (Q : Set G), S ⊔ S.map (MulAut.conj z).toMonoidHom = ⊤) :
    ∃ A : Subgroup G, Group.IsSolvable A ∧
      ∃ y : G, A ⊔ A.map (MulAut.conj y).toMonoidHom = ⊤ := by
  let N := normalizer (Q : Set G)
  obtain ⟨S,hS,z,hgen⟩ := hN
  let R := Q.subgroupOf N
  let A : Subgroup G := (S ⊔ R).map N.subtype
  let y : G := x * z
  let L : Subgroup G := A ⊔ A.map (MulAut.conj y).toMonoidHom
  have hQA : Q ≤ A := by
    have hR : R.map N.subtype = Q := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left Subgroup.le_normalizer]
    rw [← hR]
    exact Subgroup.map_mono le_sup_right
  have hS'A : S.map N.subtype ≤ A := Subgroup.map_mono le_sup_left
  have hQL : Q ≤ L := hQA.trans le_sup_left
  have hAR : A.map (MulAut.conj y).toMonoidHom ≤ L := le_sup_right
  have hconjQL : Q.map (MulAut.conj x).toMonoidHom ≤ L := by
    rintro _ ⟨q,hq,rfl⟩
    apply hAR
    have hzInv : (↑z : G)⁻¹ ∈ normalizer (Q : Set G) := N.inv_mem z.2
    have hq' := (Subgroup.mem_normalizer_iff.mp hzInv q).mp hq
    refine ⟨(↑z : G)⁻¹ * q * ↑z, hQA (by simpa only [inv_inv] using hq'), ?_⟩
    simp only [y, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hML : M ≤ L := hM ▸ sup_le hQL hconjQL
  have hxL : x ∈ L := hML hx
  have hconjL : (S.map N.subtype).map (MulAut.conj (↑z : G)).toMonoidHom ≤ L := by
    rintro _ ⟨a,ha,rfl⟩
    have hyL : (MulAut.conj y) a ∈ L := hAR ⟨a,hS'A ha,rfl⟩
    have h : x⁻¹ * (MulAut.conj y) a * x ∈ L := L.mul_mem (L.mul_mem (L.inv_mem hxL) hyL) hxL
    convert h using 1
    simp only [y, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hNL : N ≤ L := by
    have h := congrArg (Subgroup.map N.subtype) hgen
    rw [Subgroup.map_sup, conjugate_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [← h]
    exact sup_le (hS'A.trans le_sup_left) hconjL
  have htop : L = ⊤ := by
    apply top_le_iff.mp
    rw [← hfratt]
    exact sup_le hNL hML
  let _ : Group.IsSolvable S := hS
  let _ : Group.IsSolvable R := solvable_subgroupOf Q N
  let _ : R.Normal := Subgroup.normal_in_normalizer
  let _ : Group.IsSolvable (S ⊔ R : Subgroup N) := solvable_sup_normal S R
  let e := (S ⊔ R : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective
  exact ⟨A,Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,y,htop⟩

/-- The group-order induction is independent of how the nonabelian minimal
normal subgroup's pair of generating Sylow subgroups is obtained. -/
theorem generation_of_minimal_normal
    (localSylow : ∀ (G : Type) [Group G] [Finite G], ∀ M : Subgroup G,
      Minimal (fun H : Subgroup G => H.Normal ∧ H ≠ ⊥) M →
      ¬ Group.IsSolvable M →
      ∃ p : ℕ, p.Prime ∧ ∃ (P : Sylow p M) (x : M),
        (P : Subgroup M) ⊔ (P : Subgroup M).map (MulAut.conj x).toMonoidHom = ⊤)
    (G : Type) [Group G] [Finite G] :
    ∃ A : Subgroup G, Group.IsSolvable A ∧
      ∃ x : G, A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤ := by
  classical
  let Goal (K : Type) [Group K] := ∃ A : Subgroup K, Group.IsSolvable A ∧
    ∃ x : K, A ⊔ A.map (MulAut.conj x).toMonoidHom = ⊤
  have aux : ∀ n : ℕ, ∀ (K : Type) [Group K] [Finite K], Nat.card K = n → Goal K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro K _ _ hn
      by_cases hsolv : Group.IsSolvable K
      · let _ : Group.IsSolvable K := hsolv
        exact ⟨⊤,inferInstance,1,top_sup_eq _⟩
      have htop : (⊤ : Subgroup K) ≠ ⊥ := by
        intro h
        exact hsolv (Group.isSolvable_of_top_eq_bot K h)
      obtain ⟨M,hM⟩ := exists_minimal_of_wellFoundedLT
        (fun H : Subgroup K => H.Normal ∧ H ≠ ⊥) ⟨⊤,inferInstance,htop⟩
      let _ : M.Normal := hM.1.1
      by_cases hMs : Group.IsSolvable M
      · let _ : Group.IsSolvable M := hMs
        have hlt : Nat.card (K ⧸ M) < n := by
          rw [← hn, ← M.index_eq_card, ← M.index_mul_card]
          exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero M.index_ne_zero_of_finite)
            (M.one_lt_card_iff_ne_bot.mpr hM.1.2)
        obtain ⟨A,hA,y,hy⟩ := ih _ hlt (K ⧸ M) rfl
        obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective M y
        obtain ⟨S,hS,hgen⟩ := lift_solvable_quotient M hA x hy
        exact ⟨S,hS,x,hgen⟩
      obtain ⟨p,hp,P,x,hgen⟩ := localSylow K M hM hMs
      let _ : Fact p.Prime := ⟨hp⟩
      let Q : Subgroup K := (P : Subgroup M).map M.subtype
      let N := normalizer (Q : Set K)
      let _ : Group.IsNilpotent Q := (P.isPGroup'.map M.subtype).isNilpotent
      have hQM : Q ≤ M := Subgroup.map_subtype_le _
      have hgen' : Q ⊔ Q.map (MulAut.conj (x : K)).toMonoidHom = M := by
        have hh := congrArg (Subgroup.map M.subtype) hgen
        rw [Subgroup.map_sup, conjugate_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hh
        exact hh
      have hQne : Q ≠ ⊥ := by
        intro h
        have he : M = ⊥ := by simpa [h] using hgen'.symm
        exact hM.1.2 he
      have hN : N ≠ ⊤ := by
        intro h
        have hQnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp h
        have heq : Q = M := le_antisymm hQM (hM.2 ⟨hQnorm,hQne⟩ hQM)
        exact hMs (heq ▸ (inferInstance : Group.IsSolvable Q))
      have hNlt : Nat.card N < n := by
        rw [← hn, ← N.index_mul_card]
        exact lt_mul_of_one_lt_left Nat.card_pos (Subgroup.one_lt_index_of_ne_top hN)
      exact lift_solvable_normalizer (x : K) x.2 hgen' (Sylow.normalizer_sup_eq_top P)
        (ih _ hNlt N rfl)
  exact aux _ G rfl

/-- A finite direct power of a nonabelian finite simple group is generated
by two conjugate Sylow subgroups for some prime. -/
def H1 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    ¬ IsMulCommutative S → ∀ n : ℕ,
      ∃ p : ℕ, p.Prime ∧ ∃ (P : Sylow p (Fin n → S)) (x : Fin n → S),
        (P : Subgroup (Fin n → S)) ⊔
          (P : Subgroup (Fin n → S)).map (MulAut.conj x).toMonoidHom = ⊤

/-- A nonsolvable minimal normal subgroup of a finite group is a finite
direct power of a nonabelian finite simple group. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∀ M : Subgroup G,
    Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) M →
    ¬ Group.IsSolvable M →
    ∃ (S : Type) (_ : Group S) (_ : Finite S) (_ : IsSimpleGroup S) (n : ℕ),
      ¬ IsMulCommutative S ∧ Nonempty (M ≃* (Fin n → S))

theorem main : H1 → H2 →
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1.H2 := by
  intro h1 h2 n H
  have localSylow (G : Type) [Group G] [Finite G] (M : Subgroup G)
      (hM : Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) M)
      (hMs : ¬ Group.IsSolvable M) :
      ∃ p : ℕ, p.Prime ∧ ∃ (P : Sylow p M) (x : M),
        (P : Subgroup M) ⊔ (P : Subgroup M).map (MulAut.conj x).toMonoidHom = ⊤ := by
    obtain ⟨S,hGrp,hFin,hSimple,m,hNoncomm,⟨e⟩⟩ := h2 G M hM hMs
    let _ : Group S := hGrp
    let _ : Finite S := hFin
    let _ : IsSimpleGroup S := hSimple
    obtain ⟨p,hp,P,x,hgen⟩ := h1 S hNoncomm m
    let _ : Fact p.Prime := ⟨hp⟩
    let f := e.symm.toMonoidHom
    have hf : Function.Surjective f := e.symm.surjective
    refine ⟨p,hp,P.mapSurjective hf,f x,?_⟩
    have h := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup, conjugate_map, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hf] at h
    simpa only [Sylow.coe_mapSurjective] using h
  obtain ⟨S,hS,x,hgen⟩ := generation_of_minimal_normal localSylow H
  refine ⟨S.map H.subtype,(x : Equiv.Perm (Fin n)),?_,?_⟩
  · let _ : Group.IsSolvable S := hS
    let e := S.equivMapOfInjective H.subtype H.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  · have htop : S ⊔ Subgroup.zpowers x = ⊤ := by
      have hx : x ∈ (S ⊔ Subgroup.zpowers x : Subgroup H) := by
        have hmem : x ∈ Subgroup.zpowers x := ⟨1, by simp⟩
        exact (show Subgroup.zpowers x ≤ S ⊔ Subgroup.zpowers x from le_sup_right) hmem
      apply top_le_iff.mp
      rw [← hgen]
      exact sup_le le_sup_left (conjugate_mono hx le_sup_left)
    have h := congrArg (Subgroup.map H.subtype) htop
    rw [Subgroup.map_sup, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, MonoidHom.map_zpowers] at h
    exact h

end OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1
