import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1
import Mathlib.Data.SetLike.Fintype
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.Order.Preorder.Finite

/-! A nonsolvable minimal normal subgroup is a direct power of a nonabelian simple group. -/

namespace OMA.MinimalNormalPower

open Subgroup

private theorem map_minimal_normal {A : Type*} [Group A] {K : Subgroup A}
    (hK : Minimal (fun L : Subgroup A => L.Normal ∧ L ≠ ⊥) K) (e : MulAut A) :
    Minimal (fun L : Subgroup A => L.Normal ∧ L ≠ ⊥) (K.map e.toMonoidHom) := by
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have he_surj : Function.Surjective e.toMonoidHom := e.surjective
  refine ⟨⟨MulEquiv.normal_map_iff.mpr hK.1.1, ?_⟩, ?_⟩
  · exact fun h => hK.1.2 ((map_eq_bot_iff_of_injective K he_inj).mp h)
  · intro L hL hLK
    have hc : (L.comap e.toMonoidHom).Normal := hL.1.comap _
    have hn : L.comap e.toMonoidHom ≠ ⊥ := by
      intro hz
      apply hL.2
      rw [← map_comap_eq_self_of_surjective he_surj L, hz, Subgroup.map_bot]
    have hl : L.comap e.toMonoidHom ≤ K := by
      simpa only [comap_map_eq_self_of_injective he_inj] using
        (comap_mono (f := e.toMonoidHom) hLK)
    exact (map_le_iff_le_comap).mpr (hK.2 ⟨hc, hn⟩ hl)

private theorem characteristic_eq_top {G : Type*} [Group G] {M : Subgroup G}
    (hM : Minimal (fun N : Subgroup G => N.Normal ∧ N ≠ ⊥) M)
    (L : Subgroup M) [L.Characteristic] (hne : L ≠ ⊥) : L = ⊤ := by
  let _ : M.Normal := hM.1.1
  have hn : L.map M.subtype ≠ ⊥ :=
    fun h => hne ((map_eq_bot_iff_of_injective L M.subtype_injective).mp h)
  have hEq := hM.eq_of_le ⟨inferInstance, hn⟩ (map_subtype_le L)
  apply map_injective M.subtype_injective
  rw [hEq, ← MonoidHom.range_eq_map, range_subtype]

private theorem inf_centralizer_eq_bot {A : Type*} [Group A] (H : Subgroup A)
    [IsSimpleGroup H] (hnab : ¬ IsMulCommutative H) :
    H ⊓ centralizer (H : Set A) = ⊥ := by
  have hcenter : center H = ⊥ := by
    rcases (inferInstance : (center H).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hnab (center_eq_top_iff.mp h))
  apply le_bot_iff.mp
  intro x hx
  have hz : (⟨x, hx.1⟩ : H) ∈ center H := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp hx.2 y y.2
  rw [hcenter, mem_bot] at hz
  exact mem_bot.mpr (congrArg Subtype.val hz)

end OMA.MinimalNormalPower

open Subgroup in
/-- The automorphism orbit of one minimal normal subgroup gives all factors. -/
theorem OMA.solution :
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H2_R1_H2_R1.H2 := by
  classical
  intro G _ _ M hM hnonsolvable
  let _ : Nontrivial M := M.nontrivial_iff_ne_bot.mpr hM.1.2
  obtain ⟨K, hK⟩ := exists_minimal_of_wellFoundedLT
    (fun L : Subgroup M => L.Normal ∧ L ≠ ⊥) ⟨⊤, inferInstance, top_ne_bot⟩
  let ι := Set.range (fun e : MulAut M => K.map e.toMonoidHom)
  let F : ι → Subgroup M := Subtype.val
  have hrep : ∀ i : ι, ∃ e : MulAut M, K.map e.toMonoidHom = F i := fun i => i.2
  obtain ⟨e, he⟩ := Classical.skolem.mp hrep
  have facIso (i : ι) : F i ≃* K :=
    (((e i).subgroupMap K).trans (MulEquiv.subgroupCongr (he i))).symm
  have hminimal (i : ι) : Minimal (fun L : Subgroup M => L.Normal ∧ L ≠ ⊥) (F i) :=
    he i ▸ OMA.MinimalNormalPower.map_minimal_normal hK (e i)
  let base : ι := ⟨K, ⟨MulEquiv.refl M, by simp⟩⟩
  have base_eq : F base = K := rfl
  let L := ⨆ i, F i
  let _ : L.Characteristic := by
    apply characteristic_iff_map_le.mpr
    intro a
    change (⨆ i, F i).map a.toMonoidHom ≤ L
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro i
    let j : ι := ⟨K.map ((e i).trans a).toMonoidHom, ⟨(e i).trans a, rfl⟩⟩
    rw [← he i, map_map]
    exact le_iSup F j
  have hKL : K ≤ L := base_eq ▸ le_iSup F base
  have htop : L = ⊤ := OMA.MinimalNormalPower.characteristic_eq_top hM L
    (fun hz => hK.1.2 (le_bot_iff.mp (hz ▸ hKL)))
  have hdis : Pairwise (fun i j : ι => Disjoint (F i) (F j)) := by
    intro i j hij
    by_contra hd
    have hn : F i ⊓ F j ≠ ⊥ := fun h => hd (disjoint_iff.mpr h)
    let _ : (F i).Normal := (hminimal i).1.1
    let _ : (F j).Normal := (hminimal j).1.1
    exact hij (Subtype.ext (((hminimal i).eq_of_le ⟨inferInstance, hn⟩ inf_le_left).symm.trans
      ((hminimal j).eq_of_le ⟨inferInstance, hn⟩ inf_le_right)))
  have hcomm : Pairwise (fun i j : ι => ∀ x y : M, x ∈ F i → y ∈ F j → Commute x y) :=
    fun i j hij => commute_of_normal_of_disjoint (F i) (F j) (hminimal i).1.1
      (hminimal j).1.1 (hdis hij)
  have hcentral {i j : ι} (hij : i ≠ j) : F i ≤ centralizer (F j : Set M) := by
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy => (hcomm hij x y hx hy).eq.symm
  have hsimple : IsSimpleGroup K := by
    apply K.isSimpleGroup_iff.mpr
    refine ⟨hK.1.2, fun J hJK hJ => ?_⟩
    by_cases hJbot : J = ⊥
    · exact Or.inl hJbot
    · apply Or.inr
      have hnorm : L ≤ normalizer (J : Set M) := by
        apply iSup_le
        intro i
        by_cases hi : i = base
        · subst i
          rw [base_eq]
          exact (normal_subgroupOf_iff_le_normalizer hJK).mp hJ
        · exact (hcentral hi).trans ((centralizer_le hJK).trans (centralizer_le_normalizer _))
      have hJnorm : J.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hnorm))
      exact hK.eq_of_le ⟨hJnorm, hJbot⟩ hJK
  have hnab : ¬ IsMulCommutative K := by
    intro hab
    have hall (i j : ι) : F i ≤ centralizer (F j : Set M) := by
      by_cases hij : i = j
      · subst j
        apply le_centralizer_iff_isMulCommutative.mpr
        rw [isMulCommutative_iff] at hab ⊢
        exact fun x y => (facIso i).injective (by
          simpa only [map_mul] using (hab (facIso i x) (facIso i y)))
      · exact hcentral hij
    have hLC : L ≤ centralizer (L : Set M) := iSup_le fun i =>
      le_centralizer_iff.mp (iSup_le fun j => hall j i)
    have hMcomm : ∀ x y : M, x * y = y * x := by
      intro x y
      have hxm : x ∈ L := by rw [htop]; exact mem_top x
      have hym : y ∈ L := by rw [htop]; exact mem_top y
      exact (mem_centralizer_iff.mp (hLC hxm) y hym).symm
    exact hnonsolvable (Group.isSolvable_of_comm hMcomm)
  have hind : iSupIndep F := by
    rw [iSupIndep_def]
    intro i
    let _ : IsSimpleGroup K := hsimple
    let _ : IsSimpleGroup (F i) := (facIso i).isSimpleGroup
    have hi : ¬ IsMulCommutative (F i) := by
      intro hi
      apply hnab
      rw [isMulCommutative_iff] at hi ⊢
      exact fun x y => (facIso i).symm.injective (by
        simpa only [map_mul] using (hi ((facIso i).symm x) ((facIso i).symm y)))
    have hc : (⨆ (j : ι) (_ : j ≠ i), F j) ≤ centralizer (F i : Set M) :=
      iSup_le fun j => iSup_le (fun hj => hcentral hj)
    exact (disjoint_iff.mpr (OMA.MinimalNormalPower.inf_centralizer_eq_bot (F i) hi)).mono_right hc
  let _ : Fintype ι := Fintype.ofFinite ι
  let product : (∀ i, F i) ≃* M := MulEquiv.ofBijective (Subgroup.noncommPiCoprod hcomm)
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hind,
      MonoidHom.range_eq_top.mp (Subgroup.noncommPiCoprod_range.trans htop)⟩
  let reindex : (ι → K) ≃* (Fin (Fintype.card ι) → K) :=
    { Equiv.arrowCongr (Fintype.equivFin ι) (Equiv.refl K) with map_mul' := fun _ _ => rfl }
  exact ⟨K, inferInstance, inferInstance, hsimple, Fintype.card ι, hnab,
    ⟨product.symm.trans ((MulEquiv.piCongrRight facIso).trans reindex)⟩⟩
