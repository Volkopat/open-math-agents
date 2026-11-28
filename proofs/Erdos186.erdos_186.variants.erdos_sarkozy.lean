import FormalConjectures.ErdosProblems.«186»

open Finset Filter
open scoped Pointwise Classical

namespace Erdos186Proof


section Kneser

lemma add_zero_singleton {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    A + ({0} : Finset G) = A := by
  ext x
  simp [Finset.mem_add]

lemma vadd_add_finset {G : Type*} [AddCommGroup G] [DecidableEq G] (g : G) (A B : Finset G) :
    g +ᵥ (A + B) = (g +ᵥ A) + B := by
  ext x
  simp only [Finset.mem_vadd_finset, Finset.mem_add, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨g + a, ⟨a, ha, rfl⟩, b, hb, by abel⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, b, hb, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by abel⟩

lemma add_vadd_finset {G : Type*} [AddCommGroup G] [DecidableEq G] (g : G) (A B : Finset G) :
    A + (g +ᵥ B) = g +ᵥ (A + B) := by
  rw [add_comm, ← vadd_add_finset, add_comm]

lemma vadd_comm_finset {G : Type*} [AddCommGroup G] [DecidableEq G] (g h : G) (S : Finset G) :
    g +ᵥ (h +ᵥ S) = h +ᵥ (g +ᵥ S) := by
  rw [← add_vadd, add_comm, add_vadd]

lemma vadd_mem_iff_finset {G : Type*} [AddCommGroup G] [DecidableEq G] (g : G) (S : Finset G) (x : G) :
    g +ᵥ x ∈ g +ᵥ S ↔ x ∈ S := by
  simp only [Finset.mem_vadd_finset, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, heq⟩
    have : y = x := add_left_cancel heq
    exact this ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

def stab {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) : AddSubgroup G where
  carrier := {g : G | g +ᵥ S = S}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    show (a + b) +ᵥ S = S
    rw [add_vadd, hb, ha]
  neg_mem' {a} ha := by
    show -a +ᵥ S = S
    calc -a +ᵥ S = -a +ᵥ (a +ᵥ S) := by rw [ha]
      _ = S := neg_vadd_vadd a S

lemma mem_stab_iff {G : Type*} [AddCommGroup G] [DecidableEq G] {S : Finset G} {g : G} :
    g ∈ stab S ↔ g +ᵥ S = S := Iff.rfl

noncomputable def subFinset {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    Finset G :=
  Finset.univ.filter (· ∈ H)

lemma mem_subFinset {G : Type*} [AddCommGroup G] [Fintype G] {H : AddSubgroup G} {g : G} :
    g ∈ subFinset H ↔ g ∈ H := by
  simp [subFinset]

lemma zero_mem_subFinset {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    (0 : G) ∈ subFinset H := by
  simp [subFinset]

lemma card_subFinset_pos {G : Type*} [AddCommGroup G] [Fintype G] (H : AddSubgroup G) :
    0 < (subFinset H).card :=
  Finset.card_pos.mpr ⟨0, zero_mem_subFinset H⟩

lemma subFinset_bot {G : Type*} [AddCommGroup G] [Fintype G] :
    subFinset (⊥ : AddSubgroup G) = {0} := by
  ext x
  simp [subFinset]

lemma subFinset_top {G : Type*} [AddCommGroup G] [Fintype G] :
    subFinset (⊤ : AddSubgroup G) = Finset.univ := by
  ext x
  simp [subFinset]

lemma subset_add_subFinset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) : A ⊆ A + subFinset H := by
  intro a ha
  exact Finset.mem_add.mpr ⟨a, ha, 0, zero_mem_subFinset H, add_zero a⟩

lemma add_subFinset_eq_self_of_le_stab {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {H : AddSubgroup G} (hH : H ≤ stab S) :
    S + subFinset H = S := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, h, hh, rfl⟩ := Finset.mem_add.mp hx
    have hh' : h +ᵥ S = S := hH (mem_subFinset.mp hh)
    rw [add_comm, ← hh']
    exact Finset.vadd_mem_vadd_finset hs
  · exact subset_add_subFinset S H

lemma add_subFinset_add_subFinset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) :
    A + subFinset H + subFinset H = A + subFinset H := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, h2, hh2, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a, ha, h1, hh1, rfl⟩ := Finset.mem_add.mp hy
    exact Finset.mem_add.mpr ⟨a, ha, h1 + h2,
      mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh1) (mem_subFinset.mp hh2)),
      by rw [add_assoc]⟩
  · exact subset_add_subFinset _ H

lemma add_subFinset_mono {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) {H1 H2 : AddSubgroup G} (h : H1 ≤ H2) :
    A + subFinset H1 ⊆ A + subFinset H2 := by
  apply Finset.add_subset_add_left
  intro x hx
  exact mem_subFinset.mpr (h (mem_subFinset.mp hx))

lemma stab_add_le {G : Type*} [AddCommGroup G] [DecidableEq G] (A B : Finset G) :
    stab B ≤ stab (A + B) := by
  intro g hg
  show g +ᵥ (A + B) = A + B
  rw [← add_vadd_finset, hg]

lemma card_add_subFinset_eq_mul {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) :
    (A + subFinset H).card =
      (A.image (QuotientAddGroup.mk' H)).card * (subFinset H).card := by
  set φ := QuotientAddGroup.mk' H
  have hφ_zero : ∀ h : G, φ h = 0 ↔ h ∈ H := fun h => QuotientAddGroup.eq_zero_iff h
  have himg : (A + subFinset H).image φ = A.image φ := by
    ext q
    simp only [Finset.mem_image, Finset.mem_add, mem_subFinset]
    constructor
    · rintro ⟨_, ⟨a, ha, h, hh, rfl⟩, rfl⟩
      refine ⟨a, ha, ?_⟩
      rw [map_add, (hφ_zero h).mpr hh, add_zero]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a + 0, ⟨a, ha, 0, H.zero_mem, rfl⟩, by simp⟩
  rw [← himg, Finset.card_eq_sum_card_fiberwise (f := φ) (t := (A + subFinset H).image φ)
    (fun x hx => Finset.mem_image_of_mem φ hx)]
  have hfib : ∀ q ∈ (A + subFinset H).image φ,
      ((A + subFinset H).filter (fun x => φ x = q)).card = (subFinset H).card := by
    intro q hq
    rw [himg] at hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    have hset : (A + subFinset H).filter (fun x => φ x = φ a) = a +ᵥ subFinset H := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_add, Finset.mem_vadd_finset, mem_subFinset,
        vadd_eq_add]
      constructor
      · rintro ⟨_, hφ⟩
        have hxa : x - a ∈ H := by
          rw [← hφ_zero, map_sub, sub_eq_zero]
          exact hφ
        exact ⟨x - a, hxa, by abel⟩
      · rintro ⟨h, hh, rfl⟩
        refine ⟨⟨a, ha, h, hh, rfl⟩, ?_⟩
        rw [map_add, (hφ_zero h).mpr hh, add_zero]
    rw [hset, Finset.card_vadd_finset]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

lemma card_subFinset_dvd_card_add_subFinset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (H : AddSubgroup G) :
    (subFinset H).card ∣ (A + subFinset H).card := by
  rw [card_add_subFinset_eq_mul]
  exact dvd_mul_left _ _

lemma card_subFinset_dvd_of_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {H1 H2 : AddSubgroup G} (h : H1 ≤ H2) :
    (subFinset H1).card ∣ (subFinset H2).card := by
  have heq : subFinset H2 + subFinset H1 = subFinset H2 := by
    apply Finset.Subset.antisymm
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      exact mem_subFinset.mpr (H2.add_mem (mem_subFinset.mp ha) (h (mem_subFinset.mp hb)))
    · exact subset_add_subFinset _ _
  rw [← heq]
  exact card_subFinset_dvd_card_add_subFinset _ _

lemma stab_vadd {G : Type*} [AddCommGroup G] [DecidableEq G] (g : G) (S : Finset G) :
    stab (g +ᵥ S) = stab S := by
  ext x
  simp only [mem_stab_iff]
  constructor
  · intro h
    calc x +ᵥ S = -g +ᵥ (g +ᵥ (x +ᵥ S)) := (neg_vadd_vadd g _).symm
      _ = -g +ᵥ (x +ᵥ (g +ᵥ S)) := by rw [vadd_comm_finset g x S]
      _ = -g +ᵥ (g +ᵥ S) := by rw [h]
      _ = S := neg_vadd_vadd g S
  · intro h
    rw [vadd_comm_finset x g S, h]

lemma card_subFinset_lt_of_lt {G : Type*} [AddCommGroup G] [Fintype G]
    {H1 H2 : AddSubgroup G} (h : H1 < H2) :
    (subFinset H1).card < (subFinset H2).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨fun x hx => mem_subFinset.mpr (h.le (mem_subFinset.mp hx)), ?_⟩
  intro heq
  apply h.ne
  ext x
  have := Finset.ext_iff.mp heq x
  simpa [mem_subFinset] using this

lemma le_stab_iff_add_subFinset_eq {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {H : AddSubgroup G} :
    H ≤ stab S ↔ S + subFinset H = S := by
  constructor
  · exact add_subFinset_eq_self_of_le_stab
  · intro heq h hh
    show h +ᵥ S = S
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_vadd_finset.mp hx
      rw [← heq]
      exact Finset.mem_add.mpr ⟨s, hs, h, mem_subFinset.mpr hh, by rw [vadd_eq_add, add_comm]⟩
    · simp

lemma card_eq_card_image_mul_of_le_stab {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S : Finset G} {H : AddSubgroup G} (hH : H ≤ stab S) :
    S.card = (S.image (QuotientAddGroup.mk' H)).card * (subFinset H).card := by
  have h1 := card_add_subFinset_eq_mul S H
  rw [add_subFinset_eq_self_of_le_stab hH] at h1
  exact h1

lemma vadd_subFinset_disjoint_of_not_subset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {C : Finset G} {H : AddSubgroup G} (hHC : H ≤ stab C) {x : G}
    (hx : ¬ x +ᵥ subFinset H ⊆ C) :
    Disjoint C (x +ᵥ subFinset H) := by
  rw [Finset.disjoint_left]
  intro y hyC hyx
  apply hx
  obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hyx
  intro z hz
  obtain ⟨h', hh', rfl⟩ := Finset.mem_vadd_finset.mp hz
  have hdiff : h' - h ∈ H := H.sub_mem (mem_subFinset.mp hh') (mem_subFinset.mp hh)
  have hst : (h' - h) +ᵥ C = C := hHC hdiff
  rw [← hst]
  have heq : x +ᵥ h' = (h' - h) +ᵥ (x +ᵥ h) := by
    simp only [vadd_eq_add]; abel
  rw [heq]
  exact Finset.vadd_mem_vadd_finset hyC

lemma stab_union_partial_coset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {C D : Finset G} {H : AddSubgroup G} {x : G}
    (hHC : stab C = H) (hDne : D.Nonempty)
    (hDsub : D ⊆ x +ᵥ subFinset H) (hDstrict : D ≠ x +ᵥ subFinset H)
    (hdisj : Disjoint C (x +ᵥ subFinset H)) :
    stab (C ∪ D) = stab D ∧ stab D < H := by
  have hHC_mem : ∀ h ∈ H, h +ᵥ C = C := fun h hh => by
    have : h ∈ stab C := hHC.symm ▸ hh
    exact this
  have hDlt : D.card < (subFinset H).card := by
    have hss : D ⊂ x +ᵥ subFinset H := Finset.ssubset_iff_subset_ne.mpr ⟨hDsub, hDstrict⟩
    simpa [Finset.card_vadd_finset] using Finset.card_lt_card hss
  have hSDle : stab D ≤ H := by
    intro g hg
    obtain ⟨d, hd⟩ := hDne
    have hgd : g + d ∈ D := by
      have : g +ᵥ d ∈ g +ᵥ D := Finset.vadd_mem_vadd_finset hd
      rwa [hg, vadd_eq_add] at this
    obtain ⟨h1, hh1, rfl⟩ := Finset.mem_vadd_finset.mp (hDsub hd)
    obtain ⟨h2, hh2, heq⟩ := Finset.mem_vadd_finset.mp (hDsub hgd)
    have hg_eq : g = h2 - h1 := by
      simp only [vadd_eq_add] at heq
      calc g = (g + (x + h1)) - (x + h1) := by abel
        _ = (x + h2) - (x + h1) := by rw [← heq]
        _ = h2 - h1 := by abel
    rw [hg_eq]
    exact H.sub_mem (mem_subFinset.mp hh2) (mem_subFinset.mp hh1)
  have hSDlt : stab D < H := by
    refine lt_of_le_of_ne hSDle ?_
    intro heq
    have hHD : H ≤ stab D := heq ▸ le_rfl
    obtain ⟨d, hd⟩ := hDne
    have h1 : d +ᵥ subFinset H ⊆ D := by
      intro z hz
      obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hz
      have hst : h +ᵥ D = D := hHD (mem_subFinset.mp hh)
      rw [← hst, vadd_eq_add, add_comm]
      exact Finset.vadd_mem_vadd_finset hd
    have h2 : (subFinset H).card ≤ D.card := by
      simpa [Finset.card_vadd_finset] using Finset.card_le_card h1
    omega
  refine ⟨?_, hSDlt⟩
  apply le_antisymm
  · intro g hg
    have hgH : g ∈ H := by
      by_contra hgnH
      have hgx_disj : Disjoint (g +ᵥ (x +ᵥ subFinset H)) (x +ᵥ subFinset H) := by
        rw [Finset.disjoint_left]
        intro y hy1 hy2
        obtain ⟨z, hz, rfl⟩ := Finset.mem_vadd_finset.mp hy1
        obtain ⟨h1, hh1, rfl⟩ := Finset.mem_vadd_finset.mp hz
        obtain ⟨h2, hh2, heq⟩ := Finset.mem_vadd_finset.mp hy2
        apply hgnH
        have hg_eq : g = h2 - h1 := by
          simp only [vadd_eq_add] at heq
          calc g = (g + (x + h1)) - (x + h1) := by abel
            _ = (x + h2) - (x + h1) := by rw [← heq]
            _ = h2 - h1 := by abel
        rw [hg_eq]
        exact H.sub_mem (mem_subFinset.mp hh2) (mem_subFinset.mp hh1)
      have hgD_sub_C : g +ᵥ D ⊆ C := by
        intro y hy
        have hyCD : y ∈ C ∪ D := by
          have : y ∈ g +ᵥ (C ∪ D) :=
            Finset.vadd_finset_subset_vadd_finset Finset.subset_union_right hy
          rwa [hg] at this
        have hy_gx : y ∈ g +ᵥ (x +ᵥ subFinset H) :=
          Finset.vadd_finset_subset_vadd_finset hDsub hy
        have hynotD : y ∉ D := fun hyD =>
          Finset.disjoint_left.mp hgx_disj hy_gx (hDsub hyD)
        exact (Finset.mem_union.mp hyCD).resolve_right hynotD
      have hgx_sub_C : g +ᵥ (x +ᵥ subFinset H) ⊆ C := by
        obtain ⟨d, hd⟩ := hDne
        have hgdC : g +ᵥ d ∈ C := hgD_sub_C (Finset.vadd_mem_vadd_finset hd)
        have hgx_eq : g +ᵥ (x +ᵥ subFinset H) = (g +ᵥ d) +ᵥ subFinset H := by
          obtain ⟨h0, hh0, rfl⟩ := Finset.mem_vadd_finset.mp (hDsub hd)
          have hh0' : h0 ∈ H := mem_subFinset.mp hh0
          ext z
          simp only [Finset.mem_vadd_finset, mem_subFinset, vadd_eq_add]
          constructor
          · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
            exact ⟨h - h0, H.sub_mem hh hh0', by abel⟩
          · rintro ⟨h, hh, rfl⟩
            exact ⟨x + (h0 + h), ⟨h0 + h, H.add_mem hh0' hh, rfl⟩, by abel⟩
        rw [hgx_eq]
        intro z hz
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hz
        have hst : h +ᵥ C = C := hHC_mem h (mem_subFinset.mp hh)
        rw [← hst, vadd_eq_add, add_comm]
        exact Finset.vadd_mem_vadd_finset hgdC
      have hsub : x +ᵥ subFinset H ⊆ C ∪ D := by
        intro y hy
        have hgy : g +ᵥ y ∈ C := hgx_sub_C (Finset.vadd_mem_vadd_finset hy)
        have hgyCD : g +ᵥ y ∈ g +ᵥ (C ∪ D) := by
          rw [hg]
          exact Finset.mem_union_left D hgy
        exact (vadd_mem_iff_finset g (C ∪ D) y).mp hgyCD
      have hsubD : x +ᵥ subFinset H ⊆ D := by
        intro y hy
        exact (Finset.mem_union.mp (hsub hy)).resolve_left
          (Finset.disjoint_right.mp hdisj hy)
      exact hDstrict (Finset.Subset.antisymm hDsub hsubD)
    have hg_pres_coset : g +ᵥ (x +ᵥ subFinset H) = x +ᵥ subFinset H := by
      ext z
      simp only [Finset.mem_vadd_finset, mem_subFinset, vadd_eq_add]
      constructor
      · rintro ⟨_, ⟨h, hh, rfl⟩, rfl⟩
        exact ⟨g + h, H.add_mem hgH hh, by abel⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨x + (h - g), ⟨h - g, H.sub_mem hh hgH, rfl⟩, by abel⟩
    show g +ᵥ D = D
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      have hyCD : y ∈ C ∪ D := by
        have : y ∈ g +ᵥ (C ∪ D) :=
          Finset.vadd_finset_subset_vadd_finset Finset.subset_union_right hy
        rwa [hg] at this
      have hyx : y ∈ x +ᵥ subFinset H := by
        rw [← hg_pres_coset]
        exact Finset.vadd_finset_subset_vadd_finset hDsub hy
      exact (Finset.mem_union.mp hyCD).resolve_left (Finset.disjoint_right.mp hdisj hyx)
    · simp
  · intro g hg
    have hgH : g ∈ H := hSDle hg
    show g +ᵥ (C ∪ D) = C ∪ D
    rw [Finset.vadd_finset_union, hHC_mem g hgH, hg]

set_option maxHeartbeats 400000 in
theorem kneser_add :
    ∀ (m : ℕ) (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
      (A B : Finset G), A.Nonempty → B.Nonempty → (A + B).card + A.card ≤ m →
      (A + subFinset (stab (A + B))).card + (B + subFinset (stab (A + B))).card ≤
        (A + B).card + (subFinset (stab (A + B))).card := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro G _ _ _ A B hA hB hm
    set K := stab (A + B) with hKdef
    by_cases hK : K ≠ ⊥
    · set φ := QuotientAddGroup.mk' K
      have hφ_zero : ∀ g : G, φ g = 0 ↔ g ∈ K := fun g => QuotientAddGroup.eq_zero_iff g
      set A' := A.image φ
      set B' := B.image φ
      have hA' : A'.Nonempty := hA.image φ
      have hB' : B'.Nonempty := hB.image φ
      have hAB' : A' + B' = (A + B).image φ := by
        ext q
        simp only [A', B', Finset.mem_add, Finset.mem_image]
        constructor
        · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
          exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, map_add φ a b⟩
        · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
          exact ⟨φ a, ⟨a, ha, rfl⟩, φ b, ⟨b, hb, rfl⟩, (map_add φ a b).symm⟩
      have hKcard : 2 ≤ (subFinset K).card := by
        have hne : ∃ g ∈ K, g ≠ 0 := by
          by_contra hall
          push Not at hall
          apply hK
          ext g
          simp only [AddSubgroup.mem_bot]
          exact ⟨hall g, fun hg => hg ▸ K.zero_mem⟩
        obtain ⟨g, hgK, hg0⟩ := hne
        have hsub : ({0, g} : Finset G) ⊆ subFinset K := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact zero_mem_subFinset K
          · exact mem_subFinset.mpr hgK
        calc 2 = ({0, g} : Finset G).card := (Finset.card_pair hg0.symm).symm
          _ ≤ (subFinset K).card := Finset.card_le_card hsub
      have hAB_mul : (A + B).card = (A' + B').card * (subFinset K).card := by
        rw [hAB']
        exact card_eq_card_image_mul_of_le_stab (show K ≤ stab (A + B) from le_rfl)
      have hlt_AB : (A' + B').card < (A + B).card := by
        have hpos : 0 < (A' + B').card := (hA'.add hB').card_pos
        nlinarith
      have hle_A : A'.card ≤ A.card := Finset.card_image_le
      have hstab' : stab (A' + B') = ⊥ := by
        ext q
        simp only [mem_stab_iff, AddSubgroup.mem_bot]
        constructor
        · intro hq
          obtain ⟨g, rfl⟩ := QuotientAddGroup.mk'_surjective K q
          rw [hφ_zero]
          show g +ᵥ (A + B) = A + B
          apply Finset.eq_of_subset_of_card_le
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
            have hφy : φ (g + y) ∈ A' + B' := by
              rw [← hq, map_add, ← vadd_eq_add]
              have hy' : φ y ∈ A' + B' := by
                rw [hAB']; exact Finset.mem_image_of_mem φ hy
              exact Finset.vadd_mem_vadd_finset hy'
            rw [hAB'] at hφy
            obtain ⟨z, hz, hφeq⟩ := Finset.mem_image.mp hφy
            have hdiff : g + y - z ∈ K := by
              rw [← hφ_zero, map_sub, sub_eq_zero]
              exact hφeq.symm
            have hst : (g + y - z) +ᵥ (A + B) = A + B := hdiff
            rw [← hst]
            have : g +ᵥ y = (g + y - z) +ᵥ z := by simp only [vadd_eq_add]; abel
            rw [this]
            exact Finset.vadd_mem_vadd_finset hz
          · simp
        · rintro rfl
          exact zero_vadd _ _
      have hIH := @ih ((A' + B').card + A'.card) (by omega) (G ⧸ K) _ _ _ A' B' hA' hB' le_rfl
      rw [hstab', subFinset_bot, Finset.card_singleton, add_zero_singleton, add_zero_singleton] at hIH
      rw [card_add_subFinset_eq_mul A K, card_add_subFinset_eq_mul B K, hAB_mul]
      calc A'.card * (subFinset K).card + B'.card * (subFinset K).card
          = (A'.card + B'.card) * (subFinset K).card := by ring
        _ ≤ ((A' + B').card + 1) * (subFinset K).card :=
            Nat.mul_le_mul_right _ hIH
        _ = (A' + B').card * (subFinset K).card + (subFinset K).card := by ring
    push Not at hK
    have hKeq : stab (A + B) = ⊥ := hK
    rw [show subFinset K = {0} by rw [show K = ⊥ from hKeq, subFinset_bot]]
    rw [add_zero_singleton, add_zero_singleton, Finset.card_singleton]
    by_cases hA1 : A.card ≤ 1
    · have hAeq1 : A.card = 1 := le_antisymm hA1 hA.card_pos
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hAeq1
      have : ({a} + B).card = B.card := by
        rw [Finset.singleton_add, Finset.card_vadd_finset]
      rw [this, Finset.card_singleton]
      omega
    have hA2 : 2 ≤ A.card := by omega
    obtain ⟨a0, ha0, a1, ha1, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hnotStabB : a1 - a0 ∉ stab B := by
      intro hmem
      have hmemK : a1 - a0 ∈ stab (A + B) := stab_add_le A B hmem
      rw [hKeq, AddSubgroup.mem_bot] at hmemK
      exact hne (sub_eq_zero.mp hmemK).symm
    obtain ⟨b0, hb0, hb0_not⟩ : ∃ b ∈ B, b + (a1 - a0) ∉ B := by
      by_contra hall
      push Not at hall
      apply hnotStabB
      show (a1 - a0) +ᵥ B = B
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨b, hb, rfl⟩ := Finset.mem_vadd_finset.mp hy
        rw [vadd_eq_add, add_comm]
        exact hall b hb
      · simp
    set g_shift : G := a0 - b0
    set B' : Finset G := g_shift +ᵥ B
    have hAB'_eq : A + B' = g_shift +ᵥ (A + B) := add_vadd_finset g_shift A B
    have hB'_card : B'.card = B.card := Finset.card_vadd_finset g_shift B
    have hAB'_card : (A + B').card = (A + B).card := by
      rw [hAB'_eq, Finset.card_vadd_finset]
    suffices hsuff : A.card + B'.card ≤ (A + B').card + 1 by
      rw [hB'_card, hAB'_card] at hsuff
      exact hsuff
    have hB'ne : B'.Nonempty := hB.vadd_finset
    have hstab_AB' : stab (A + B') = ⊥ := by
      rw [hAB'_eq, stab_vadd, hKeq]
    have ha0_inter : a0 ∈ A ∩ B' := by
      refine Finset.mem_inter.mpr ⟨ha0, Finset.mem_vadd_finset.mpr ⟨b0, hb0, ?_⟩⟩
      simp [g_shift, vadd_eq_add]
    have ha1_not_B' : a1 ∉ B' := by
      intro hmem
      obtain ⟨b, hb, heq⟩ := Finset.mem_vadd_finset.mp hmem
      apply hb0_not
      have : b = b0 + (a1 - a0) := by
        simp only [g_shift, vadd_eq_add] at heq
        calc b = (a0 - b0 + b) + b0 - a0 := by abel
          _ = a1 + b0 - a0 := by rw [heq]
          _ = b0 + (a1 - a0) := by abel
      exact this ▸ hb
    have hInter_ne : (A ∩ B').Nonempty := ⟨a0, ha0_inter⟩
    have hUnion_ne : (A ∪ B').Nonempty := hA.mono Finset.subset_union_left
    have hInter_lt : (A ∩ B').card < A.card := by
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro heq
      have hmemI : a1 ∈ A ∩ B' := by rw [heq]; exact ha1
      exact ha1_not_B' (Finset.mem_inter.mp hmemI).2
    let IsConv (C : Finset G) : Prop :=
      C ⊆ A + B' ∧
      (A ∩ B').card + ((A ∪ B') + subFinset (stab C)).card ≤
        C.card + (subFinset (stab C)).card
    have hC0_sub : (A ∩ B') + (A ∪ B') ⊆ A + B' := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨huA, huB'⟩ := Finset.mem_inter.mp hu
      rcases Finset.mem_union.mp hv with hvA | hvB'
      · exact Finset.mem_add.mpr ⟨v, hvA, u, huB', add_comm v u⟩
      · exact Finset.mem_add.mpr ⟨u, huA, v, hvB', rfl⟩
    have hC0_conv : IsConv ((A ∩ B') + (A ∪ B')) := by
      refine ⟨hC0_sub, ?_⟩
      have hlt : ((A ∩ B') + (A ∪ B')).card + (A ∩ B').card < (A + B).card + A.card := by
        have hle1 : ((A ∩ B') + (A ∪ B')).card ≤ (A + B').card := Finset.card_le_card hC0_sub
        omega
      have hIH0 := ih _ (by omega) G (A ∩ B') (A ∪ B') hInter_ne hUnion_ne le_rfl
      have hle_inter : (A ∩ B').card ≤ ((A ∩ B') + subFinset (stab ((A ∩ B') + (A ∪ B')))).card :=
        Finset.card_le_card (subset_add_subFinset _ _)
      omega
    have hex_conv : ∃ n : ℕ, ∃ C : Finset G, IsConv C ∧ (subFinset (stab C)).card = n :=
      ⟨_, _, hC0_conv, rfl⟩
    obtain ⟨C, hC_conv, hC_card⟩ := Nat.find_spec hex_conv
    set H := stab C with hHdef
    have hC_min : ∀ C' : Finset G, IsConv C' → (subFinset H).card ≤ (subFinset (stab C')).card := by
      intro C' hC'
      rw [hHdef, hC_card]
      exact Nat.find_min' hex_conv ⟨C', hC', rfl⟩
    by_cases hHbot : H = ⊥
    · have hH1 : (subFinset H).card = 1 := by rw [hHbot, subFinset_bot, Finset.card_singleton]
      have hU_eq : (A ∪ B') + subFinset H = A ∪ B' := by
        rw [hHbot, subFinset_bot, add_zero_singleton]
      have hC_le : C.card ≤ (A + B').card := Finset.card_le_card hC_conv.1
      have hconv_ineq : (A ∩ B').card + ((A ∪ B') + subFinset H).card ≤
          C.card + (subFinset H).card := hC_conv.2
      rw [hH1, hU_eq] at hconv_ineq
      have hIU : (A ∩ B').card + (A ∪ B').card = A.card + B'.card := by
        rw [add_comm, Finset.card_union_add_card_inter]
      omega
    exfalso
    have hCne : C.Nonempty := by
      by_contra hCe
      rw [Finset.not_nonempty_iff_eq_empty] at hCe
      have hHtop : H = ⊤ := by
        ext g; simp [H, hCe, mem_stab_iff]
      have hUtop : (A ∪ B') + subFinset H = Finset.univ := by
        ext x
        simp only [Finset.mem_univ, iff_true, Finset.mem_add, mem_subFinset, hHtop,
          AddSubgroup.mem_top, true_and]
        obtain ⟨u, hu⟩ := hUnion_ne
        exact ⟨u, hu, x - u, by abel⟩
      have hconv_ineq : (A ∩ B').card + ((A ∪ B') + subFinset H).card ≤
          C.card + (subFinset H).card := hC_conv.2
      rw [hUtop, hCe, Finset.card_empty, hHtop, subFinset_top] at hconv_ineq
      have hpos := hInter_ne.card_pos
      omega
    have hAB'_not_conv : ¬ IsConv (A + B') := by
      intro hconv
      have hle := hC_min (A + B') hconv
      rw [hstab_AB', subFinset_bot, Finset.card_singleton] at hle
      have hgt : 1 < (subFinset H).card := by
        have : (⊥ : AddSubgroup G) < H := bot_lt_iff_ne_bot.mpr hHbot
        simpa [subFinset_bot] using card_subFinset_lt_of_lt this
      omega
    have hAB'_strict_ineq : (A + B').card + 1 < (A ∩ B').card + (A ∪ B').card := by
      by_contra hge
      push Not at hge
      apply hAB'_not_conv
      refine ⟨Subset.rfl, ?_⟩
      rw [hstab_AB', subFinset_bot, Finset.card_singleton, add_zero_singleton]
      exact hge
    obtain ⟨a, ha, b, hb, hab_not⟩ : ∃ a ∈ A, ∃ b ∈ B', ¬ (a + b) +ᵥ subFinset H ⊆ A + B' := by
      by_contra hall
      push Not at hall
      have hHle : H ≤ stab (A + B') := by
        rw [le_stab_iff_add_subFinset_eq]
        apply Finset.Subset.antisymm
        · intro x hx
          obtain ⟨y, hy, h, hh, rfl⟩ := Finset.mem_add.mp hx
          obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hy
          exact hall a ha b hb (Finset.mem_vadd_finset.mpr ⟨h, hh, by simp [vadd_eq_add]⟩)
        · exact subset_add_subFinset _ _
      rw [hstab_AB'] at hHle
      exact hHbot (le_bot_iff.mp hHle)
    have hC_disj : Disjoint C ((a + b) +ᵥ subFinset H) :=
      vadd_subFinset_disjoint_of_not_subset (show H ≤ stab C from le_rfl)
        (fun hsub => hab_not (hsub.trans hC_conv.1))
    set A1 := A ∩ (a +ᵥ subFinset H)
    set A2 := A ∩ (b +ᵥ subFinset H)
    set B1 := B' ∩ (b +ᵥ subFinset H)
    set B2 := B' ∩ (a +ᵥ subFinset H)
    have hA1_ne : A1.Nonempty :=
      ⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_vadd_finset.mpr ⟨0, zero_mem_subFinset H, by simp⟩⟩⟩
    have hB1_ne : B1.Nonempty :=
      ⟨b, Finset.mem_inter.mpr ⟨hb, Finset.mem_vadd_finset.mpr ⟨0, zero_mem_subFinset H, by simp⟩⟩⟩
    have hkey : ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty →
        X ⊆ A → Y ⊆ B' → X + Y ⊆ (a + b) +ᵥ subFinset H →
        let Hi := stab (X + Y)
        Hi < H ∧
        (X + subFinset Hi).card + (Y + subFinset Hi).card ≤ (X + Y).card + (subFinset Hi).card ∧
        ((A ∪ B') + subFinset H).card + (X + subFinset Hi).card + (Y + subFinset Hi).card <
          ((A ∪ B') + subFinset Hi).card + (subFinset H).card ∧
        (X + Y).card + C.card ≤ (A + B').card := by
      intro X Y hX hY hXA hYB hXYcos
      set Hi := stab (X + Y)
      have hXYsub : X + Y ⊆ A + B' := Finset.add_subset_add hXA hYB
      have hXYne : (X + Y).Nonempty := hX.add hY
      have hXYstrict : X + Y ≠ (a + b) +ᵥ subFinset H := fun heq => hab_not (heq ▸ hXYsub)
      have ⟨hstab_union, hHilt⟩ :=
        stab_union_partial_coset (x := a + b) rfl hXYne hXYcos hXYstrict hC_disj
      have hdisj_CXY : Disjoint C (X + Y) := hC_disj.mono_right hXYcos
      have hcard_union : (C ∪ (X + Y)).card = C.card + (X + Y).card :=
        Finset.card_union_of_disjoint hdisj_CXY
      have hle_AB' : (X + Y).card + C.card ≤ (A + B').card := by
        rw [add_comm, ← hcard_union]
        exact Finset.card_le_card (Finset.union_subset hC_conv.1 hXYsub)
      have hlt_IH : (X + Y).card + X.card < (A + B).card + A.card := by
        have hposC : 0 < C.card := hCne.card_pos
        have hleX : X.card ≤ A.card := Finset.card_le_card hXA
        linarith
      have hIH_XY := ih _ (by linarith) G X Y hX hY le_rfl
      have hnot_conv : ¬ IsConv (C ∪ (X + Y)) := by
        intro hc
        have h1 : (subFinset H).card ≤ (subFinset (stab (C ∪ (X + Y)))).card := hC_min _ hc
        rw [hstab_union] at h1
        have h2 : (subFinset Hi).card < (subFinset H).card := card_subFinset_lt_of_lt hHilt
        linarith
      have hfail : (C ∪ (X + Y)).card + (subFinset Hi).card <
          (A ∩ B').card + ((A ∪ B') + subFinset Hi).card := by
        by_contra hge
        push Not at hge
        apply hnot_conv
        refine ⟨Finset.union_subset hC_conv.1 hXYsub, ?_⟩
        rw [hstab_union]
        exact hge
      rw [hcard_union] at hfail
      have hC_ineq : (A ∩ B').card + ((A ∪ B') + subFinset H).card ≤
          C.card + (subFinset H).card := hC_conv.2
      refine ⟨hHilt, hIH_XY, by linarith, hle_AB'⟩
    have hA1B1_cos : A1 + B1 ⊆ (a + b) +ᵥ subFinset H := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨h1, hh1, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
      obtain ⟨h2, hh2, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hv).2
      exact Finset.mem_vadd_finset.mpr ⟨h1 + h2,
        mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh1) (mem_subFinset.mp hh2)),
        by simp only [vadd_eq_add]; abel⟩
    have hA2B2_cos : A2 + B2 ⊆ (a + b) +ᵥ subFinset H := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨h1, hh1, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
      obtain ⟨h2, hh2, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hv).2
      exact Finset.mem_vadd_finset.mpr ⟨h1 + h2,
        mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh1) (mem_subFinset.mp hh2)),
        by simp only [vadd_eq_add]; abel⟩
    obtain ⟨hH1lt, hIH1, heq1_1, hleAB1⟩ :=
      hkey A1 B1 hA1_ne hB1_ne Finset.inter_subset_left Finset.inter_subset_left hA1B1_cos
    set H1 := stab (A1 + B1)
    have hdiff_coset : ∀ (x : G) (H' : AddSubgroup G), x ∈ A ∪ B' → H' ≤ H →
        ((x +ᵥ subFinset H) \ (((A ∪ B') ∩ (x +ᵥ subFinset H)) + subFinset H')).card +
          ((A ∪ B') + subFinset H').card ≤ ((A ∪ B') + subFinset H).card := by
      intro x H' hx hH'le
      have hsub1 : (A ∪ B') + subFinset H' ⊆ (A ∪ B') + subFinset H :=
        add_subFinset_mono (A ∪ B') hH'le
      have hsub2 : (x +ᵥ subFinset H) \ (((A ∪ B') ∩ (x +ᵥ subFinset H)) + subFinset H') ⊆
          ((A ∪ B') + subFinset H) \ ((A ∪ B') + subFinset H') := by
        intro z hz
        obtain ⟨hzx, hznot⟩ := Finset.mem_sdiff.mp hz
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hzx
          exact Finset.mem_add.mpr ⟨x, hx, h, hh, by simp [vadd_eq_add]⟩
        · intro hzU
          apply hznot
          obtain ⟨u, hu, h', hh', rfl⟩ := Finset.mem_add.mp hzU
          refine Finset.mem_add.mpr ⟨u, Finset.mem_inter.mpr ⟨hu, ?_⟩, h', hh', rfl⟩
          obtain ⟨h, hh, heq⟩ := Finset.mem_vadd_finset.mp hzx
          exact Finset.mem_vadd_finset.mpr ⟨h - h',
            mem_subFinset.mpr (H.sub_mem (mem_subFinset.mp hh) (hH'le (mem_subFinset.mp hh'))),
            by simp only [vadd_eq_add] at heq ⊢; calc x + (h - h') = (x + h) - h' := by abel
              _ = (u + h') - h' := by rw [heq]
              _ = u := by abel⟩
      have hcard_sdiff := Finset.card_sdiff_add_card_eq_card hsub1
      have hle_sd := Finset.card_le_card hsub2
      linarith
    have hB2_ne : B2.Nonempty := by
      by_contra hB2e
      rw [Finset.not_nonempty_iff_eq_empty] at hB2e
      have hcap : (A ∪ B') ∩ (a +ᵥ subFinset H) = A1 := by
        rw [Finset.union_inter_distrib_right]
        change A1 ∪ B2 = A1
        rw [hB2e, Finset.union_empty]
      have hsubA1 : A1 + subFinset H1 ⊆ a +ᵥ subFinset H := by
        intro z hz
        obtain ⟨u, hu, h', hh', rfl⟩ := Finset.mem_add.mp hz
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
        exact Finset.mem_vadd_finset.mpr ⟨h + h',
          mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh) (hH1lt.le (mem_subFinset.mp hh'))),
          by simp only [vadd_eq_add]; abel⟩
      have hd := hdiff_coset a H1 (Finset.mem_union_left B' ha) hH1lt.le
      rw [hcap] at hd
      have hsd := Finset.card_sdiff_add_card_eq_card hsubA1
      rw [Finset.card_vadd_finset] at hsd
      linarith
    have hA2_ne : A2.Nonempty := by
      by_contra hA2e
      rw [Finset.not_nonempty_iff_eq_empty] at hA2e
      have hcap : (A ∪ B') ∩ (b +ᵥ subFinset H) = B1 := by
        rw [Finset.union_inter_distrib_right]
        change A2 ∪ B1 = B1
        rw [hA2e, Finset.empty_union]
      have hsubB1 : B1 + subFinset H1 ⊆ b +ᵥ subFinset H := by
        intro z hz
        obtain ⟨u, hu, h', hh', rfl⟩ := Finset.mem_add.mp hz
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_inter.mp hu).2
        exact Finset.mem_vadd_finset.mpr ⟨h + h',
          mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh) (hH1lt.le (mem_subFinset.mp hh'))),
          by simp only [vadd_eq_add]; abel⟩
      have hd := hdiff_coset b H1 (Finset.mem_union_right A hb) hH1lt.le
      rw [hcap] at hd
      have hsd := Finset.card_sdiff_add_card_eq_card hsubB1
      rw [Finset.card_vadd_finset] at hsd
      linarith
    obtain ⟨hH2lt, hIH2, heq1_2, hleAB2⟩ :=
      hkey A2 B2 hA2_ne hB2_ne Finset.inter_subset_left Finset.inter_subset_left hA2B2_cos
    set H2 := stab (A2 + B2)
    have hcos_ne : a +ᵥ subFinset H ≠ b +ᵥ subFinset H := by
      intro heq
      have hB12 : B1 = B2 := by simp [B1, B2, heq]
      have hcap : (A ∪ B') ∩ (a +ᵥ subFinset H) = A1 ∪ B1 := by
        rw [Finset.union_inter_distrib_right]
        change A1 ∪ B2 = A1 ∪ B1
        rw [hB12]
      have hsubU : (A1 ∪ B1) + subFinset H1 ⊆ a +ᵥ subFinset H := by
        intro z hz
        obtain ⟨u, hu, h', hh', rfl⟩ := Finset.mem_add.mp hz
        have huH : u ∈ a +ᵥ subFinset H := by
          rcases Finset.mem_union.mp hu with h1 | h2
          · exact (Finset.mem_inter.mp h1).2
          · rw [heq]; exact (Finset.mem_inter.mp h2).2
        obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp huH
        exact Finset.mem_vadd_finset.mpr ⟨h + h',
          mem_subFinset.mpr (H.add_mem (mem_subFinset.mp hh) (hH1lt.le (mem_subFinset.mp hh'))),
          by simp only [vadd_eq_add]; abel⟩
      have hcard_le : ((A1 ∪ B1) + subFinset H1).card ≤
          (A1 + subFinset H1).card + (B1 + subFinset H1).card := by
        rw [Finset.union_add]
        exact Finset.card_union_le _ _
      have hd := hdiff_coset a H1 (Finset.mem_union_left B' ha) hH1lt.le
      rw [hcap] at hd
      have hsd := Finset.card_sdiff_add_card_eq_card hsubU
      rw [Finset.card_vadd_finset] at hsd
      linarith
    have hcos_disj : Disjoint (a +ᵥ subFinset H) (b +ᵥ subFinset H) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      apply hcos_ne
      obtain ⟨h1, hh1, rfl⟩ := Finset.mem_vadd_finset.mp hz1
      obtain ⟨h2, hh2, heq⟩ := Finset.mem_vadd_finset.mp hz2
      have hab : b - a ∈ H := by
        have : b - a = h1 - h2 := by
          simp only [vadd_eq_add] at heq
          calc b - a = (b + h2) - a - h2 := by abel
            _ = (a + h1) - a - h2 := by rw [heq]
            _ = h1 - h2 := by abel
        rw [this]
        exact H.sub_mem (mem_subFinset.mp hh1) (mem_subFinset.mp hh2)
      ext y
      simp only [Finset.mem_vadd_finset, mem_subFinset, vadd_eq_add]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h - (b - a), H.sub_mem hh hab, by abel⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h + (b - a), H.add_mem hh hab, by abel⟩
    have heq2 : ∀ (X Y : Finset G) (Hi : AddSubgroup G), Hi ≤ H →
        ((A ∪ B') + subFinset H).card + (X + subFinset Hi).card + (Y + subFinset Hi).card <
          ((A ∪ B') + subFinset Hi).card + (subFinset H).card →
        X.card + Y.card + (subFinset Hi).card ≤ (subFinset H).card := by
      intro X Y Hi hHile hstrict
      have hmono : ((A ∪ B') + subFinset Hi).card ≤ ((A ∪ B') + subFinset H).card :=
        Finset.card_le_card (add_subFinset_mono _ hHile)
      have hlt : (X + subFinset Hi).card + (Y + subFinset Hi).card < (subFinset H).card := by linarith
      obtain ⟨c1, hc1⟩ := card_subFinset_dvd_card_add_subFinset X Hi
      obtain ⟨c2, hc2⟩ := card_subFinset_dvd_card_add_subFinset Y Hi
      obtain ⟨c3, hc3⟩ := card_subFinset_dvd_of_le hHile
      have hpos := card_subFinset_pos Hi
      have hc_lt : c1 + c2 < c3 := by nlinarith
      have hstep : (X + subFinset Hi).card + (Y + subFinset Hi).card + (subFinset Hi).card ≤
          (subFinset H).card := by nlinarith
      have hXle : X.card ≤ (X + subFinset Hi).card := Finset.card_le_card (subset_add_subFinset _ _)
      have hYle : Y.card ≤ (Y + subFinset Hi).card := Finset.card_le_card (subset_add_subFinset _ _)
      linarith
    have h2_1 : A1.card + B1.card + (subFinset H1).card ≤ (subFinset H).card :=
      heq2 A1 B1 H1 hH1lt.le heq1_1
    have h2_2 : A2.card + B2.card + (subFinset H2).card ≤ (subFinset H).card :=
      heq2 A2 B2 H2 hH2lt.le heq1_2
    set S := (a +ᵥ subFinset H) \ (A1 ∪ B2)
    set T := (b +ᵥ subFinset H) \ (A2 ∪ B1)
    have hST_disj : Disjoint S T := hcos_disj.mono Finset.sdiff_subset Finset.sdiff_subset
    have hS_disj_U : Disjoint S (A ∪ B') := by
      rw [Finset.disjoint_left]
      intro z hzS hzU
      obtain ⟨hza, hznot⟩ := Finset.mem_sdiff.mp hzS
      apply hznot
      rcases Finset.mem_union.mp hzU with hzA | hzB'
      · exact Finset.mem_union_left B2 (Finset.mem_inter.mpr ⟨hzA, hza⟩)
      · exact Finset.mem_union_right A1 (Finset.mem_inter.mpr ⟨hzB', hza⟩)
    have hT_disj_U : Disjoint T (A ∪ B') := by
      rw [Finset.disjoint_left]
      intro z hzT hzU
      obtain ⟨hzb, hznot⟩ := Finset.mem_sdiff.mp hzT
      apply hznot
      rcases Finset.mem_union.mp hzU with hzA | hzB'
      · exact Finset.mem_union_left B1 (Finset.mem_inter.mpr ⟨hzA, hzb⟩)
      · exact Finset.mem_union_right A2 (Finset.mem_inter.mpr ⟨hzB', hzb⟩)
    have hS_sub : S ⊆ (A ∪ B') + subFinset H := by
      intro z hz
      obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_sdiff.mp hz).1
      exact Finset.mem_add.mpr ⟨a, Finset.mem_union_left B' ha, h, hh, by simp [vadd_eq_add]⟩
    have hT_sub : T ⊆ (A ∪ B') + subFinset H := by
      intro z hz
      obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_sdiff.mp hz).1
      exact Finset.mem_add.mpr ⟨b, Finset.mem_union_right A hb, h, hh, by simp [vadd_eq_add]⟩
    have hUH_ge : S.card + T.card + (A ∪ B').card ≤ ((A ∪ B') + subFinset H).card := by
      have h1 : S ∪ T ∪ (A ∪ B') ⊆ (A ∪ B') + subFinset H :=
        Finset.union_subset (Finset.union_subset hS_sub hT_sub) (subset_add_subFinset _ _)
      have hdisj1 : Disjoint (S ∪ T) (A ∪ B') := Finset.disjoint_union_left.mpr ⟨hS_disj_U, hT_disj_U⟩
      calc S.card + T.card + (A ∪ B').card
          = (S ∪ T).card + (A ∪ B').card := by rw [Finset.card_union_of_disjoint hST_disj]
        _ = (S ∪ T ∪ (A ∪ B')).card := (Finset.card_union_of_disjoint hdisj1).symm
        _ ≤ ((A ∪ B') + subFinset H).card := Finset.card_le_card h1
    have hC_ineq : (A ∩ B').card + ((A ∪ B') + subFinset H).card ≤
        C.card + (subFinset H).card := hC_conv.2
    have hA1le : A1.card ≤ (A1 + subFinset H1).card := Finset.card_le_card (subset_add_subFinset _ _)
    have hB1le : B1.card ≤ (B1 + subFinset H1).card := Finset.card_le_card (subset_add_subFinset _ _)
    have hA2le : A2.card ≤ (A2 + subFinset H2).card := Finset.card_le_card (subset_add_subFinset _ _)
    have hB2le : B2.card ≤ (B2 + subFinset H2).card := Finset.card_le_card (subset_add_subFinset _ _)
    have hH_le_a : (subFinset H).card ≤ S.card + A1.card + B2.card := by
      have hsub : a +ᵥ subFinset H ⊆ S ∪ (A1 ∪ B2) := by
        intro z hz
        by_cases hmem : z ∈ A1 ∪ B2
        · exact Finset.mem_union_right S hmem
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hmem⟩)
      calc (subFinset H).card = (a +ᵥ subFinset H).card := (Finset.card_vadd_finset a _).symm
        _ ≤ (S ∪ (A1 ∪ B2)).card := Finset.card_le_card hsub
        _ ≤ S.card + (A1 ∪ B2).card := Finset.card_union_le _ _
        _ ≤ S.card + (A1.card + B2.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = S.card + A1.card + B2.card := by ring
    have hH_le_b : (subFinset H).card ≤ T.card + A2.card + B1.card := by
      have hsub : b +ᵥ subFinset H ⊆ T ∪ (A2 ∪ B1) := by
        intro z hz
        by_cases hmem : z ∈ A2 ∪ B1
        · exact Finset.mem_union_right T hmem
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz, hmem⟩)
      calc (subFinset H).card = (b +ᵥ subFinset H).card := (Finset.card_vadd_finset b _).symm
        _ ≤ (T ∪ (A2 ∪ B1)).card := Finset.card_le_card hsub
        _ ≤ T.card + (A2 ∪ B1).card := Finset.card_union_le _ _
        _ ≤ T.card + (A2.card + B1.card) := Nat.add_le_add_left (Finset.card_union_le _ _) _
        _ = T.card + A2.card + B1.card := by ring
    have h3_1 : S.card + T.card + A1.card + B1.card < (subFinset H).card + (subFinset H1).card := by
      linarith
    have h3_2 : S.card + T.card + A2.card + B2.card < (subFinset H).card + (subFinset H2).card := by
      linarith
    linarith

def finsetListSum {G : Type*} [AddCommMonoid G] [DecidableEq G] : List (Finset G) → Finset G
  | [] => {0}
  | A :: L => A + finsetListSum L

lemma finsetListSum_nonempty {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (L : List (Finset G)) (hL : ∀ A ∈ L, A.Nonempty) :
    (finsetListSum L).Nonempty := by
  induction L with
  | nil => exact ⟨0, by simp [finsetListSum]⟩
  | cons A L ih =>
    exact (hL A (by simp)).add (ih (fun B hB => hL B (by simp [hB])))

lemma stab_add_subFinset_eq {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {S B : Finset G} :
    stab (S + subFinset (stab (S + B))) = stab (S + B) := by
  set H := stab (S + B)
  apply le_antisymm
  · intro g hg
    show g +ᵥ (S + B) = S + B
    have h1 : g +ᵥ (S + subFinset H) = S + subFinset H := hg
    have h2 : S + subFinset H + B = S + B := by
      rw [add_right_comm, add_subFinset_eq_self_of_le_stab (show H ≤ stab (S + B) from le_rfl)]
    calc g +ᵥ (S + B) = g +ᵥ (S + subFinset H + B) := by rw [h2]
      _ = (g +ᵥ (S + subFinset H)) + B := vadd_add_finset g _ B
      _ = S + subFinset H + B := by rw [h1]
      _ = S + B := h2
  · rw [le_stab_iff_add_subFinset_eq]
    exact add_subFinset_add_subFinset S H

lemma finsetListSum_add_subFinset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (L : List (Finset G)) (hLne : L ≠ []) (H : AddSubgroup G) :
    finsetListSum (L.map (fun A => A + subFinset H)) = finsetListSum L + subFinset H := by
  induction L with
  | nil => contradiction
  | cons A L ih =>
    cases L with
    | nil =>
      simp only [List.map_cons, List.map_nil, finsetListSum, add_zero_singleton]
    | cons B L' =>
      have hne : B :: L' ≠ [] := List.cons_ne_nil _ _
      have hih := ih hne
      simp only [List.map_cons, finsetListSum] at hih ⊢
      rw [hih]
      calc (A + subFinset H) + (B + finsetListSum L' + subFinset H)
          = (A + (B + finsetListSum L')) + (subFinset H + subFinset H) := by abel
        _ = (A + (B + finsetListSum L')) + subFinset H := by
            rw [← add_assoc, add_subFinset_add_subFinset, add_assoc]

theorem kneser_list_sum {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (L : List (Finset G)) (hLne : L ≠ []) (hL : ∀ A ∈ L, A.Nonempty) :
    (L.map (fun A => (A + subFinset (stab (finsetListSum L))).card)).sum ≤
      (finsetListSum L).card + (L.length - 1) * (subFinset (stab (finsetListSum L))).card := by
  have hmain : ∀ (n : ℕ) (L : List (Finset G)), L.length = n → L ≠ [] → (∀ A ∈ L, A.Nonempty) →
      (L.map (fun A => (A + subFinset (stab (finsetListSum L))).card)).sum ≤
        (finsetListSum L).card + (L.length - 1) * (subFinset (stab (finsetListSum L))).card := by
    intro n
    induction n with
    | zero =>
      intro L hlen hne _
      exact absurd (List.eq_nil_of_length_eq_zero hlen) hne
    | succ n ih =>
      intro L hlen hne hL
      cases L with
      | nil => contradiction
      | cons A R =>
        cases R with
        | nil =>
          simp only [finsetListSum, add_zero_singleton, List.map_cons,
            List.map_nil, List.sum_cons, List.sum_nil, add_zero, List.length_singleton,
            Nat.sub_self, zero_mul]
          rw [add_subFinset_eq_self_of_le_stab le_rfl]
        | cons B L' =>
          set R := B :: L'
          have hRlen : R.length = n := by simpa [R] using hlen
          have hRne : R ≠ [] := List.cons_ne_nil _ _
          have hA : A.Nonempty := hL A (by simp)
          have hR : ∀ X ∈ R, X.Nonempty := fun X hX => hL X (by simp [R, hX])
          have hSR : (finsetListSum R).Nonempty := finsetListSum_nonempty R hR
          set S := finsetListSum R
          set H := stab (A + S)
          have hK2 := kneser_add ((A + S).card + A.card) G A S hA hSR le_rfl
          have hstab_SH : stab (S + subFinset H) = H := by
            have hcomm : A + S = S + A := add_comm A S
            simpa [H, hcomm] using stab_add_subFinset_eq (S := S) (B := A)
          set R' := R.map (fun X => X + subFinset H)
          have hR'len : R'.length = n := by simp [R', hRlen]
          have hR'ne : R' ≠ [] := by simp [R', hRne]
          have hR' : ∀ X ∈ R', X.Nonempty := by
            intro X hX
            obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
            exact (hR Y hY).add ⟨0, zero_mem_subFinset H⟩
          have hsumR' : finsetListSum R' = S + subFinset H :=
            finsetListSum_add_subFinset R hRne H
          have hih := ih R' hR'len hR'ne hR'
          rw [hsumR', hstab_SH] at hih
          have hmap_eq : (R'.map (fun X => (X + subFinset H).card)).sum =
              (R.map (fun X => (X + subFinset H).card)).sum := by
            simp only [R', List.map_map]
            congr 1
            apply List.map_congr_left
            intro X _
            simp only [Function.comp_apply, add_subFinset_add_subFinset]
          rw [hmap_eq, show R'.length = R.length by simp [R']] at hih
          have hRpos : 1 ≤ R.length := by simp [R]
          change (A + subFinset H).card + (R.map (fun X => (X + subFinset H).card)).sum ≤
            (A + S).card + ((A :: R).length - 1) * (subFinset H).card
          have hlen_eq : (A :: R).length - 1 = (R.length - 1) + 1 := by simp [R]
          rw [hlen_eq, add_mul, one_mul]
          linarith
  exact hmain L.length L rfl hLne hL

end Kneser


section KneserCorollaries

lemma card_subFinset_top_zmod (b : ℕ) [NeZero b] :
    (subFinset (⊤ : AddSubgroup (ZMod b))).card = b := by
  rw [subFinset_top, Finset.card_univ, ZMod.card]

lemma zmod_subgroup_char (b : ℕ) [NeZero b] (H : AddSubgroup (ZMod b)) :
    let d := b / (subFinset H).card
    d ∣ b ∧ 0 < d ∧ (subFinset H).card * d = b ∧
      (H = ⊤ ↔ d = 1) ∧
      (∀ x : ℕ, (x : ZMod b) ∈ H ↔ d ∣ x) := by
  set q := (subFinset H).card
  have hqpos : 0 < q := card_subFinset_pos H
  have hqdvd : q ∣ b := by
    have := card_subFinset_dvd_of_le (le_top : H ≤ ⊤)
    rwa [card_subFinset_top_zmod b] at this
  set d := b / q
  have hmul : q * d = b := Nat.mul_div_cancel' hqdvd
  have hd_dvd : d ∣ b := ⟨q, by rw [mul_comm, hmul]⟩
  have hbpos : 0 < b := NeZero.pos b
  have hdpos : 0 < d := by
    by_contra h0
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h0
    rw [hd0, mul_zero] at hmul
    omega
  have htop : H = ⊤ ↔ d = 1 := by
    constructor
    · intro h
      have hqeq : q = b := by rw [show q = (subFinset H).card from rfl, h, card_subFinset_top_zmod b]
      dsimp [d]; rw [hqeq, Nat.div_self hbpos]
    · intro hd1
      have hqb : q = b := by nlinarith
      ext x
      simp only [AddSubgroup.mem_top, iff_true]
      have heq : subFinset H = Finset.univ :=
        Finset.eq_univ_of_card (subFinset H) (by rw [ZMod.card]; exact hqb)
      exact mem_subFinset.mp (heq ▸ Finset.mem_univ x)
  -- Characterize H as {y : ZMod b | d ∣ y.val}
  set M : Finset (ZMod b) := Finset.univ.filter (fun y : ZMod b => d ∣ y.val)
  have hsub_M : subFinset H ⊆ M := by
    intro y hy
    have hyH : y ∈ H := mem_subFinset.mp hy
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ y, ?_⟩
    -- Order of y in H divides |H| = q, so q • y = 0 in ZMod b
    have hcardH : Fintype.card H = q := by
      rw [Fintype.card_subtype]
      rfl
    have hqyH : q • (⟨y, hyH⟩ : H) = 0 := by
      rw [← hcardH]
      obtain ⟨c, hc⟩ := addOrderOf_dvd_card (x := (⟨y, hyH⟩ : H))
      rw [hc, mul_nsmul, addOrderOf_nsmul_eq_zero, smul_zero]
    have hqy : q • y = 0 := congrArg Subtype.val hqyH
    have hval : ((q * y.val : ℕ) : ZMod b) = 0 := by
      rw [Nat.cast_mul, ← nsmul_eq_mul, ZMod.natCast_zmod_val, hqy]
    have hbdvd : b ∣ q * y.val := (ZMod.natCast_eq_zero_iff _ _).mp hval
    exact (Nat.mul_dvd_mul_iff_left hqpos).mp (hmul.symm ▸ hbdvd)
  have hM_card : M.card = q := by
    have hbij : M = (Finset.range q).image (fun k => ((d * k : ℕ) : ZMod b)) := by
      ext y
      simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_range]
      constructor
      · rintro ⟨k, hk⟩
        have hlt : k < q := by
          have hy_lt : y.val < b := y.val_lt
          nlinarith
        refine ⟨k, hlt, ?_⟩
        rw [← hk, ZMod.natCast_zmod_val]
      · rintro ⟨k, hk, rfl⟩
        have hlt : d * k < b := by nlinarith
        rw [ZMod.val_natCast_of_lt hlt]
        exact dvd_mul_right d k
    rw [hbij, Finset.card_image_of_injOn]
    · exact Finset.card_range q
    · intro k1 hk1 k2 hk2 heq
      rw [Finset.mem_coe, Finset.mem_range] at hk1 hk2
      have h1 : d * k1 < b := by nlinarith
      have h2 : d * k2 < b := by nlinarith
      have hval := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
      exact Nat.eq_of_mul_eq_mul_left hdpos hval
  have hH_eq_M : subFinset H = M :=
    Finset.eq_of_subset_of_card_le hsub_M (by rw [hM_card])
  refine ⟨hd_dvd, hdpos, hmul, htop, ?_⟩
  intro x
  rw [← mem_subFinset, hH_eq_M]
  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and, ZMod.val_natCast]
  exact Nat.dvd_mod_iff hd_dvd

lemma card_add_subFinset_ge_two_mul_of_not_subset {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {P : Finset G} {H : AddSubgroup G} (h0 : (0 : G) ∈ P) (hnot : ¬ (P : Set G) ⊆ H) :
    2 * (subFinset H).card ≤ (P + subFinset H).card := by
  have hex : ∃ p ∈ P, p ∉ H := by
    by_contra hall
    push Not at hall
    exact hnot hall
  obtain ⟨p, hpP, hpnH⟩ := hex
  have hdisj : Disjoint (subFinset H) (p +ᵥ subFinset H) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hx2
    apply hpnH
    have : p = (p + h) - h := by abel
    rw [this]
    exact H.sub_mem (mem_subFinset.mp hx1) (mem_subFinset.mp hh)
  have hsub1 : subFinset H ⊆ P + subFinset H := by
    intro h hh
    exact Finset.mem_add.mpr ⟨0, h0, h, hh, zero_add h⟩
  have hsub2 : p +ᵥ subFinset H ⊆ P + subFinset H := by
    intro x hx
    obtain ⟨h, hh, rfl⟩ := Finset.mem_vadd_finset.mp hx
    exact Finset.mem_add.mpr ⟨p, hpP, h, hh, rfl⟩
  calc 2 * (subFinset H).card
      = (subFinset H).card + (p +ᵥ subFinset H).card := by
        rw [Finset.card_vadd_finset, two_mul]
    _ = (subFinset H ∪ (p +ᵥ subFinset H)).card := (Finset.card_union_of_disjoint hdisj).symm
    _ ≤ (P + subFinset H).card := Finset.card_le_card (Finset.union_subset hsub1 hsub2)

-- Corollary A (Lemma 2.3): Cochrane-Ostergaard-Spencer for k * P
theorem cos_sumset_bound {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (P : Finset G) (h0 : (0 : G) ∈ P) (hgen : AddSubgroup.closure (P : Set G) = ⊤)
    (k : ℕ) (hk : 1 ≤ k) :
    (finsetListSum (List.replicate k P)).card = Fintype.card G ∨
      k * P.card ≤ 2 * (finsetListSum (List.replicate k P)).card := by
  set L := List.replicate k P
  have hLne : L ≠ [] := by simp [L]; omega
  have hL : ∀ A ∈ L, A.Nonempty := by
    intro A hA
    rw [List.mem_replicate] at hA
    exact hA.2 ▸ ⟨0, h0⟩
  set S := finsetListSum L
  set H := stab S
  by_cases hH : H = ⊤
  · left
    have hSne : S.Nonempty := finsetListSum_nonempty L hL
    obtain ⟨s, hs⟩ := hSne
    have hSu : S = Finset.univ := by
      ext x
      simp only [Finset.mem_univ, iff_true]
      have hst : (x - s) +ᵥ S = S := by
        have : x - s ∈ H := hH ▸ AddSubgroup.mem_top _
        exact this
      rw [← hst]
      exact Finset.mem_vadd_finset.mpr ⟨s, hs, by simp [vadd_eq_add]⟩
    rw [hSu, Finset.card_univ]
  · right
    have hnot : ¬ (P : Set G) ⊆ H := by
      intro hsub
      have hle : AddSubgroup.closure (P : Set G) ≤ H := (AddSubgroup.closure_le H).mpr hsub
      rw [hgen] at hle
      exact hH (top_le_iff.mp hle)
    have h2H : 2 * (subFinset H).card ≤ (P + subFinset H).card :=
      card_add_subFinset_ge_two_mul_of_not_subset h0 hnot
    have hPle : P.card ≤ (P + subFinset H).card :=
      Finset.card_le_card (subset_add_subFinset P H)
    have hK := kneser_list_sum L hLne hL
    have hmap : (L.map (fun A => (A + subFinset H).card)).sum = k * (P + subFinset H).card := by
      simp [L, List.map_replicate, List.sum_replicate, smul_eq_mul]
    rw [hmap, List.length_replicate] at hK
    have hHpos : 1 ≤ (subFinset H).card := card_subFinset_pos H
    -- 2 * (|P + H| - |H|) ≥ |P| and k * |P + H| ≤ |S| + (k - 1) * |H|
    have hdiff : P.card + 2 * (subFinset H).card ≤ 2 * (P + subFinset H).card := by omega
    have hmul : k * P.card + 2 * k * (subFinset H).card ≤ 2 * (k * (P + subFinset H).card) := by
      calc k * P.card + 2 * k * (subFinset H).card
          = k * (P.card + 2 * (subFinset H).card) := by ring
        _ ≤ k * (2 * (P + subFinset H).card) := Nat.mul_le_mul_left k hdiff
        _ = 2 * (k * (P + subFinset H).card) := by ring
    have hK2 : 2 * (k * (P + subFinset H).card) ≤
        2 * S.card + 2 * (k - 1) * (subFinset H).card := by linarith
    have hksub : 2 * (k - 1) * (subFinset H).card ≤ 2 * k * (subFinset H).card := by
      apply Nat.mul_le_mul_right
      omega
    linarith


theorem cos_sumset_bound_subgroup {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (K : AddSubgroup G) (P : Finset G) (h0 : (0 : G) ∈ P)
    (hPK : P ⊆ subFinset K) (hgen : K ≤ AddSubgroup.closure (P : Set G))
    (k : ℕ) (hk : 1 ≤ k) :
    (subFinset K).card ≤ (finsetListSum (List.replicate k P)).card ∨
      k * P.card ≤ 2 * (finsetListSum (List.replicate k P)).card := by
  set L := List.replicate k P
  have hLne : L ≠ [] := by simp [L]; omega
  have hL : ∀ A ∈ L, A.Nonempty := by
    intro A hA
    rw [List.mem_replicate] at hA
    exact hA.2 ▸ ⟨0, h0⟩
  set S := finsetListSum L
  set H := stab S
  have h0S : (0 : G) ∈ S := by
    have haux : ∀ m : ℕ, (0 : G) ∈ finsetListSum (List.replicate m P) := by
      intro m
      induction m with
      | zero => simp [finsetListSum]
      | succ m ihm =>
        rw [List.replicate_succ, finsetListSum]
        exact Finset.mem_add.mpr ⟨0, h0, 0, ihm, add_zero 0⟩
    exact haux k
  have hSK : S ⊆ subFinset K := by
    have haux : ∀ m : ℕ, finsetListSum (List.replicate m P) ⊆ subFinset K := by
      intro m
      induction m with
      | zero =>
        intro x hx
        simp only [List.replicate_zero, finsetListSum, Finset.mem_singleton] at hx
        exact hx ▸ zero_mem_subFinset K
      | succ m ihm =>
        rw [List.replicate_succ, finsetListSum]
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
        exact mem_subFinset.mpr (K.add_mem (mem_subFinset.mp (hPK ha)) (mem_subFinset.mp (ihm hb)))
    exact haux k
  have hHK : H ≤ K := by
    intro g hg
    have hgS : g ∈ S := by
      have : g +ᵥ (0 : G) ∈ g +ᵥ S := Finset.vadd_mem_vadd_finset h0S
      rw [hg, vadd_eq_add, add_zero] at this
      exact this
    exact mem_subFinset.mp (hSK hgS)
  by_cases hH : H = K
  · left
    have hsub : subFinset K ⊆ S := by
      intro x hx
      have hxH : x ∈ H := hH ▸ mem_subFinset.mp hx
      have hst : x +ᵥ S = S := hxH
      rw [← hst]
      exact Finset.mem_vadd_finset.mpr ⟨0, h0S, by simp [vadd_eq_add]⟩
    exact Finset.card_le_card hsub
  · right
    have hnot : ¬ (P : Set G) ⊆ H := by
      intro hsub
      have hle : AddSubgroup.closure (P : Set G) ≤ H := (AddSubgroup.closure_le H).mpr hsub
      exact hH (le_antisymm hHK (hgen.trans hle))
    have h2H : 2 * (subFinset H).card ≤ (P + subFinset H).card :=
      card_add_subFinset_ge_two_mul_of_not_subset h0 hnot
    have hPle : P.card ≤ (P + subFinset H).card :=
      Finset.card_le_card (subset_add_subFinset P H)
    have hK := kneser_list_sum L hLne hL
    have hmap : (L.map (fun A => (A + subFinset H).card)).sum = k * (P + subFinset H).card := by
      simp [L, List.map_replicate, List.sum_replicate, smul_eq_mul]
    rw [hmap, List.length_replicate] at hK
    have hdiff : P.card + 2 * (subFinset H).card ≤ 2 * (P + subFinset H).card := by omega
    have hmul : k * P.card + 2 * k * (subFinset H).card ≤ 2 * (k * (P + subFinset H).card) := by
      calc k * P.card + 2 * k * (subFinset H).card
          = k * (P.card + 2 * (subFinset H).card) := by ring
        _ ≤ k * (2 * (P + subFinset H).card) := Nat.mul_le_mul_left k hdiff
        _ = 2 * (k * (P + subFinset H).card) := by ring
    have hK2 : 2 * (k * (P + subFinset H).card) ≤
        2 * S.card + 2 * (k - 1) * (subFinset H).card := by linarith
    have hksub : 2 * (k - 1) * (subFinset H).card ≤ 2 * k * (subFinset H).card := by
      apply Nat.mul_le_mul_right
      omega
    linarith

-- Subset sums in ZMod d from a Finset ℕ
def subsetSumMod (d : ℕ) (A : Finset ℕ) : Finset (ZMod d) :=
  A.powerset.image (fun S => ((S.sum id : ℕ) : ZMod d))

lemma subsetSumMod_insert (d a : ℕ) (A : Finset ℕ) (ha : a ∉ A) :
    subsetSumMod d (insert a A) = ({0, (a : ZMod d)} : Finset (ZMod d)) + subsetSumMod d A := by
  ext x
  simp only [subsetSumMod, Finset.mem_image, Finset.mem_powerset, Finset.mem_add,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨S, hS, rfl⟩
    by_cases haS : a ∈ S
    · refine ⟨(a : ZMod d), Or.inr rfl, (((S.erase a).sum id : ℕ) : ZMod d),
        ⟨S.erase a, fun y hy => by
          have hyS := hS (Finset.mem_of_mem_erase hy)
          exact (Finset.mem_insert.mp hyS).resolve_left (Finset.ne_of_mem_erase hy), rfl⟩, ?_⟩
      rw [← Nat.cast_add]; congr 1; exact Finset.add_sum_erase S id haS
    · refine ⟨0, Or.inl rfl, ((S.sum id : ℕ) : ZMod d),
        ⟨S, fun y hy => (Finset.mem_insert.mp (hS hy)).resolve_left (fun h => haS (h ▸ hy)), rfl⟩,
        zero_add _⟩
  · rintro ⟨u, hu, _, ⟨S, hS, rfl⟩, rfl⟩
    rcases hu with rfl | rfl
    · exact ⟨S, hS.trans (Finset.subset_insert a _), by simp⟩
    · have haS : a ∉ S := fun h => ha (hS h)
      refine ⟨insert a S, Finset.insert_subset_insert a hS, ?_⟩
      rw [Finset.sum_insert haS, id_eq, Nat.cast_add]

lemma subsetSumMod_eq_finsetListSum (d : ℕ) (A : Finset ℕ) :
    subsetSumMod d A = finsetListSum (A.toList.map (fun a : ℕ => ({0, (a : ZMod d)} : Finset (ZMod d)))) := by
  have haux : ∀ (L : List ℕ), L.Nodup →
      subsetSumMod d L.toFinset = finsetListSum (L.map (fun a : ℕ => ({0, (a : ZMod d)} : Finset (ZMod d)))) := by
    intro L
    induction L with
    | nil =>
      intro _
      ext x
      simp [subsetSumMod, finsetListSum]
    | cons a L ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      have ha_not : a ∉ L.toFinset := by simpa using hnd.1
      rw [List.toFinset_cons, subsetSumMod_insert d a L.toFinset ha_not,
        List.map_cons, finsetListSum, ih hnd.2]
  have := haux A.toList (Finset.nodup_toList A)
  simpa using this

-- Corollary B (Lemma 5.8): subset sums cover ZMod d
theorem subsetSumMod_eq_univ {d : ℕ} [NeZero d] (A : Finset ℕ)
    (hdiv : ∀ d' : ℕ, d' ∣ d → 1 < d' → d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card) :
    subsetSumMod d A = Finset.univ := by
  have hd : 0 < d := NeZero.pos d
  by_cases hAe : A = ∅
  · subst hAe
    have hd1 : d = 1 := by
      by_contra hne
      have hgt : 1 < d := by omega
      have h := hdiv d dvd_rfl hgt
      simp at h
      omega
    subst hd1
    ext x
    simp only [Finset.mem_univ, iff_true, subsetSumMod, Finset.mem_image, Finset.mem_powerset]
    exact ⟨∅, Finset.empty_subset _, Subsingleton.elim _ _⟩
  · set L := A.toList.map (fun a : ℕ => ({0, (a : ZMod d)} : Finset (ZMod d)))
    have hLne : L ≠ [] := by
      simp [L, Finset.toList_eq_nil, hAe]
    have hL : ∀ X ∈ L, X.Nonempty := by
      intro X hX
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hX
      exact ⟨0, by simp⟩
    have hS_eq : subsetSumMod d A = finsetListSum L := subsetSumMod_eq_finsetListSum d A
    rw [hS_eq]
    set S := finsetListSum L
    set H := stab S
    have ⟨hd'_dvd, hd'pos, hmul, htop, hchar⟩ := zmod_subgroup_char d H
    set d' := d / (subFinset H).card
    by_cases hd'1 : d' = 1
    · have hHtop : H = ⊤ := htop.mpr hd'1
      obtain ⟨s, hs⟩ := finsetListSum_nonempty L hL
      ext x
      simp only [Finset.mem_univ, iff_true]
      have hst : (x - s) +ᵥ S = S := by
        have : x - s ∈ H := hHtop ▸ AddSubgroup.mem_top _
        exact this
      rw [← hst]
      exact Finset.mem_vadd_finset.mpr ⟨s, hs, by simp [vadd_eq_add]⟩
    · have hd'gt : 1 < d' := by omega
      have hK := kneser_list_sum L hLne hL
      have hsum_eq : (L.map (fun X => (X + subFinset H).card)).sum =
          ∑ a ∈ A, (({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H).card := by
        simp only [L, List.map_map]
        exact Finset.sum_map_toList A (fun a : ℕ => (({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H).card)
      rw [hsum_eq, show L.length = A.card by simp [L]] at hK
      have hterm : ∀ a ∈ A,
          (if ¬ d' ∣ a then (subFinset H).card else 0) + (subFinset H).card ≤
            (({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H).card := by
        intro a _
        by_cases hnd : d' ∣ a
        · rw [if_neg (not_not.mpr hnd)]
          have hsub : subFinset H ⊆ ({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H := by
            intro h hh
            exact Finset.mem_add.mpr ⟨0, by simp, h, hh, zero_add h⟩
          have := Finset.card_le_card hsub
          omega
        · rw [if_pos hnd]
          have hnotH : (a : ZMod d) ∉ H := fun h => hnd ((hchar a).mp h)
          have hnot_sub : ¬ (({0, (a : ZMod d)} : Finset (ZMod d)) : Set (ZMod d)) ⊆ H := by
            intro hsub
            exact hnotH (hsub (by simp))
          have h0m : (0 : ZMod d) ∈ ({0, (a : ZMod d)} : Finset (ZMod d)) := by simp
          have := card_add_subFinset_ge_two_mul_of_not_subset h0m hnot_sub
          omega
      have hsum_ge :
          (A.filter (fun a => ¬ d' ∣ a)).card * (subFinset H).card + A.card * (subFinset H).card ≤
            ∑ a ∈ A, (({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H).card := by
        calc (A.filter (fun a => ¬ d' ∣ a)).card * (subFinset H).card + A.card * (subFinset H).card
            = (∑ a ∈ A, if ¬ d' ∣ a then (subFinset H).card else 0) +
                (∑ _a ∈ A, (subFinset H).card) := by
              rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
                Finset.sum_const, smul_eq_mul, smul_eq_mul]
          _ = ∑ a ∈ A, ((if ¬ d' ∣ a then (subFinset H).card else 0) + (subFinset H).card) :=
              (Finset.sum_add_distrib).symm
          _ ≤ ∑ a ∈ A, (({0, (a : ZMod d)} : Finset (ZMod d)) + subFinset H).card :=
              Finset.sum_le_sum hterm
      have hcnt : d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card := hdiv d' hd'_dvd hd'gt
      have hApos : 1 ≤ A.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hAe)
      have hSge : d ≤ S.card := by
        have h1 : (d' - 1) * (subFinset H).card + A.card * (subFinset H).card ≤
            S.card + (A.card - 1) * (subFinset H).card := by
          calc (d' - 1) * (subFinset H).card + A.card * (subFinset H).card
              ≤ (A.filter (fun a => ¬ d' ∣ a)).card * (subFinset H).card +
                  A.card * (subFinset H).card :=
                Nat.add_le_add_right (Nat.mul_le_mul_right _ hcnt) _
            _ ≤ _ := hsum_ge
            _ ≤ S.card + (A.card - 1) * (subFinset H).card := hK
        have h2 : A.card * (subFinset H).card =
            (A.card - 1) * (subFinset H).card + (subFinset H).card := by
          calc A.card * (subFinset H).card
              = (A.card - 1 + 1) * (subFinset H).card := by congr 1; omega
            _ = (A.card - 1) * (subFinset H).card + (subFinset H).card := by ring
        have h3 : (d' - 1) * (subFinset H).card + (subFinset H).card = d := by
          calc (d' - 1) * (subFinset H).card + (subFinset H).card
              = (d' - 1 + 1) * (subFinset H).card := by ring
            _ = d' * (subFinset H).card := by congr 1; omega
            _ = (subFinset H).card * d' := mul_comm _ _
            _ = d := hmul
        omega
      exact Finset.eq_univ_of_card S (by rw [ZMod.card]; exact le_antisymm (by
        simpa [ZMod.card] using Finset.card_le_univ S) hSge)

-- Lemma 2.5 (additive shift growth via residue classes mod q)
lemma card_union_vadd_ge (T : Finset ℕ) (q : ℕ) (hq : 0 < q) :
    T.card + (T.image (fun x : ℕ => (x : ZMod q))).card ≤ (T ∪ (q +ᵥ T)).card := by
  have hsub : (T ∪ (q +ᵥ T)).card = T.card + ((q +ᵥ T) \ T).card := by
    rw [← Finset.card_union_of_disjoint Finset.disjoint_sdiff,
      Finset.union_sdiff_self_eq_union]
  rw [hsub]
  apply Nat.add_le_add_left
  set R := T.image (fun x : ℕ => (x : ZMod q))
  let f : ZMod q → ℕ := fun r =>
    if hr : (T.filter (fun x : ℕ => (x : ZMod q) = r)).Nonempty then
      q + (T.filter (fun x : ℕ => (x : ZMod q) = r)).max' hr
    else 0
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro r hr
    rw [Finset.mem_coe] at hr ⊢
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hr
    have hne : (T.filter (fun x : ℕ => (x : ZMod q) = (x0 : ZMod q))).Nonempty :=
      ⟨x0, Finset.mem_filter.mpr ⟨hx0, rfl⟩⟩
    simp only [f, dif_pos hne]
    set mx := (T.filter (fun x : ℕ => (x : ZMod q) = (x0 : ZMod q))).max' hne
    have hmx_mem := Finset.mem_filter.mp (Finset.max'_mem _ hne)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_vadd_finset.mpr ⟨mx, hmx_mem.1, rfl⟩, ?_⟩
    intro hmemT
    have hmemF : q + mx ∈ T.filter (fun x : ℕ => (x : ZMod q) = (x0 : ZMod q)) := by
      refine Finset.mem_filter.mpr ⟨hmemT, ?_⟩
      rw [Nat.cast_add, ZMod.natCast_self, zero_add, hmx_mem.2]
    have hle := Finset.le_max' _ _ hmemF
    omega
  · intro r1 hr1 r2 hr2 heq
    rw [Finset.mem_coe] at hr1 hr2
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp hr1
    obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp hr2
    have hne1 : (T.filter (fun x : ℕ => (x : ZMod q) = (x1 : ZMod q))).Nonempty :=
      ⟨x1, Finset.mem_filter.mpr ⟨hx1, rfl⟩⟩
    have hne2 : (T.filter (fun x : ℕ => (x : ZMod q) = (x2 : ZMod q))).Nonempty :=
      ⟨x2, Finset.mem_filter.mpr ⟨hx2, rfl⟩⟩
    simp only [f, dif_pos hne1, dif_pos hne2] at heq
    have h1 := (Finset.mem_filter.mp (Finset.max'_mem _ hne1)).2
    have h2 := (Finset.mem_filter.mp (Finset.max'_mem _ hne2)).2
    have hcast := congrArg (fun n : ℕ => (n : ZMod q)) heq
    simpa [Nat.cast_add, ZMod.natCast_self, h1, h2] using hcast

-- Corollary C (Weak Lev): Sum of 2*r dense coprime sets in [0, Q] contains a long interval
lemma card_image_zmod_ge_of_subset_Icc {S : Finset ℕ} {Q q : ℕ}
    (hS : S ⊆ Finset.Icc 0 Q) (hq : 0 < q) (hqQ : q ≤ Q) :
    q * S.card ≤ 2 * Q * (S.image (fun x : ℕ => (x : ZMod q))).card := by
  set R := S.image (fun x : ℕ => (x : ZMod q))
  have hfib : ∀ r ∈ R, (S.filter (fun x : ℕ => (x : ZMod q) = r)).card ≤ Q / q + 1 := by
    intro r _
    have hle : (S.filter (fun x : ℕ => (x : ZMod q) = r)).card ≤ (Finset.Icc 0 (Q / q)).card := by
      refine Finset.card_le_card_of_injOn (fun x => x / q) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe] at hx ⊢
        have hxQ : x ≤ Q := (Finset.mem_Icc.mp (hS (Finset.mem_filter.mp hx).1)).2
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.div_le_div_right hxQ⟩
      · intro x1 hx1 x2 hx2 heq
        rw [Finset.mem_coe] at hx1 hx2
        have hr1 := (Finset.mem_filter.mp hx1).2
        have hr2 := (Finset.mem_filter.mp hx2).2
        have hmod : x1 % q = x2 % q := by
          haveI : NeZero q := ⟨Nat.ne_of_gt hq⟩
          have h := congrArg ZMod.val (hr1.trans hr2.symm)
          simpa [ZMod.val_natCast] using h
        dsimp at heq
        have hd1 := Nat.div_add_mod x1 q
        have hd2 := Nat.div_add_mod x2 q
        rw [← hd1, ← hd2, heq, hmod]
    simpa using hle
  have hScard : S.card ≤ R.card * (Q / q + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun x : ℕ => (x : ZMod q)) (t := R)
      (fun x hx => Finset.mem_image_of_mem _ hx)]
    calc ∑ r ∈ R, (S.filter (fun x : ℕ => (x : ZMod q) = r)).card
        ≤ ∑ _r ∈ R, (Q / q + 1) := Finset.sum_le_sum hfib
      _ = R.card * (Q / q + 1) := by rw [Finset.sum_const, smul_eq_mul]
  have hqmul : q * (Q / q + 1) ≤ 2 * Q := by
    rw [mul_add, mul_one]
    have := Nat.mul_div_le Q q
    omega
  calc q * S.card
      ≤ q * (R.card * (Q / q + 1)) := Nat.mul_le_mul_left q hScard
    _ = R.card * (q * (Q / q + 1)) := by ring
    _ ≤ R.card * (2 * Q) := Nat.mul_le_mul_left _ hqmul
    _ = 2 * Q * R.card := by ring

lemma finsetListSum_image_zmod (q : ℕ) (L : List (Finset ℕ)) :
    (finsetListSum L).image (fun x : ℕ => (x : ZMod q)) =
      finsetListSum (L.map (fun S => S.image (fun x : ℕ => (x : ZMod q)))) := by
  induction L with
  | nil =>
    ext x
    simp [finsetListSum]
  | cons A L ih =>
    simp only [finsetListSum, List.map_cons, ← ih]
    ext z
    simp only [Finset.mem_image, Finset.mem_add]
    constructor
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
      exact ⟨(a : ZMod q), ⟨a, ha, rfl⟩, (b : ZMod q), ⟨b, hb, rfl⟩, (Nat.cast_add a b).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, Nat.cast_add a b⟩

lemma weak_lev_half {α_inv Q r : ℕ} (hα : 1 ≤ α_inv) (hQ : 4 * α_inv ≤ Q)
    (hr : 4 * α_inv ≤ r) (S : Fin r → Finset ℕ)
    (hsub : ∀ j, S j ⊆ Finset.Icc 0 Q)
    (h0 : ∀ j, 0 ∈ S j)
    (hdense : ∀ j, Q ≤ α_inv * (S j).card)
    (hcop : ∀ j, ∀ d ≥ 2, ∃ x ∈ S j, ¬ d ∣ x) :
    let T := finsetListSum (List.ofFn S)
    let M := ∑ j : Fin r, (S j).max' ⟨0, h0 j⟩
    T ⊆ Finset.Icc 0 M ∧
    r * Q ≤ 2 * α_inv * M ∧
    ((Finset.Icc 0 M) \ T).card ≤ 1 + 4 * α_inv * Q := by
  -- Helper for prefix sums of length k ≤ r
  have hQpos : 0 < Q := by omega
  have hQj_bounds : ∀ j : Fin r,
      let qj := (S j).max' ⟨0, h0 j⟩
      0 < qj ∧ qj ≤ Q ∧ Q ≤ 2 * α_inv * qj := by
    intro j
    set qj := (S j).max' ⟨0, h0 j⟩
    have hleQ : qj ≤ Q := (Finset.mem_Icc.mp (hsub j (Finset.max'_mem _ _))).2
    have hcard_le : (S j).card ≤ qj + 1 := by
      have h1 : S j ⊆ Finset.Icc 0 qj := fun x hx =>
        Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ x hx⟩
      simpa using Finset.card_le_card h1
    have h2 : Q ≤ α_inv * (qj + 1) := (hdense j).trans (Nat.mul_le_mul_left α_inv hcard_le)
    have h3 : Q ≤ 2 * α_inv * qj := by nlinarith
    have hpos : 0 < qj := by
      by_contra h0j
      have : qj = 0 := by omega
      rw [this, mul_zero] at h3
      omega
    exact ⟨hpos, hleQ, h3⟩
  -- For any prefix of at least 4 * α_inv sets, image mod qj covers all of ZMod qj
  have hcover : ∀ (L : List (Finset ℕ)), 4 * α_inv ≤ L.length →
      (∀ X ∈ L, X ⊆ Finset.Icc 0 Q ∧ 0 ∈ X ∧ Q ≤ α_inv * X.card ∧ ∀ d ≥ 2, ∃ x ∈ X, ¬ d ∣ x) →
      ∀ (q : ℕ), 0 < q → q ≤ Q →
      ((finsetListSum L).image (fun x : ℕ => (x : ZMod q))).card = q := by
    intro L hLlen hLprop q hqpos hqQ
    haveI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
    rw [finsetListSum_image_zmod]
    set L' := L.map (fun X => X.image (fun x : ℕ => (x : ZMod q)))
    have hL'ne : L' ≠ [] := by
      intro he
      have : L.length = 0 := by simpa [L'] using congrArg List.length he
      omega
    have hL'ne_el : ∀ Y ∈ L', Y.Nonempty := by
      intro Y hY
      obtain ⟨X, hXL, rfl⟩ := List.mem_map.mp hY
      exact ⟨0, Finset.mem_image.mpr ⟨0, (hLprop X hXL).2.1, by simp⟩⟩
    set U := finsetListSum L'
    set H := stab U
    have ⟨hd_dvd, hd_pos, hmul, htop, hchar⟩ := zmod_subgroup_char q H
    set d := q / (subFinset H).card
    by_cases hd1 : d = 1
    · have hHtop : H = ⊤ := htop.mpr hd1
      obtain ⟨u, hu⟩ := finsetListSum_nonempty L' hL'ne_el
      have hUuniv : U = Finset.univ := by
        ext z
        simp only [Finset.mem_univ, iff_true]
        have hst : (z - u) +ᵥ U = U := by
          have : z - u ∈ H := hHtop ▸ AddSubgroup.mem_top _
          exact this
        rw [← hst]
        exact Finset.mem_vadd_finset.mpr ⟨u, hu, by simp [vadd_eq_add]⟩
      rw [hUuniv, Finset.card_univ, ZMod.card]
    · exfalso
      have hdgt : 1 < d := by omega
      have hK := kneser_list_sum L' hL'ne hL'ne_el
      have hterm : ∀ Y ∈ L',
          q + 4 * α_inv * (subFinset H).card ≤ 4 * α_inv * (Y + subFinset H).card := by
        intro Y hY
        obtain ⟨X, hXL, rfl⟩ := List.mem_map.mp hY
        obtain ⟨hXsub, hX0, hXdense, hXcop⟩ := hLprop X hXL
        have hY0 : (0 : ZMod q) ∈ X.image (fun x : ℕ => (x : ZMod q)) :=
          Finset.mem_image.mpr ⟨0, hX0, by simp⟩
        have hYnot : ¬ ((X.image (fun x : ℕ => (x : ZMod q)) : Finset (ZMod q)) : Set (ZMod q)) ⊆ H := by
          intro hsubH
          obtain ⟨x, hxX, hnd⟩ := hXcop d (by omega)
          have hxH : (x : ZMod q) ∈ H := hsubH (Finset.mem_image_of_mem _ hxX)
          exact hnd ((hchar x).mp hxH)
        have h2H := card_add_subFinset_ge_two_mul_of_not_subset hY0 hYnot
        have hYle : (X.image (fun x : ℕ => (x : ZMod q))).card ≤
            (X.image (fun x : ℕ => (x : ZMod q)) + subFinset H).card :=
          Finset.card_le_card (subset_add_subFinset _ _)
        have hYcard : q ≤ 2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q))).card := by
          have h1 := card_image_zmod_ge_of_subset_Icc hXsub hqpos hqQ
          have h2 : q * Q ≤ q * (α_inv * X.card) := Nat.mul_le_mul_left q hXdense
          have h3 : q * (α_inv * X.card) = α_inv * (q * X.card) := by ring
          have h4 : α_inv * (q * X.card) ≤ α_inv * (2 * Q * (X.image (fun x : ℕ => (x : ZMod q))).card) :=
            Nat.mul_le_mul_left α_inv h1
          have h5 : q * Q ≤ (2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q))).card) * Q := by nlinarith
          exact Nat.le_of_mul_le_mul_right h5 hQpos
        have hY1 : 2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q))).card ≤
            2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q)) + subFinset H).card :=
          Nat.mul_le_mul_left _ hYle
        have hY2 : 4 * α_inv * (subFinset H).card ≤
            2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q)) + subFinset H).card := by
          calc 4 * α_inv * (subFinset H).card = 2 * α_inv * (2 * (subFinset H).card) := by ring
            _ ≤ 2 * α_inv * (X.image (fun x : ℕ => (x : ZMod q)) + subFinset H).card :=
                Nat.mul_le_mul_left _ h2H
        linarith
      have hsum_ge : L'.length * q + L'.length * (4 * α_inv * (subFinset H).card) ≤
          4 * α_inv * (L'.map (fun Y => (Y + subFinset H).card)).sum := by
        have haux : ∀ (M : List (Finset (ZMod q))),
            (∀ Y ∈ M, q + 4 * α_inv * (subFinset H).card ≤ 4 * α_inv * (Y + subFinset H).card) →
            M.length * q + M.length * (4 * α_inv * (subFinset H).card) ≤
              4 * α_inv * (M.map (fun Y => (Y + subFinset H).card)).sum := by
          intro M
          induction M with
          | nil => intro _; simp
          | cons Y M ihM =>
            intro hM
            have h1 := hM Y (by simp)
            have h2 := ihM (fun Z hZ => hM Z (by simp [hZ]))
            simp only [List.length_cons, List.map_cons, List.sum_cons]
            nlinarith
        exact haux L' hterm
      have hUle : U.card ≤ q := by simpa [ZMod.card] using Finset.card_le_univ U
      have hHpos : 1 ≤ (subFinset H).card := card_subFinset_pos H
      have hL'len : 4 * α_inv ≤ L'.length := by simpa [L'] using hLlen
      have h1 : L'.length * q + L'.length * (4 * α_inv * (subFinset H).card) ≤
          4 * α_inv * U.card + 4 * α_inv * (L'.length - 1) * (subFinset H).card := by
        calc _ ≤ 4 * α_inv * (L'.map (fun Y => (Y + subFinset H).card)).sum := hsum_ge
          _ ≤ 4 * α_inv * (U.card + (L'.length - 1) * (subFinset H).card) :=
              Nat.mul_le_mul_left _ hK
          _ = 4 * α_inv * U.card + 4 * α_inv * (L'.length - 1) * (subFinset H).card := by ring
      have h2 : 4 * α_inv * (L'.length - 1) * (subFinset H).card + 4 * α_inv * (subFinset H).card =
          L'.length * (4 * α_inv * (subFinset H).card) := by
        have hlen1 : L'.length - 1 + 1 = L'.length := by omega
        calc 4 * α_inv * (L'.length - 1) * (subFinset H).card + 4 * α_inv * (subFinset H).card
            = (L'.length - 1 + 1) * (4 * α_inv * (subFinset H).card) := by ring
          _ = L'.length * (4 * α_inv * (subFinset H).card) := by rw [hlen1]
      have h3 : 4 * α_inv * q ≤ L'.length * q := Nat.mul_le_mul_right q hL'len
      have h4 : 4 * α_inv * U.card ≤ 4 * α_inv * q := Nat.mul_le_mul_left _ hUle
      nlinarith
  -- Now prove prefix induction on a list of length r (reversing so we add one set at a time)
  set L := List.ofFn S
  have hLprop : ∀ X ∈ L, X ⊆ Finset.Icc 0 Q ∧ 0 ∈ X ∧ Q ≤ α_inv * X.card ∧ ∀ d ≥ 2, ∃ x ∈ X, ¬ d ∣ x := by
    intro X hX
    rw [List.mem_ofFn] at hX
    obtain ⟨j, rfl⟩ := hX
    exact ⟨hsub j, h0 j, hdense j, hcop j⟩
  -- For any list P with all elements satisfying hLprop:
  -- finsetListSum P ⊆ Icc 0 (sum of maxes), and missing elements ≤ 1 + 4 * α_inv * Q
  have hlist_main : ∀ (P : List (Finset ℕ)),
      (∀ X ∈ P, X ⊆ Finset.Icc 0 Q ∧ 0 ∈ X ∧ Q ≤ α_inv * X.card ∧ ∀ d ≥ 2, ∃ x ∈ X, ¬ d ∣ x) →
      let M_P := (P.map (fun X => if hX : 0 ∈ X then X.max' ⟨0, hX⟩ else 0)).sum
      finsetListSum P ⊆ Finset.Icc 0 M_P ∧
      M_P + 1 ≤ (finsetListSum P).card + (1 + 4 * α_inv * Q) := by
    intro P
    induction P with
    | nil =>
      intro _
      simp [finsetListSum]
    | cons X P ih =>
      intro hP
      have hXprop := hP X (by simp)
      have hPprop : ∀ Y ∈ P, Y ⊆ Finset.Icc 0 Q ∧ 0 ∈ Y ∧ Q ≤ α_inv * Y.card ∧
          ∀ d ≥ 2, ∃ x ∈ Y, ¬ d ∣ x := fun Y hY => hP Y (by simp [hY])
      obtain ⟨hsubP, hcardP⟩ := ih hPprop
      set qX := X.max' ⟨0, hXprop.2.1⟩
      have hqX_leQ : qX ≤ Q := (Finset.mem_Icc.mp (hXprop.1 (Finset.max'_mem _ _))).2
      have hqX_pos : 0 < qX := by
        have h1 : X.card ≤ qX + 1 := by
          simpa using Finset.card_le_card (fun x hx => Finset.mem_Icc.mpr ⟨Nat.zero_le _, Finset.le_max' _ x hx⟩)
        have h2 : Q ≤ α_inv * (qX + 1) := hXprop.2.2.1.trans (Nat.mul_le_mul_left α_inv h1)
        nlinarith
      have hMP_eq : ((X :: P).map (fun Y => if hY : 0 ∈ Y then Y.max' ⟨0, hY⟩ else 0)).sum =
          qX + (P.map (fun Y => if hY : 0 ∈ Y then Y.max' ⟨0, hY⟩ else 0)).sum := by
        simp [qX, hXprop.2.1]
      rw [hMP_eq]
      constructor
      · intro z hz
        obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
        have hxle : x ≤ qX := Finset.le_max' X x hx
        have hyle := (Finset.mem_Icc.mp (hsubP hy)).2
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
      · by_cases hPlen : 4 * α_inv ≤ P.length
        · -- Step grows by at least qX via Lemma 2.5 + hcover!
          have hcov := hcover P hPlen hPprop qX hqX_pos hqX_leQ
          have h25 := card_union_vadd_ge (finsetListSum P) qX hqX_pos
          rw [hcov] at h25
          have hinc : finsetListSum P ∪ (qX +ᵥ finsetListSum P) ⊆ X + finsetListSum P := by
            apply Finset.union_subset
            · intro y hy
              exact Finset.mem_add.mpr ⟨0, hXprop.2.1, y, hy, zero_add y⟩
            · intro z hz
              obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hz
              exact Finset.mem_add.mpr ⟨qX, Finset.max'_mem _ _, y, hy, rfl⟩
          have hcard_ge : (finsetListSum P).card + qX ≤ (X + finsetListSum P).card :=
            h25.trans (Finset.card_le_card hinc)
          simp only [finsetListSum]
          omega
        · -- P.length < 4 * α_inv: M_P + qX ≤ 4 * α_inv * Q directly!
          have hPsum_le : (P.map (fun Y => if hY : 0 ∈ Y then Y.max' ⟨0, hY⟩ else 0)).sum ≤
              P.length * Q := by
            have haux : ∀ (R : List (Finset ℕ)), (∀ Y ∈ R, Y ⊆ Finset.Icc 0 Q) →
                (R.map (fun Y => if hY : 0 ∈ Y then Y.max' ⟨0, hY⟩ else 0)).sum ≤ R.length * Q := by
              intro R
              induction R with
              | nil => intro _; simp
              | cons Y R ihR =>
                intro hR
                simp only [List.map_cons, List.sum_cons, List.length_cons]
                have hR' := ihR (fun Z hZ => hR Z (by simp [hZ]))
                split_ifs with h0Y
                · have hle : Y.max' ⟨0, h0Y⟩ ≤ Q :=
                    (Finset.mem_Icc.mp (hR Y (by simp) (Finset.max'_mem _ _))).2
                  nlinarith
                · nlinarith
            exact haux P (fun Y hY => (hPprop Y hY).1)
          have h1le : 1 ≤ (finsetListSum (X :: P)).card :=
            (finsetListSum_nonempty (X :: P) (fun Y hY => ⟨0, (hP Y hY).2.1⟩)).card_pos
          have hlen_le : P.length + 1 ≤ 4 * α_inv := by omega
          nlinarith
  obtain ⟨hTsub, hTcard⟩ := hlist_main L hLprop
  have hlist_sum_ofFn : ∀ {m : ℕ} (f : Fin m → ℕ), (List.ofFn f).sum = ∑ j : Fin m, f j := by
    intro m
    induction m with
    | zero => intro f; simp
    | succ m ih =>
      intro f
      rw [List.ofFn_succ, List.sum_cons, ih, Fin.sum_univ_succ]
  have hM_eq : (L.map (fun X => if hX : 0 ∈ X then X.max' ⟨0, hX⟩ else 0)).sum =
      ∑ j : Fin r, (S j).max' ⟨0, h0 j⟩ := by
    simp only [L, List.map_ofFn, hlist_sum_ofFn]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [h0 j]
  rw [hM_eq] at hTsub hTcard
  refine ⟨hTsub, ?_, ?_⟩
  · calc r * Q = ∑ _j : Fin r, Q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ j : Fin r, (2 * α_inv * (S j).max' ⟨0, h0 j⟩) :=
          Finset.sum_le_sum fun j _ => (hQj_bounds j).2.2
      _ = 2 * α_inv * ∑ j : Fin r, (S j).max' ⟨0, h0 j⟩ := (Finset.mul_sum _ _ _).symm
  · have hsd := Finset.card_sdiff_add_card_eq_card hTsub
    simp only [Nat.card_Icc, tsub_zero] at hsd
    omega

theorem weak_lev_interval {α_inv Q : ℕ} (hα : 1 ≤ α_inv) (hQ : 4 * α_inv ≤ Q)
    (S : Fin (2 * (16 * α_inv * (4 * α_inv))) → Finset ℕ)
    (hsub : ∀ j, S j ⊆ Finset.Icc 0 Q)
    (h0 : ∀ j, 0 ∈ S j)
    (hdense : ∀ j, Q ≤ α_inv * (S j).card)
    (hcop : ∀ j, ∀ d ≥ 2, ∃ x ∈ S j, ¬ d ∣ x) :
    ∃ a : ℕ, 0 < a ∧ a ≤ (16 * α_inv * (4 * α_inv)) * Q ∧ Finset.Icc a (a + Q) ⊆ finsetListSum (List.ofFn S) := by
  let r := 16 * α_inv * (4 * α_inv)
  have hr : 4 * α_inv ≤ r := by dsimp [r]; nlinarith
  let S1 : Fin r → Finset ℕ := fun j => S ⟨j.1, by omega⟩
  let S2 : Fin r → Finset ℕ := fun j => S ⟨r + j.1, by omega⟩
  obtain ⟨hT1sub, hM1ge, hT1miss⟩ := weak_lev_half hα hQ hr S1
    (fun j => hsub _) (fun j => h0 _) (fun j => hdense _) (fun j => hcop _)
  obtain ⟨hT2sub, hM2ge, hT2miss⟩ := weak_lev_half hα hQ hr S2
    (fun j => hsub _) (fun j => h0 _) (fun j => hdense _) (fun j => hcop _)
  set T1 := finsetListSum (List.ofFn S1)
  set T2 := finsetListSum (List.ofFn S2)
  set M1 := ∑ j : Fin r, (S1 j).max' ⟨0, h0 _⟩
  set M2 := ∑ j : Fin r, (S2 j).max' ⟨0, h0 _⟩
  have hsum_eq : finsetListSum (List.ofFn S) = T1 + T2 := by
    have hsplit : List.ofFn S = List.ofFn S1 ++ List.ofFn S2 := by
      apply List.ext_getElem
      · simp [r, two_mul]
      · intro i hi1 hi2
        by_cases hir : i < r
        · rw [List.getElem_append_left (by simpa using hir)]
          simp [S1]
        · rw [List.getElem_append_right (by simpa using Nat.le_of_not_lt hir)]
          simp only [List.length_ofFn, List.getElem_ofFn, S2]
          congr 1
          ext
          dsimp
          omega
    have happ : ∀ (L1 L2 : List (Finset ℕ)),
        finsetListSum (L1 ++ L2) = finsetListSum L1 + finsetListSum L2 := by
      intro L1 L2
      induction L1 with
      | nil => rw [List.nil_append, finsetListSum, add_comm, add_zero_singleton]
      | cons X L1 ih => simp [finsetListSum, ih, add_assoc]
    rw [hsplit, happ]
  rw [hsum_eq]
  have hM1_big : 32 * α_inv * Q ≤ M1 := by
    have h1 : 2 * α_inv * (32 * α_inv * Q) = r * Q := by dsimp [r]; ring
    nlinarith
  have hM2_big : 32 * α_inv * Q ≤ M2 := by
    have h1 : 2 * α_inv * (32 * α_inv * Q) = r * Q := by dsimp [r]; ring
    nlinarith
  -- Helper: given A ⊆ Icc 0 M1, B ⊆ Icc 0 M2 with M1 ≤ M2 and small missing sets, Icc (M1/2) M1 ⊆ A + B
  have hmerge : ∀ (A B : Finset ℕ) (Ma Mb : ℕ),
      A ⊆ Finset.Icc 0 Ma → B ⊆ Finset.Icc 0 Mb → Ma ≤ Mb →
      32 * α_inv * Q ≤ Ma →
      ((Finset.Icc 0 Ma) \ A).card ≤ 1 + 4 * α_inv * Q →
      ((Finset.Icc 0 Mb) \ B).card ≤ 1 + 4 * α_inv * Q →
      Finset.Icc (Ma / 2) (Ma / 2 + Q) ⊆ A + B := by
    intro A B Ma Mb _ _ hle hMbig hAmiss hBmiss z hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hz
    have hzMa : z ≤ Ma := by
      have h2Q : 2 * Q ≤ 32 * α_inv * Q := by nlinarith
      omega
    have hzMb : z ≤ Mb := hzMa.trans hle
    set badA := (Finset.Icc 0 z).filter (fun x => x ∉ A)
    set badB := (Finset.Icc 0 z).filter (fun x => z - x ∉ B)
    have hbadA_le : badA.card ≤ 1 + 4 * α_inv * Q := by
      have hsubA : badA ⊆ (Finset.Icc 0 Ma) \ A := by
        intro x hx
        obtain ⟨hxI, hxnot⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _,
          (Finset.mem_Icc.mp hxI).2.trans hzMa⟩, hxnot⟩
      exact (Finset.card_le_card hsubA).trans hAmiss
    have hbadB_le : badB.card ≤ 1 + 4 * α_inv * Q := by
      have hsubB : badB.image (fun x => z - x) ⊆ (Finset.Icc 0 Mb) \ B := by
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hxI, hxnot⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩, hxnot⟩
      have hinj : Set.InjOn (fun x => z - x) (badB : Set ℕ) := by
        intro x1 hx1 x2 hx2 heq
        have h1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx1).1).2
        have h2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx2).1).2
        dsimp at heq
        omega
      calc badB.card = (badB.image (fun x => z - x)).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ ((Finset.Icc 0 Mb) \ B).card := Finset.card_le_card hsubB
        _ ≤ 1 + 4 * α_inv * Q := hBmiss
    have hlt : (badA ∪ badB).card < (Finset.Icc 0 z).card := by
      have hu : (badA ∪ badB).card ≤ badA.card + badB.card := Finset.card_union_le _ _
      simp only [Nat.card_Icc, tsub_zero]
      have hf16 : 16 ≤ 4 * α_inv * Q := by nlinarith
      have h32 : 32 * α_inv * Q = 8 * (4 * α_inv * Q) := by ring
      omega
    obtain ⟨x, hxI, hxnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hxA : x ∈ A := by
      by_contra h
      exact hxnot (Finset.mem_union_left badB (Finset.mem_filter.mpr ⟨hxI, h⟩))
    have hzxB : z - x ∈ B := by
      by_contra h
      exact hxnot (Finset.mem_union_right badA (Finset.mem_filter.mpr ⟨hxI, h⟩))
    have hxz : x ≤ z := (Finset.mem_Icc.mp hxI).2
    exact Finset.mem_add.mpr ⟨x, hxA, z - x, hzxB, Nat.add_sub_of_le hxz⟩
  have hM1_le : M1 ≤ r * Q := by
    calc M1 = ∑ j : Fin r, (S1 j).max' ⟨0, h0 _⟩ := rfl
      _ ≤ ∑ _j : Fin r, Q := Finset.sum_le_sum fun j _ =>
          (Finset.mem_Icc.mp (hsub _ (Finset.max'_mem _ _))).2
      _ = r * Q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hM2_le : M2 ≤ r * Q := by
    calc M2 = ∑ j : Fin r, (S2 j).max' ⟨0, h0 _⟩ := rfl
      _ ≤ ∑ _j : Fin r, Q := Finset.sum_le_sum fun j _ =>
          (Finset.mem_Icc.mp (hsub _ (Finset.max'_mem _ _))).2
      _ = r * Q := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  dsimp [r] at hM1_le hM2_le
  have h32pos : 2 ≤ 32 * α_inv * Q := by nlinarith
  rcases le_total M1 M2 with h12 | h21
  · exact ⟨M1 / 2, by omega, by omega, hmerge T1 T2 M1 M2 hT1sub hT2sub h12 hM1_big hT1miss hT2miss⟩
  · rw [add_comm]
    exact ⟨M2 / 2, by omega, by omega, hmerge T2 T1 M2 M1 hT2sub hT1sub h21 hM2_big hT2miss hT1miss⟩

end KneserCorollaries

section Chernoff

lemma mgf_coloring {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Finset α) (C : Finset β) (hβ : 0 < Fintype.card β) (t : ℝ) :
    ∑ f : α → β, Real.exp (t * ((E.filter (fun a => f a ∈ C)).card : ℝ)) =
      (Fintype.card β : ℝ) ^ Fintype.card α *
        (1 + ((C.card : ℝ) / (Fintype.card β : ℝ)) * (Real.exp t - 1)) ^ E.card := by
  let g : α → β → ℝ := fun a y => if a ∈ E ∧ y ∈ C then Real.exp t else 1
  have hprod_eq : ∀ f : α → β,
      ∏ a : α, g a (f a) = Real.exp (t * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
    intro f
    have h1 : ∏ a : α, g a (f a) =
        ∏ a ∈ Finset.univ.filter (fun a => a ∈ E ∧ f a ∈ C), Real.exp t := by
      simp [g, Finset.prod_ite]
    have hfilt : Finset.univ.filter (fun a => a ∈ E ∧ f a ∈ C) = E.filter (fun a => f a ∈ C) := by
      ext a; simp
    rw [h1, hfilt, Finset.prod_const, ← Real.exp_nat_mul, mul_comm]
  have hsum_eq : ∑ f : α → β, Real.exp (t * ((E.filter (fun a => f a ∈ C)).card : ℝ)) =
      ∏ a : α, ∑ y : β, g a y := by
    simp_rw [← hprod_eq]
    exact (Fintype.prod_sum g).symm
  rw [hsum_eq]
  have hβpos : (0 : ℝ) < (Fintype.card β : ℝ) := Nat.cast_pos.mpr hβ
  have hβne : (Fintype.card β : ℝ) ≠ 0 := ne_of_gt hβpos
  have hinner : ∀ a : α, ∑ y : β, g a y =
      if a ∈ E then (Fintype.card β : ℝ) * (1 + ((C.card : ℝ) / (Fintype.card β : ℝ)) * (Real.exp t - 1))
      else (Fintype.card β : ℝ) := by
    intro a
    by_cases ha : a ∈ E
    · simp only [ha, if_true, g, true_and]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      have hC_eq : (Finset.univ.filter (fun y : β => y ∈ C)) = C := by ext y; simp
      have hC_compl : (Finset.univ.filter (fun y : β => y ∉ C)).card = Fintype.card β - C.card := by
        have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun y : β => y ∈ C)
        rw [hC_eq, Finset.card_univ] at h
        omega
      rw [hC_eq, hC_compl]
      have hCle : C.card ≤ Fintype.card β := Finset.card_le_univ C
      rw [Nat.cast_sub hCle]
      field_simp [hβne]
      ring
    · simp [ha, g]
  simp_rw [hinner]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hE_eq : Finset.univ.filter (fun a : α => a ∈ E) = E := by ext a; simp
  have hE_compl : (Finset.univ.filter (fun a : α => a ∉ E)).card = Fintype.card α - E.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun a : α => a ∈ E)
    rw [hE_eq, Finset.card_univ] at h
    omega
  rw [hE_eq, hE_compl, mul_pow]
  have hEle : E.card ≤ Fintype.card α := Finset.card_le_univ E
  calc (Fintype.card β : ℝ) ^ E.card *
        (1 + (C.card : ℝ) / (Fintype.card β : ℝ) * (Real.exp t - 1)) ^ E.card *
        (Fintype.card β : ℝ) ^ (Fintype.card α - E.card)
      = ((Fintype.card β : ℝ) ^ E.card * (Fintype.card β : ℝ) ^ (Fintype.card α - E.card)) *
        (1 + (C.card : ℝ) / (Fintype.card β : ℝ) * (Real.exp t - 1)) ^ E.card := by ring
    _ = (Fintype.card β : ℝ) ^ (E.card + (Fintype.card α - E.card)) *
        (1 + (C.card : ℝ) / (Fintype.card β : ℝ) * (Real.exp t - 1)) ^ E.card := by rw [pow_add]
    _ = (Fintype.card β : ℝ) ^ Fintype.card α *
        (1 + (C.card : ℝ) / (Fintype.card β : ℝ) * (Real.exp t - 1)) ^ E.card := by
          rw [Nat.add_sub_of_le hEle]

lemma chernoff_lower {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Finset α) (C : Finset β) (hβ : 0 < Fintype.card β) :
    let p : ℝ := (C.card : ℝ) / (Fintype.card β : ℝ)
    ((Finset.univ.filter (fun f : α → β =>
        4 * ((E.filter (fun a => f a ∈ C)).card : ℝ) ≤ p * (E.card : ℝ))).card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ) / 4) := by
  intro p
  set bad := Finset.univ.filter (fun f : α → β =>
    4 * ((E.filter (fun a => f a ∈ C)).card : ℝ) ≤ p * (E.card : ℝ))
  have hp0 : 0 ≤ p := by positivity
  have h1 : Real.exp (- p * (E.card : ℝ) / 4) * (bad.card : ℝ) ≤
      ∑ f : α → β, Real.exp ((-1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
    calc Real.exp (- p * (E.card : ℝ) / 4) * (bad.card : ℝ)
        = ∑ _f ∈ bad, Real.exp (- p * (E.card : ℝ) / 4) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ f ∈ bad, Real.exp ((-1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro f hf
          have hcond := (Finset.mem_filter.mp hf).2
          apply Real.exp_le_exp.mpr
          linarith
      _ ≤ ∑ f : α → β, Real.exp ((-1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro f
          exact (Real.exp_pos _).le
  have hmgf := mgf_coloring E C hβ (-1)
  have hexp_inv : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  have hbase_nn : 0 ≤ 1 + p * (Real.exp (-1 : ℝ) - 1) := by
    have hp1 : p ≤ 1 := by
      dsimp [p]
      rw [div_le_one (Nat.cast_pos.mpr hβ)]
      exact Nat.cast_le.mpr (Finset.card_le_univ C)
    have hexp_pos : 0 ≤ Real.exp (-1 : ℝ) := (Real.exp_pos _).le
    nlinarith
  have hbase_le : 1 + p * (Real.exp (-1 : ℝ) - 1) ≤ Real.exp (- p / 2) := by
    have hstep1 : 1 + p * (Real.exp (-1 : ℝ) - 1) ≤ 1 + (- p / 2) := by nlinarith
    calc 1 + p * (Real.exp (-1 : ℝ) - 1)
        ≤ 1 + (- p / 2) := hstep1
      _ = (- p / 2) + 1 := by ring
      _ ≤ Real.exp (- p / 2) := Real.add_one_le_exp _
  have hpow : (1 + p * (Real.exp (-1 : ℝ) - 1)) ^ E.card ≤ Real.exp (- p * (E.card : ℝ) / 2) := by
    calc (1 + p * (Real.exp (-1 : ℝ) - 1)) ^ E.card
        ≤ (Real.exp (- p / 2)) ^ E.card := pow_le_pow_left₀ hbase_nn hbase_le E.card
      _ = Real.exp ((E.card : ℝ) * (- p / 2)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (- p * (E.card : ℝ) / 2) := by ring_nf
  have h2 : Real.exp (- p * (E.card : ℝ) / 4) * (bad.card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ) / 2) := by
    calc Real.exp (- p * (E.card : ℝ) / 4) * (bad.card : ℝ)
        ≤ ∑ f : α → β, Real.exp ((-1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := h1
      _ = (Fintype.card β : ℝ) ^ Fintype.card α * (1 + p * (Real.exp (-1 : ℝ) - 1)) ^ E.card := hmgf
      _ ≤ (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hexp_split : Real.exp (- p * (E.card : ℝ) / 2) =
      Real.exp (- p * (E.card : ℝ) / 4) * Real.exp (- p * (E.card : ℝ) / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp_split] at h2
  have hpos : 0 < Real.exp (- p * (E.card : ℝ) / 4) := Real.exp_pos _
  nlinarith

lemma chernoff_upper {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Finset α) (C : Finset β) (hβ : 0 < Fintype.card β) :
    let p : ℝ := (C.card : ℝ) / (Fintype.card β : ℝ)
    ((Finset.univ.filter (fun f : α → β =>
        3 * p * (E.card : ℝ) ≤ ((E.filter (fun a => f a ∈ C)).card : ℝ))).card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ)) := by
  intro p
  set bad := Finset.univ.filter (fun f : α → β =>
    3 * p * (E.card : ℝ) ≤ ((E.filter (fun a => f a ∈ C)).card : ℝ))
  have hp0 : 0 ≤ p := by positivity
  have h1 : Real.exp (3 * p * (E.card : ℝ)) * (bad.card : ℝ) ≤
      ∑ f : α → β, Real.exp ((1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
    calc Real.exp (3 * p * (E.card : ℝ)) * (bad.card : ℝ)
        = ∑ _f ∈ bad, Real.exp (3 * p * (E.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ f ∈ bad, Real.exp ((1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro f hf
          have hcond := (Finset.mem_filter.mp hf).2
          apply Real.exp_le_exp.mpr
          linarith
      _ ≤ ∑ f : α → β, Real.exp ((1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro f
          exact (Real.exp_pos _).le
  have hmgf := mgf_coloring E C hβ 1
  have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hbase_nn : 0 ≤ 1 + p * (Real.exp 1 - 1) := by
    have : 1 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    nlinarith
  have hbase_le : 1 + p * (Real.exp 1 - 1) ≤ Real.exp (2 * p) := by
    calc 1 + p * (Real.exp 1 - 1)
        ≤ 2 * p + 1 := by nlinarith
      _ ≤ Real.exp (2 * p) := Real.add_one_le_exp _
  have hpow : (1 + p * (Real.exp 1 - 1)) ^ E.card ≤ Real.exp (2 * p * (E.card : ℝ)) := by
    calc (1 + p * (Real.exp 1 - 1)) ^ E.card
        ≤ (Real.exp (2 * p)) ^ E.card := pow_le_pow_left₀ hbase_nn hbase_le E.card
      _ = Real.exp ((E.card : ℝ) * (2 * p)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (2 * p * (E.card : ℝ)) := by ring_nf
  have h2 : Real.exp (3 * p * (E.card : ℝ)) * (bad.card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (2 * p * (E.card : ℝ)) := by
    calc Real.exp (3 * p * (E.card : ℝ)) * (bad.card : ℝ)
        ≤ ∑ f : α → β, Real.exp ((1 : ℝ) * ((E.filter (fun a => f a ∈ C)).card : ℝ)) := h1
      _ = (Fintype.card β : ℝ) ^ Fintype.card α * (1 + p * (Real.exp 1 - 1)) ^ E.card := hmgf
      _ ≤ (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (2 * p * (E.card : ℝ)) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hexp_split : Real.exp (2 * p * (E.card : ℝ)) =
      Real.exp (3 * p * (E.card : ℝ)) * Real.exp (- p * (E.card : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp_split] at h2
  have hpos : 0 < Real.exp (3 * p * (E.card : ℝ)) := Real.exp_pos _
  nlinarith

lemma chernoff_half_lower {α : Type*} [Fintype α] [DecidableEq α]
    (E : Finset α) (c : Bool) :
    ((Finset.univ.filter (fun f : α → Bool =>
        4 * (E.filter (fun a => f a = c)).card ≤ E.card)).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card α * Real.exp (- (E.card : ℝ) / 24) := by
  set bad := Finset.univ.filter (fun f : α → Bool =>
    4 * (E.filter (fun a => f a = c)).card ≤ E.card)
  have h1 : Real.exp (- (E.card : ℝ) / 8) * (bad.card : ℝ) ≤
      ∑ f : α → Bool, Real.exp ((-1 / 2 : ℝ) * ((E.filter (fun a => f a ∈ ({c} : Finset Bool))).card : ℝ)) := by
    calc Real.exp (- (E.card : ℝ) / 8) * (bad.card : ℝ)
        = ∑ _f ∈ bad, Real.exp (- (E.card : ℝ) / 8) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ f ∈ bad, Real.exp ((-1 / 2 : ℝ) * ((E.filter (fun a => f a ∈ ({c} : Finset Bool))).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro f hf
          have hcond : (4 * (E.filter (fun a => f a = c)).card : ℝ) ≤ (E.card : ℝ) := by
            exact_mod_cast (Finset.mem_filter.mp hf).2
          have heq : E.filter (fun a => f a ∈ ({c} : Finset Bool)) = E.filter (fun a => f a = c) := by
            ext a; simp
          rw [heq]
          apply Real.exp_le_exp.mpr
          linarith
      _ ≤ ∑ f : α → Bool, Real.exp ((-1 / 2 : ℝ) * ((E.filter (fun a => f a ∈ ({c} : Finset Bool))).card : ℝ)) := by
          apply Finset.sum_le_univ_sum_of_nonneg
          intro f; exact (Real.exp_pos _).le
  have hmgf := mgf_coloring E ({c} : Finset Bool) (by decide) (-1 / 2)
  have hcardB : Fintype.card Bool = 2 := Fintype.card_bool
  rw [hcardB, Finset.card_singleton] at hmgf
  -- Show exp(-1/2) ≤ 2/3 because (3/2)^2 = 9/4 < exp 1
  have hexp_half : Real.exp (-1 / 2 : ℝ) ≤ 2 / 3 := by
    have hsq : Real.exp (-1 / 2 : ℝ) ^ 2 = Real.exp (-1 : ℝ) := by
      rw [sq, ← Real.exp_add]; norm_num
    have hlt : Real.exp (-1 : ℝ) ≤ (2 / 3 : ℝ) ^ 2 := by
      rw [Real.exp_neg]
      have he : (9 / 4 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hinv : (Real.exp 1)⁻¹ ≤ (9 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) he
      linarith
    have hpos : 0 ≤ Real.exp (-1 / 2 : ℝ) := (Real.exp_pos _).le
    nlinarith
  have hbase_nn : 0 ≤ 1 + (1 : ℝ) / 2 * (Real.exp (-1 / 2 : ℝ) - 1) := by
    have : 0 ≤ Real.exp (-1 / 2 : ℝ) := (Real.exp_pos _).le
    linarith
  have hbase_le : 1 + (1 : ℝ) / 2 * (Real.exp (-1 / 2 : ℝ) - 1) ≤ Real.exp (-1 / 6 : ℝ) := by
    calc 1 + (1 : ℝ) / 2 * (Real.exp (-1 / 2 : ℝ) - 1)
        ≤ (-1 / 6 : ℝ) + 1 := by linarith
      _ ≤ Real.exp (-1 / 6 : ℝ) := Real.add_one_le_exp _
  have hpow : (1 + (1 : ℝ) / 2 * (Real.exp (-1 / 2 : ℝ) - 1)) ^ E.card ≤
      Real.exp (- (E.card : ℝ) / 6) := by
    calc _ ≤ (Real.exp (-1 / 6 : ℝ)) ^ E.card := pow_le_pow_left₀ hbase_nn hbase_le E.card
      _ = Real.exp ((E.card : ℝ) * (-1 / 6 : ℝ)) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp (- (E.card : ℝ) / 6) := by ring_nf
  have h2 : Real.exp (- (E.card : ℝ) / 8) * (bad.card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card α * Real.exp (- (E.card : ℝ) / 6) := by
    calc Real.exp (- (E.card : ℝ) / 8) * (bad.card : ℝ)
        ≤ _ := h1
      _ = (2 : ℝ) ^ Fintype.card α * (1 + (1 : ℝ) / 2 * (Real.exp (-1 / 2 : ℝ) - 1)) ^ E.card := by
          simpa using hmgf
      _ ≤ (2 : ℝ) ^ Fintype.card α * Real.exp (- (E.card : ℝ) / 6) :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hexp_split : Real.exp (- (E.card : ℝ) / 6) =
      Real.exp (- (E.card : ℝ) / 8) * Real.exp (- (E.card : ℝ) / 24) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp_split] at h2
  have hpos : 0 < Real.exp (- (E.card : ℝ) / 8) := Real.exp_pos _
  nlinarith

end Chernoff

def subsetSumLe (h : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.filter (fun S => S.card ≤ h)).image (fun S => S.sum id)

def subsetSumModLe (b h : ℕ) (A : Finset ℕ) : Finset (ZMod b) :=
  (subsetSumLe h A).image (fun x : ℕ => (x : ZMod b))

lemma zero_mem_subsetSumLe (h : ℕ) (A : Finset ℕ) : 0 ∈ subsetSumLe h A := by
  simp only [subsetSumLe, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨∅, ⟨Finset.empty_subset _, Nat.zero_le _⟩, by simp⟩

lemma subsetSumLe_mono_left {h1 h2 : ℕ} (hh : h1 ≤ h2) (A : Finset ℕ) :
    subsetSumLe h1 A ⊆ subsetSumLe h2 A := by
  intro x hx
  simp only [subsetSumLe, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hx ⊢
  obtain ⟨S, ⟨hSA, hSc⟩, rfl⟩ := hx
  exact ⟨S, ⟨hSA, hSc.trans hh⟩, rfl⟩

lemma subsetSumLe_mono_right (h : ℕ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    subsetSumLe h A ⊆ subsetSumLe h B := by
  intro x hx
  simp only [subsetSumLe, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hx ⊢
  obtain ⟨S, ⟨hSA, hSc⟩, rfl⟩ := hx
  exact ⟨S, ⟨hSA.trans hAB, hSc⟩, rfl⟩

lemma subsetSumLe_insert_superset (h : ℕ) (A : Finset ℕ) (m : ℕ) (hmA : m ∉ A) :
    subsetSumLe h A ∪ (m +ᵥ subsetSumLe h A) ⊆ subsetSumLe (h + 1) (insert m A) := by
  apply Finset.union_subset
  · exact (subsetSumLe_mono_left (Nat.le_succ h) A).trans
      (subsetSumLe_mono_right (h + 1) (Finset.subset_insert m A))
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hx
    simp only [subsetSumLe, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset] at hy ⊢
    obtain ⟨S, ⟨hSA, hSc⟩, rfl⟩ := hy
    have hmS : m ∉ S := fun hmem => hmA (hSA hmem)
    refine ⟨insert m S, ⟨Finset.insert_subset_insert m hSA, ?_⟩, ?_⟩
    · rw [Finset.card_insert_of_notMem hmS]; omega
    · rw [Finset.sum_insert hmS, id_eq, vadd_eq_add]

-- Lemma 2.6: Double counting in finite additive abelian group
lemma card_small_growth_le {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (d : ℕ) (hd : d ≤ A.card) :
    (Finset.univ.filter (fun x : G => ((x +ᵥ A) \ A).card ≤ d)).card * (A.card - d) ≤
      A.card * A.card := by
  set Gd := Finset.univ.filter (fun x : G => ((x +ᵥ A) \ A).card ≤ d)
  set N := Fintype.card G
  have hdouble : ∑ x : G, ((x +ᵥ A) \ A).card = A.card * (N - A.card) := by
    have h1 : ∀ x : G, ((x +ᵥ A) \ A).card = ∑ a ∈ A, if x + a ∉ A then 1 else 0 := by
      intro x
      have heq : (x +ᵥ A) \ A = (A.filter (fun a => x + a ∉ A)).image (fun a => x + a) := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_vadd_finset, Finset.mem_image, Finset.mem_filter,
          vadd_eq_add]
        constructor
        · rintro ⟨⟨a, ha, rfl⟩, hnot⟩
          exact ⟨a, ⟨ha, hnot⟩, rfl⟩
        · rintro ⟨a, ⟨ha, hnot⟩, rfl⟩
          exact ⟨⟨a, ha, rfl⟩, hnot⟩
      rw [heq, Finset.card_image_of_injective _ (add_right_injective x), Finset.card_filter]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have hinner : ∀ a ∈ A, (∑ x : G, if x + a ∉ A then 1 else 0) = N - A.card := by
      intro a _
      rw [← Finset.card_filter]
      have hbij : (Finset.univ.filter (fun x : G => x + a ∉ A)).card =
          (Finset.univ \ A).card := by
        refine Finset.card_bij (fun x _ => x + a) ?_ ?_ ?_
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
        · intro x1 _ x2 _ heq
          exact add_right_cancel heq
        · intro y hy
          exact ⟨y - a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa using (Finset.mem_sdiff.mp hy).2⟩, sub_add_cancel y a⟩
      rw [hbij, Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
  have hupper : ∑ x : G, ((x +ᵥ A) \ A).card ≤ Gd.card * d + (N - Gd.card) * A.card := by
    have hsplit : ∑ x : G, ((x +ᵥ A) \ A).card =
        (∑ x ∈ Gd, ((x +ᵥ A) \ A).card) + (∑ x ∈ Finset.univ \ Gd, ((x +ᵥ A) \ A).card) := by
      rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.subset_univ Gd)]
    rw [hsplit]
    have h1 : ∑ x ∈ Gd, ((x +ᵥ A) \ A).card ≤ Gd.card * d := by
      calc ∑ x ∈ Gd, ((x +ᵥ A) \ A).card
          ≤ ∑ _x ∈ Gd, d := Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2
        _ = Gd.card * d := by rw [Finset.sum_const, smul_eq_mul]
    have h2 : ∑ x ∈ Finset.univ \ Gd, ((x +ᵥ A) \ A).card ≤ (N - Gd.card) * A.card := by
      calc ∑ x ∈ Finset.univ \ Gd, ((x +ᵥ A) \ A).card
          ≤ ∑ _x ∈ Finset.univ \ Gd, A.card := Finset.sum_le_sum fun x _ => by
            calc ((x +ᵥ A) \ A).card ≤ (x +ᵥ A).card := Finset.card_le_card Finset.sdiff_subset
              _ = A.card := Finset.card_vadd_finset x A
        _ = (Finset.univ \ Gd).card * A.card := by rw [Finset.sum_const, smul_eq_mul]
        _ = (N - Gd.card) * A.card := by
            rw [Finset.card_sdiff_of_subset (Finset.subset_univ Gd), Finset.card_univ]
    omega
  have hAN : A.card ≤ N := Finset.card_le_univ A
  have hGN : Gd.card ≤ N := Finset.card_le_univ Gd
  have hkey : A.card * (N - A.card) ≤ Gd.card * d + (N - Gd.card) * A.card := hdouble ▸ hupper
  zify [hd, hAN, hGN] at hkey ⊢
  nlinarith

-- Lemma 2.7: Subadditivity of |(x +ᵥ A) \ A|
lemma card_sdiff_vadd_add_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (x y : G) :
    (((x + y) +ᵥ A) \ A).card ≤ ((x +ᵥ A) \ A).card + ((y +ᵥ A) \ A).card := by
  have hsub : ((x + y) +ᵥ A) \ A ⊆ (((x + y) +ᵥ A) \ (y +ᵥ A)) ∪ ((y +ᵥ A) \ A) := by
    intro z hz
    obtain ⟨hz1, hznot⟩ := Finset.mem_sdiff.mp hz
    by_cases hzy : z ∈ y +ᵥ A
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzy, hznot⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz1, hzy⟩)
  have hshift : (((x + y) +ᵥ A) \ (y +ᵥ A)).card = ((x +ᵥ A) \ A).card := by
    have heq : ((x + y) +ᵥ A) \ (y +ᵥ A) = y +ᵥ ((x +ᵥ A) \ A) := by
      ext z
      simp only [Finset.mem_sdiff, Finset.mem_vadd_finset, vadd_eq_add]
      constructor
      · rintro ⟨⟨a, ha, rfl⟩, hnot⟩
        refine ⟨x + a, ⟨⟨a, ha, rfl⟩, ?_⟩, by abel⟩
        intro hmem
        exact hnot ⟨x + a, hmem, by abel⟩
      · rintro ⟨w, ⟨⟨a, ha, rfl⟩, hnot⟩, rfl⟩
        refine ⟨⟨a, ha, by abel⟩, ?_⟩
        rintro ⟨a', ha', heq'⟩
        have : a' = x + a := add_left_cancel heq'
        exact hnot (this ▸ ha')
    rw [heq, Finset.card_vadd_finset]
  calc (((x + y) +ᵥ A) \ A).card
      ≤ ((((x + y) +ᵥ A) \ (y +ᵥ A)) ∪ ((y +ᵥ A) \ A)).card := Finset.card_le_card hsub
    _ ≤ (((x + y) +ᵥ A) \ (y +ᵥ A)).card + ((y +ᵥ A) \ A).card := Finset.card_union_le _ _
    _ = ((x +ᵥ A) \ A).card + ((y +ᵥ A) \ A).card := by rw [hshift]

lemma card_sdiff_vadd_list_sum_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (L : List G) :
    ((L.sum +ᵥ A) \ A).card ≤ (L.map (fun x => ((x +ᵥ A) \ A).card)).sum := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.sum_cons, List.map_cons]
    exact (card_sdiff_vadd_add_le A x L.sum).trans (Nat.add_le_add_left ih _)

def log2P (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma lt_two_pow_log2P {n : ℕ} : n < 2 ^ log2P n := by
  dsimp [log2P]
  exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n

lemma list_sum_le_prod (ds : List ℕ) (hds : ∀ d ∈ ds, 2 ≤ d) : ds.sum ≤ ds.prod := by
  induction ds with
  | nil => simp
  | cons a rest ih =>
    have ha : 2 ≤ a := hds a (by simp)
    have hrest : ∀ d ∈ rest, 2 ≤ d := fun d hd => hds d (by simp [hd])
    cases rest with
    | nil => simp
    | cons b rest' =>
      have hb : 2 ≤ b := hrest b (by simp)
      have hprod_ge : 2 ≤ (b :: rest').prod := by
        have haux : ∀ L : List ℕ, (∀ d ∈ L, 2 ≤ d) → 1 ≤ L.prod := by
          intro L
          induction L with
          | nil => intro _; simp
          | cons x L ihL =>
            intro hL
            have hx := hL x (by simp)
            have h1 := ihL (fun y hy => hL y (by simp [hy]))
            simp only [List.prod_cons]
            nlinarith
        have h1 := haux rest' (fun y hy => hrest y (by simp [hy]))
        simp only [List.prod_cons]
        nlinarith
      have hih := ih hrest
      simp only [List.sum_cons, List.prod_cons] at hprod_ge hih ⊢
      nlinarith

lemma two_pow_length_le_prod (ds : List ℕ) (hds : ∀ d ∈ ds, 2 ≤ d) :
    2 ^ ds.length ≤ ds.prod := by
  induction ds with
  | nil => simp
  | cons a rest ih =>
    have ha : 2 ≤ a := hds a (by simp)
    have hih := ih (fun d hd => hds d (by simp [hd]))
    simp only [List.length_cons, pow_succ', List.prod_cons]
    exact Nat.mul_le_mul ha hih

def IsNiceDiv (ℓ n m : ℕ) (A : Finset ℕ) : Prop :=
  ∀ d : ℕ, 2 ≤ d → d ≤ 1024 * ℓ * n / m →
    64000 * ℓ * (log2P n) ^ 2 + 512 * ℓ * d ≤ (A.filter (fun a => ¬ d ∣ a)).card

def IsNiceDyad (ℓ n : ℕ) (A : Finset ℕ) : Prop :=
  ∀ j : ℕ, j < log2P n →
    (A.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card = 0 ∨
      256 * ℓ * log2P n ≤ (A.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card

def IsNice (ℓ n m : ℕ) (A : Finset ℕ) : Prop :=
  IsNiceDiv ℓ n m A ∧ IsNiceDyad ℓ n A

set_option maxHeartbeats 400000 in
theorem lemma_6_3 {ℓ n : ℕ} (hℓ : 1 ≤ ℓ) (hn : 2 ≤ n) (A : Finset ℕ)
    (hAsub : A ⊆ Finset.Icc 1 n)
    (hm_big : 200000 * ℓ * (log2P n) ^ 3 + 1048576 * ℓ ^ 2 * n / A.card + 100 ≤ A.card / 4) :
    ∃ d_tot : ℕ, ∃ A' : Finset ℕ,
      1 ≤ d_tot ∧ d_tot ≤ 3 * n / A.card ∧
      IsNice ℓ n A.card A' ∧
      A.card / 2 ≤ A'.card ∧
      (∀ x ∈ A', 1 ≤ x ∧ d_tot * x ∈ A) := by
  set m := A.card
  set L := log2P n
  have hm_big' : 200000 * ℓ * L ^ 3 + 1048576 * ℓ ^ 2 * n / m + 100 ≤ m / 4 := hm_big
  have hm_ge : 400 ≤ m := by
    have h100 : 100 ≤ m / 4 := le_trans (Nat.le_add_left 100 _) hm_big'
    omega
  have hL_ge : 1 ≤ L := by dsimp [L, log2P]; omega
  have hstep : ∀ (meas : ℕ) (d_tot : ℕ) (A_cur : Finset ℕ) (ds : List ℕ) (dyad_steps : ℕ),
      2 * (n / d_tot) + (if IsNiceDyad ℓ n A_cur then 0 else 1) ≤ meas →
      d_tot = ds.prod →
      (∀ d ∈ ds, 2 ≤ d) →
      (∀ x ∈ A_cur, 1 ≤ x ∧ d_tot * x ∈ A) →
      m / 2 ≤ A_cur.card →
      dyad_steps ≤ ds.length + (if IsNiceDyad ℓ n A_cur then 1 else 0) →
      m ≤ A_cur.card + ds.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds.sum +
            dyad_steps * (256 * ℓ * L ^ 2) →
      ∃ d_fin : ℕ, ∃ A' : Finset ℕ,
        1 ≤ d_fin ∧ d_fin ≤ 3 * n / m ∧
        IsNice ℓ n m A' ∧
        m / 2 ≤ A'.card ∧
        (∀ x ∈ A', 1 ≤ x ∧ d_fin * x ∈ A) := by
    intro meas
    induction meas using Nat.strongRecOn with
    | ind meas ih =>
      intro d_tot A_cur ds dyad_steps hmeas hd_eq hds hAcur hcard_cur hdyad_cnt hloss
      have hd_pos : 1 ≤ d_tot := by
        rw [hd_eq]
        have h1 := two_pow_length_le_prod ds hds
        have h2 : 1 ≤ 2 ^ ds.length := Nat.one_le_pow _ _ (by decide)
        omega
      have hAcur_le : ∀ x ∈ A_cur, x ≤ n / d_tot := by
        intro x hx
        have hmem := hAsub (hAcur x hx).2
        have hle : d_tot * x ≤ n := (Finset.mem_Icc.mp hmem).2
        exact (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; exact hle)
      have hcard_le_div : A_cur.card ≤ n / d_tot := by
        have hsub : A_cur ⊆ Finset.Icc 1 (n / d_tot) := fun x hx =>
          Finset.mem_Icc.mpr ⟨(hAcur x hx).1, hAcur_le x hx⟩
        simpa using Finset.card_le_card hsub
      have hd_le_3 : d_tot ≤ 3 * n / m := by
        have h1 : m / 2 ≤ n / d_tot := hcard_cur.trans hcard_le_div
        have h2 : d_tot * (m / 2) ≤ n := by
          have := (Nat.le_div_iff_mul_le hd_pos).mp h1
          rwa [mul_comm] at this
        have h3 : m ≤ 3 * (m / 2) := by omega
        have h4 : d_tot * m ≤ 3 * n := by
          calc d_tot * m ≤ d_tot * (3 * (m / 2)) := Nat.mul_le_mul_left d_tot h3
            _ = 3 * (d_tot * (m / 2)) := by ring
            _ ≤ 3 * n := Nat.mul_le_mul_left 3 h2
        exact (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr h4
      -- Check if IsNiceDiv holds
      by_cases hdiv : IsNiceDiv ℓ n m A_cur
      · -- Check if IsNiceDyad holds
        by_cases hdyad : IsNiceDyad ℓ n A_cur
        · exact ⟨d_tot, A_cur, hd_pos, hd_le_3, ⟨hdiv, hdyad⟩, hcard_cur, hAcur⟩
        · -- Dyadic cleanup step
          let A_next := A_cur.filter (fun x =>
            ∀ j < L, 2 ^ j ≤ x → x < 2 ^ (j + 1) →
              256 * ℓ * L ≤ (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card)
          have hAnext_sub : A_next ⊆ A_cur := Finset.filter_subset _ _
          have hAnext_prop : ∀ x ∈ A_next, 1 ≤ x ∧ d_tot * x ∈ A := fun x hx => hAcur x (hAnext_sub hx)
          -- Every element of A_cur \ A_next belongs to some sparse dyadic interval j < L
          have hdiff_sub : A_cur \ A_next ⊆
              (Finset.range L).biUnion (fun j =>
                if (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card < 256 * ℓ * L then
                  A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
                else ∅) := by
            intro x hx
            obtain ⟨hxA, hxnot⟩ := Finset.mem_sdiff.mp hx
            have hfail : ¬ (∀ j < L, 2 ^ j ≤ x → x < 2 ^ (j + 1) →
                256 * ℓ * L ≤ (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card) := by
              intro h; exact hxnot (Finset.mem_filter.mpr ⟨hxA, h⟩)
            push Not at hfail
            obtain ⟨j, hjL, hj1, hj2, hjcard⟩ := hfail
            refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjL, ?_⟩
            rw [if_pos hjcard]
            exact Finset.mem_filter.mpr ⟨hxA, hj1, hj2⟩
          have hdiff_card : (A_cur \ A_next).card ≤ 256 * ℓ * L ^ 2 := by
            calc (A_cur \ A_next).card
                ≤ ((Finset.range L).biUnion (fun j =>
                    if (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card < 256 * ℓ * L then
                      A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
                    else ∅)).card := Finset.card_le_card hdiff_sub
              _ ≤ ∑ j ∈ Finset.range L,
                    (if (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card < 256 * ℓ * L then
                      A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
                    else ∅).card := Finset.card_biUnion_le
              _ ≤ ∑ _j ∈ Finset.range L, (256 * ℓ * L) := by
                  apply Finset.sum_le_sum
                  intro j _
                  split_ifs with hlt
                  · exact Nat.le_of_lt hlt
                  · simp
              _ = L * (256 * ℓ * L) := by simp [Finset.sum_const, Finset.card_range]
              _ = 256 * ℓ * L ^ 2 := by ring
          have hAnext_dyad : IsNiceDyad ℓ n A_next := by
            intro j hjL
            by_cases hbig : 256 * ℓ * L ≤ (A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card
            · right
              have hsub : A_cur.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) ⊆
                  A_next.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) := by
                intro x hx
                obtain ⟨hxA, hx1, hx2⟩ := Finset.mem_filter.mp hx
                refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxA, ?_⟩, hx1, hx2⟩
                intro j' _ hj'1 hj'2
                have hjeq : j' = j := by
                  by_contra hne
                  rcases lt_or_gt_of_ne hne with hlt | hgt
                  · have : 2 ^ (j' + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
                    omega
                  · have : 2 ^ (j + 1) ≤ 2 ^ j' := Nat.pow_le_pow_right (by decide) (by omega)
                    omega
                exact hjeq ▸ hbig
              exact hbig.trans (Finset.card_le_card hsub)
            · left
              rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
              intro x hx
              obtain ⟨hxN, hx1, hx2⟩ := Finset.mem_filter.mp hx
              exact hbig ((Finset.mem_filter.mp hxN).2 j hjL hx1 hx2)
          have hsd := Finset.card_sdiff_add_card_eq_card hAnext_sub
          have hds_len : ds.length ≤ L := by
            have h1 : 2 ^ ds.length ≤ d_tot := hd_eq ▸ two_pow_length_le_prod ds hds
            have h2 : d_tot ≤ n := by
              have h1' : 1 ≤ A_cur.card := by omega
              obtain ⟨x, hx⟩ := Finset.card_pos.mp h1'
              have hx1 := (hAcur x hx).1
              have hle := (Finset.mem_Icc.mp (hAsub (hAcur x hx).2)).2
              nlinarith
            have h3 : 2 ^ ds.length < 2 ^ L := lt_of_le_of_lt (h1.trans h2) lt_two_pow_log2P
            exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h3)
          have hds_sum : ds.sum ≤ 3 * n / m := by
            exact (list_sum_le_prod ds hds).trans (hd_eq ▸ hd_le_3)
          have hdyad_cnt' : dyad_steps + 1 ≤ ds.length + (if IsNiceDyad ℓ n A_next then 1 else 0) := by
            rw [if_neg hdyad] at hdyad_cnt
            rw [if_pos hAnext_dyad]
            omega
          have hloss' : m ≤ A_next.card + ds.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds.sum +
              (dyad_steps + 1) * (256 * ℓ * L ^ 2) := by
            calc m ≤ A_cur.card + ds.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds.sum +
                    dyad_steps * (256 * ℓ * L ^ 2) := hloss
              _ = A_next.card + (A_cur \ A_next).card + ds.length * (64000 * ℓ * L ^ 2) +
                    512 * ℓ * ds.sum + dyad_steps * (256 * ℓ * L ^ 2) := by omega
              _ ≤ A_next.card + 256 * ℓ * L ^ 2 + ds.length * (64000 * ℓ * L ^ 2) +
                    512 * ℓ * ds.sum + dyad_steps * (256 * ℓ * L ^ 2) := by omega
              _ = A_next.card + ds.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds.sum +
                    (dyad_steps + 1) * (256 * ℓ * L ^ 2) := by ring
          have hcard_next : m / 2 ≤ A_next.card := by
            have h1 : ds.length * (64000 * ℓ * L ^ 2) ≤ 64000 * ℓ * L ^ 3 := by
              calc ds.length * (64000 * ℓ * L ^ 2) ≤ L * (64000 * ℓ * L ^ 2) :=
                    Nat.mul_le_mul_right _ hds_len
                _ = 64000 * ℓ * L ^ 3 := by ring
            have h2 : (dyad_steps + 1) * (256 * ℓ * L ^ 2) ≤ 512 * ℓ * L ^ 3 := by
              have hdy : dyad_steps + 1 ≤ 2 * L := by
                rw [if_pos hAnext_dyad] at hdyad_cnt'
                omega
              calc (dyad_steps + 1) * (256 * ℓ * L ^ 2) ≤ (2 * L) * (256 * ℓ * L ^ 2) :=
                    Nat.mul_le_mul_right _ hdy
                _ = 512 * ℓ * L ^ 3 := by ring
            have h3 : 512 * ℓ * ds.sum ≤ 1048576 * ℓ ^ 2 * n / m := by
              have ha : 512 * ℓ * ds.sum ≤ 512 * ℓ * (3 * n / m) := Nat.mul_le_mul_left _ hds_sum
              have hb : 512 * ℓ * (3 * n / m) ≤ (512 * ℓ * (3 * n)) / m := Nat.mul_div_le_mul_div_assoc _ _ _
              have hc : 512 * ℓ * (3 * n) ≤ 1048576 * ℓ ^ 2 * n := by
                have hℓ2 : ℓ ≤ ℓ ^ 2 := by nlinarith
                calc 512 * ℓ * (3 * n) = 1536 * (ℓ * n) := by ring
                  _ ≤ 1048576 * (ℓ ^ 2 * n) := by nlinarith
                  _ = 1048576 * ℓ ^ 2 * n := by ring
              exact ha.trans (hb.trans (Nat.div_le_div_right hc))
            have hL3 : 64000 * ℓ * L ^ 3 + 512 * ℓ * L ^ 3 ≤ 200000 * ℓ * L ^ 3 := by
              calc 64000 * ℓ * L ^ 3 + 512 * ℓ * L ^ 3 = 64512 * (ℓ * L ^ 3) := by ring
                _ ≤ 200000 * (ℓ * L ^ 3) := Nat.mul_le_mul_right _ (by decide)
                _ = 200000 * ℓ * L ^ 3 := by ring
            have hsum_loss : ds.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds.sum +
                (dyad_steps + 1) * (256 * ℓ * L ^ 2) ≤ m / 4 := by linarith
            omega
          have hmeas_lt : 2 * (n / d_tot) + (if IsNiceDyad ℓ n A_next then 0 else 1) < meas := by
            rw [if_neg hdyad] at hmeas
            rw [if_pos hAnext_dyad]
            omega
          exact ih _ hmeas_lt d_tot A_next ds (dyad_steps + 1) le_rfl hd_eq hds hAnext_prop
            hcard_next hdyad_cnt' hloss'
      · -- Division step: some d ∈ [2, 1024 * ℓ * n / m] fails IsNiceDiv
        unfold IsNiceDiv at hdiv
        push Not at hdiv
        obtain ⟨d, hd2, hd_ub, hbad_lt⟩ := hdiv
        set A_div := A_cur.filter (fun a => d ∣ a)
        set A_next := A_div.image (fun a => a / d)
        have hA_next_card : A_next.card = A_div.card := by
          refine Finset.card_image_of_injOn ?_
          intro x hx y hy heq
          dsimp at heq
          have hdx := (Finset.mem_filter.mp hx).2
          have hdy := (Finset.mem_filter.mp hy).2
          calc x = d * (x / d) := (Nat.mul_div_cancel' hdx).symm
            _ = d * (y / d) := by rw [heq]
            _ = y := Nat.mul_div_cancel' hdy
        have hsplit_card : A_div.card + (A_cur.filter (fun a => ¬ d ∣ a)).card = A_cur.card :=
          Finset.card_filter_add_card_filter_not _
        have hAnext_prop : ∀ x ∈ A_next, 1 ≤ x ∧ (d_tot * d) * x ∈ A := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          obtain ⟨hyA, hdy⟩ := Finset.mem_filter.mp hy
          have hy1 := (hAcur y hyA).1
          have hmul_eq : d * (y / d) = y := Nat.mul_div_cancel' hdy
          have hx1 : 1 ≤ y / d := by
            by_contra h0
            have hz : y / d = 0 := Nat.eq_zero_of_not_pos h0
            rw [hz, mul_zero] at hmul_eq
            linarith
          refine ⟨hx1, ?_⟩
          rw [mul_assoc, hmul_eq]
          exact (hAcur y hyA).2
        -- First bound A_next.card ≥ m / 4 from single-step loss
        have hbad_lt' : (A_cur.filter (fun a => ¬ d ∣ a)).card < 64000 * ℓ * L ^ 2 + 512 * ℓ * d := hbad_lt
        have hstep_loss_le : 64000 * ℓ * L ^ 2 + 512 * ℓ * d ≤ m / 4 := by
          have h1 : 64000 * ℓ * L ^ 2 ≤ 200000 * ℓ * L ^ 3 := by
            calc 64000 * ℓ * L ^ 2 = 64000 * ℓ * L ^ 2 * 1 := by ring
              _ ≤ 64000 * ℓ * L ^ 2 * L := Nat.mul_le_mul_left _ hL_ge
              _ = 64000 * (ℓ * L ^ 3) := by ring
              _ ≤ 200000 * (ℓ * L ^ 3) := Nat.mul_le_mul_right _ (by decide)
              _ = 200000 * ℓ * L ^ 3 := by ring
          have h2 : 512 * ℓ * d ≤ 1048576 * ℓ ^ 2 * n / m := by
            have ha : 512 * ℓ * d ≤ 512 * ℓ * (1024 * ℓ * n / m) := Nat.mul_le_mul_left _ hd_ub
            have hb : 512 * ℓ * (1024 * ℓ * n / m) ≤ (512 * ℓ * (1024 * ℓ * n)) / m :=
              Nat.mul_div_le_mul_div_assoc _ _ _
            have hc : 512 * ℓ * (1024 * ℓ * n) ≤ 1048576 * ℓ ^ 2 * n := by
              calc 512 * ℓ * (1024 * ℓ * n) = 524288 * (ℓ ^ 2 * n) := by ring
                _ ≤ 1048576 * (ℓ ^ 2 * n) := Nat.mul_le_mul_right _ (by decide)
                _ = 1048576 * ℓ ^ 2 * n := by ring
            exact ha.trans (hb.trans (Nat.div_le_div_right hc))
          linarith
        have hcard_ge_quarter : m / 4 ≤ A_next.card := by omega
        -- Therefore d_tot * d ≤ 5 * n / m and d_tot * d ≤ n
        have hdd_pos : 1 ≤ d_tot * d := Nat.mul_pos hd_pos (by omega)
        have hAnext_le_div : A_next.card ≤ n / (d_tot * d) := by
          have hsub : A_next ⊆ Finset.Icc 1 (n / (d_tot * d)) := fun x hx =>
            Finset.mem_Icc.mpr ⟨(hAnext_prop x hx).1,
              (Nat.le_div_iff_mul_le hdd_pos).mpr (by
                rw [mul_comm]; exact (Finset.mem_Icc.mp (hAsub (hAnext_prop x hx).2)).2)⟩
          simpa using Finset.card_le_card hsub
        have hdd_le_5 : d_tot * d ≤ 5 * n / m := by
          have h1 : m / 4 ≤ n / (d_tot * d) := hcard_ge_quarter.trans hAnext_le_div
          have h2 : (d_tot * d) * (m / 4) ≤ n := by
            have := (Nat.le_div_iff_mul_le hdd_pos).mp h1
            rwa [mul_comm] at this
          have h3 : m ≤ 5 * (m / 4) := by omega
          have h4 : (d_tot * d) * m ≤ 5 * n := by
            calc (d_tot * d) * m ≤ (d_tot * d) * (5 * (m / 4)) := Nat.mul_le_mul_left _ h3
              _ = 5 * ((d_tot * d) * (m / 4)) := by ring
              _ ≤ 5 * n := Nat.mul_le_mul_left 5 h2
          exact (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr h4
        have hdd_le_n : d_tot * d ≤ n := by
          have h1 : 1 ≤ A_next.card := by omega
          obtain ⟨x, hx⟩ := Finset.card_pos.mp h1
          have hx1 := (hAnext_prop x hx).1
          have hle := (Finset.mem_Icc.mp (hAsub (hAnext_prop x hx).2)).2
          calc d_tot * d = (d_tot * d) * 1 := by ring
            _ ≤ (d_tot * d) * x := Nat.mul_le_mul_left _ hx1
            _ ≤ n := hle
        set ds' := d :: ds
        have hds'_prod : d_tot * d = ds'.prod := by simp [ds', hd_eq, mul_comm]
        have hds'_ge2 : ∀ x ∈ ds', 2 ≤ x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hxds
          · exact hd2
          · exact hds x hxds
        have hds'_len : ds'.length ≤ L := by
          have h1 : 2 ^ ds'.length ≤ d_tot * d := hds'_prod ▸ two_pow_length_le_prod ds' hds'_ge2
          have h2 : 2 ^ ds'.length < 2 ^ L := lt_of_le_of_lt (h1.trans hdd_le_n) lt_two_pow_log2P
          exact Nat.le_of_lt ((Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2)
        have hds'_sum : ds'.sum ≤ 5 * n / m :=
          (list_sum_le_prod ds' hds'_ge2).trans (hds'_prod ▸ hdd_le_5)
        have hdyad_cnt' : dyad_steps ≤ ds'.length + (if IsNiceDyad ℓ n A_next then 1 else 0) := by
          simp only [ds', List.length_cons]
          split_ifs at hdyad_cnt ⊢ <;> omega
        have hloss' : m ≤ A_next.card + ds'.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds'.sum +
            dyad_steps * (256 * ℓ * L ^ 2) := by
          simp only [ds', List.length_cons, List.sum_cons]
          have hcur_le : A_cur.card ≤ A_next.card + (64000 * ℓ * L ^ 2 + 512 * ℓ * d) := by omega
          have h1 : (ds.length + 1) * (64000 * ℓ * L ^ 2) =
              ds.length * (64000 * ℓ * L ^ 2) + 64000 * ℓ * L ^ 2 := by ring
          have h2 : 512 * ℓ * (d + ds.sum) = 512 * ℓ * d + 512 * ℓ * ds.sum := by ring
          omega
        have hcard_next : m / 2 ≤ A_next.card := by
          have h1 : ds'.length * (64000 * ℓ * L ^ 2) ≤ 64000 * ℓ * L ^ 3 := by
            calc ds'.length * (64000 * ℓ * L ^ 2) ≤ L * (64000 * ℓ * L ^ 2) :=
                  Nat.mul_le_mul_right _ hds'_len
              _ = 64000 * ℓ * L ^ 3 := by ring
          have h2 : dyad_steps * (256 * ℓ * L ^ 2) ≤ 512 * ℓ * L ^ 3 := by
            have hdy : dyad_steps ≤ 2 * L := by
              split_ifs at hdyad_cnt' <;> omega
            calc dyad_steps * (256 * ℓ * L ^ 2) ≤ (2 * L) * (256 * ℓ * L ^ 2) :=
                  Nat.mul_le_mul_right _ hdy
              _ = 512 * ℓ * L ^ 3 := by ring
          have h3 : 512 * ℓ * ds'.sum ≤ 1048576 * ℓ ^ 2 * n / m := by
            have ha : 512 * ℓ * ds'.sum ≤ 512 * ℓ * (5 * n / m) := Nat.mul_le_mul_left _ hds'_sum
            have hb : 512 * ℓ * (5 * n / m) ≤ (512 * ℓ * (5 * n)) / m :=
              Nat.mul_div_le_mul_div_assoc _ _ _
            have hc : 512 * ℓ * (5 * n) ≤ 1048576 * ℓ ^ 2 * n := by
              have hℓ2 : ℓ ≤ ℓ ^ 2 := by
                calc ℓ = ℓ * 1 := (mul_one ℓ).symm
                  _ ≤ ℓ * ℓ := Nat.mul_le_mul_left ℓ hℓ
                  _ = ℓ ^ 2 := (sq ℓ).symm
              calc 512 * ℓ * (5 * n) = 2560 * (ℓ * n) := by ring
                _ ≤ 1048576 * (ℓ ^ 2 * n) := Nat.mul_le_mul (by decide) (Nat.mul_le_mul_right n hℓ2)
                _ = 1048576 * ℓ ^ 2 * n := by ring
            exact ha.trans (hb.trans (Nat.div_le_div_right hc))
          have hL3 : 64000 * ℓ * L ^ 3 + 512 * ℓ * L ^ 3 ≤ 200000 * ℓ * L ^ 3 := by
            calc 64000 * ℓ * L ^ 3 + 512 * ℓ * L ^ 3 = 64512 * (ℓ * L ^ 3) := by ring
              _ ≤ 200000 * (ℓ * L ^ 3) := Nat.mul_le_mul_right _ (by decide)
              _ = 200000 * ℓ * L ^ 3 := by ring
          have hsum_loss : ds'.length * (64000 * ℓ * L ^ 2) + 512 * ℓ * ds'.sum +
              dyad_steps * (256 * ℓ * L ^ 2) ≤ m / 4 := by linarith
          omega
        have hdiv_lt : n / (d_tot * d) < n / d_tot := by
          rw [← Nat.div_div_eq_div_mul]
          have hpos_div : 0 < n / d_tot := by
            have h1 : 1 ≤ n / (d_tot * d) := by omega
            have h2 : n / (d_tot * d) ≤ n / d_tot := by
              rw [← Nat.div_div_eq_div_mul]; exact Nat.div_le_self _ _
            omega
          exact Nat.div_lt_self hpos_div (by omega : 1 < d)
        have hmeas_lt : 2 * (n / (d_tot * d)) + (if IsNiceDyad ℓ n A_next then 0 else 1) < meas := by
          split_ifs at hmeas ⊢ <;> omega
        exact ih _ hmeas_lt (d_tot * d) A_next ds' dyad_steps le_rfl hds'_prod hds'_ge2
          hAnext_prop hcard_next hdyad_cnt' hloss'
  exact hstep (2 * n + 1) 1 A [] 0 (by split_ifs <;> simp) rfl (by simp)
    (fun x hx => ⟨(Finset.mem_Icc.mp (hAsub hx)).1, by simpa using hx⟩)
    (Nat.div_le_self m 2) (by split_ifs <;> omega) (by simp [m])

lemma log2P_mono {a b : ℕ} (hab : a ≤ b) : log2P a ≤ log2P b :=
  Nat.add_le_add_right (Nat.log_mono_right hab) 1

lemma zero_mem_subsetSumMod (d : ℕ) (A : Finset ℕ) : (0 : ZMod d) ∈ subsetSumMod d A := by
  simp only [subsetSumMod, Finset.mem_image, Finset.mem_powerset]
  exact ⟨∅, Finset.empty_subset _, by simp⟩

lemma subsetSumMod_mono (d : ℕ) {A B : Finset ℕ} (hAB : A ⊆ B) :
    subsetSumMod d A ⊆ subsetSumMod d B := by
  intro x hx
  simp only [subsetSumMod, Finset.mem_image, Finset.mem_powerset] at hx ⊢
  obtain ⟨S, hSA, rfl⟩ := hx
  exact ⟨S, hSA.trans hAB, rfl⟩

lemma subsetSumMod_insert_eq (d a : ℕ) (A : Finset ℕ) (ha : a ∉ A) :
    subsetSumMod d (insert a A) = subsetSumMod d A ∪ ((a : ZMod d) +ᵥ subsetSumMod d A) := by
  ext x
  simp only [subsetSumMod, Finset.mem_union, Finset.mem_vadd_finset, Finset.mem_image,
    Finset.mem_powerset, vadd_eq_add]
  constructor
  · rintro ⟨S, hS, rfl⟩
    by_cases haS : a ∈ S
    · right
      refine ⟨(((S.erase a).sum id : ℕ) : ZMod d),
        ⟨S.erase a, fun y hy => by
          have hyS := hS (Finset.mem_of_mem_erase hy)
          exact (Finset.mem_insert.mp hyS).resolve_left (Finset.ne_of_mem_erase hy), rfl⟩, ?_⟩
      rw [← Nat.cast_add]; congr 1; exact Finset.add_sum_erase S id haS
    · left
      exact ⟨S, fun y hy => (Finset.mem_insert.mp (hS hy)).resolve_left (fun h => haS (h ▸ hy)), rfl⟩
  · rintro (⟨S, hS, rfl⟩ | ⟨_, ⟨S, hS, rfl⟩, rfl⟩)
    · exact ⟨S, hS.trans (Finset.subset_insert a _), rfl⟩
    · have haS : a ∉ S := fun h => ha (hS h)
      refine ⟨insert a S, Finset.insert_subset_insert a hS, ?_⟩
      rw [Finset.sum_insert haS, id_eq, Nat.cast_add]

lemma sum_mem_subgroup_of_forall {b : ℕ} (H : AddSubgroup (ZMod b)) (T : Finset ℕ)
    (hT : ∀ a ∈ T, (a : ZMod b) ∈ H) : ((T.sum id : ℕ) : ZMod b) ∈ H := by
  induction T using Finset.induction_on with
  | empty => simpa using H.zero_mem
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, id_eq, Nat.cast_add]
    exact H.add_mem (hT a (Finset.mem_insert_self a S))
      (ih (fun x hx => hT x (Finset.mem_insert_of_mem hx)))

-- Lemma 5.11: Every nonempty coset slice of S_0 + S(U) has size ≥ |S(U ∩ H)|
lemma card_coset_ge_sub {b : ℕ} (A_init U : Finset ℕ) (H : AddSubgroup (ZMod b)) (u : ZMod b) :
    let S0 := A_init.image (fun x : ℕ => (x : ZMod b))
    let Sfull := S0 + subsetSumMod b U
    let Su := Sfull.filter (fun x => x - u ∈ H)
    Su.Nonempty → (subsetSumMod b (U.filter (fun a : ℕ => (a : ZMod b) ∈ H))).card ≤ Su.card := by
  intro S0 Sfull Su hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨hxS, hxuH⟩ := Finset.mem_filter.mp hx
  obtain ⟨s0z, hs0z, tz, htz, rfl⟩ := Finset.mem_add.mp hxS
  obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs0z
  obtain ⟨T, hTU, rfl⟩ := Finset.mem_image.mp htz
  have hTU' : T ⊆ U := Finset.mem_powerset.mp hTU
  set UH := U.filter (fun a : ℕ => (a : ZMod b) ∈ H)
  set Tin := T.filter (fun a : ℕ => (a : ZMod b) ∈ H)
  set Tout := T.filter (fun a : ℕ => (a : ZMod b) ∉ H)
  have hTdisj : Disjoint Tin Tout := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    exact (Finset.mem_filter.mp ha2).2 (Finset.mem_filter.mp ha1).2
  have hTunion : Tin ∪ Tout = T := Finset.filter_union_filter_not_eq _ T
  have hTsum : T.sum id = Tin.sum id + Tout.sum id := by
    rw [← hTunion, Finset.sum_union hTdisj]
  have hTinH : ((Tin.sum id : ℕ) : ZMod b) ∈ H :=
    sum_mem_subgroup_of_forall H Tin (fun a ha => (Finset.mem_filter.mp ha).2)
  set base : ZMod b := (s0 : ZMod b) + ((Tout.sum id : ℕ) : ZMod b)
  have hbaseH : base - u ∈ H := by
    have heq : base - u = ((s0 : ZMod b) + ((T.sum id : ℕ) : ZMod b) - u) - ((Tin.sum id : ℕ) : ZMod b) := by
      dsimp [base]; rw [hTsum, Nat.cast_add]; abel
    rw [heq]
    exact H.sub_mem hxuH hTinH
  have hsub : base +ᵥ subsetSumMod b UH ⊆ Su := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_vadd_finset.mp hy
    obtain ⟨S, hSUH, rfl⟩ := Finset.mem_image.mp hz
    have hSUH' : S ⊆ UH := Finset.mem_powerset.mp hSUH
    have hSH : ((S.sum id : ℕ) : ZMod b) ∈ H :=
      sum_mem_subgroup_of_forall H S (fun a ha => (Finset.mem_filter.mp (hSUH' ha)).2)
    have hSTdisj : Disjoint S Tout := by
      rw [Finset.disjoint_left]
      intro a haS haTout
      exact (Finset.mem_filter.mp haTout).2 (Finset.mem_filter.mp (hSUH' haS)).2
    have hSTsub : S ∪ Tout ⊆ U :=
      Finset.union_subset (hSUH'.trans (Finset.filter_subset _ _))
        ((Finset.filter_subset _ _).trans hTU')
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · have heq : base +ᵥ ((S.sum id : ℕ) : ZMod b) =
          (s0 : ZMod b) + (((S ∪ Tout).sum id : ℕ) : ZMod b) := by
        have hsum : (S ∪ Tout).sum id = S.sum id + Tout.sum id := Finset.sum_union hSTdisj
        rw [vadd_eq_add, hsum, Nat.cast_add]; dsimp [base]; abel
      rw [heq]
      exact Finset.mem_add.mpr ⟨(s0 : ZMod b), Finset.mem_image_of_mem _ hs0,
        (((S ∪ Tout).sum id : ℕ) : ZMod b),
        Finset.mem_image.mpr ⟨S ∪ Tout, Finset.mem_powerset.mpr hSTsub, rfl⟩, rfl⟩
    · have heq : (base +ᵥ ((S.sum id : ℕ) : ZMod b)) - u = (base - u) + ((S.sum id : ℕ) : ZMod b) := by
        rw [vadd_eq_add]; abel
      rw [heq]
      exact H.add_mem hbaseH hSH
  calc (subsetSumMod b UH).card = (base +ᵥ subsetSumMod b UH).card := (Finset.card_vadd_finset base _).symm
    _ ≤ Su.card := Finset.card_le_card hsub

-- Helper: mem of finsetListSum (List.replicate k P) can be represented as sum of a list of length k in P
lemma exists_list_of_mem_finsetListSum_replicate {G : Type} [AddCommMonoid G] [DecidableEq G]
    {P : Finset G} {k : ℕ} {x : G} (hx : x ∈ finsetListSum (List.replicate k P)) :
    ∃ L : List G, L.length = k ∧ (∀ a ∈ L, a ∈ P) ∧ L.sum = x := by
  induction k generalizing x with
  | zero =>
    simp only [List.replicate_zero, finsetListSum, Finset.mem_singleton] at hx
    exact ⟨[], rfl, by simp, hx.symm⟩
  | succ k ih =>
    rw [List.replicate_succ, finsetListSum] at hx
    obtain ⟨a, ha, y, hy, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨L, hlen, hLP, hsum⟩ := ih hy
    refine ⟨a :: L, by simp [hlen], ?_, by simp [hsum]⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hzL
    · exact ha
    · exact hLP z hzL

-- Helper: growth step count bound (if f is monotone, f 0 ≥ 1, f T ≤ b < 2^L, and 2*f(t+1) ≥ 3*f(t) on S ⊆ range T, then S.card < 2*L)
lemma card_growth_steps_lt {T b L : ℕ} (hb : b < 2 ^ L)
    (f : ℕ → ℕ) (hf0 : 1 ≤ f 0) (hfT : f T ≤ b)
    (hmono : ∀ t1 t2, t1 ≤ t2 → f t1 ≤ f t2)
    (S : Finset ℕ) (hST : S ⊆ Finset.range T)
    (hstep : ∀ t ∈ S, 3 * f t ≤ 2 * f (t + 1)) :
    S.card < 2 * L := by
  have hpow : ∀ (M : Finset ℕ) (N : ℕ), M ⊆ Finset.range N →
      (∀ t ∈ M, 3 * f t ≤ 2 * f (t + 1)) →
      3 ^ M.card ≤ 2 ^ M.card * f N := by
    intro M
    induction M using Finset.strongInduction with
    | H M ih =>
      intro N hMN hMstep
      by_cases hMe : M = ∅
      · subst hMe
        simp only [Finset.card_empty, pow_zero, one_mul]
        exact hf0.trans (hmono 0 N (Nat.zero_le N))
      · have hMne : M.Nonempty := Finset.nonempty_iff_ne_empty.mpr hMe
        set m := M.max' hMne
        have hmM : m ∈ M := Finset.max'_mem M hMne
        have hmN : m < N := Finset.mem_range.mp (hMN hmM)
        set M' := M.erase m
        have hM'ss : M' ⊂ M := Finset.erase_ssubset hmM
        have hM'sub : M' ⊆ Finset.range m := by
          intro x hx
          have hxM : x ∈ M := Finset.mem_of_mem_erase hx
          have hxne : x ≠ m := Finset.ne_of_mem_erase hx
          have hxle : x ≤ m := Finset.le_max' M x hxM
          exact Finset.mem_range.mpr (lt_of_le_of_ne hxle hxne)
        have hih := ih M' hM'ss m hM'sub (fun t ht => hMstep t (Finset.mem_of_mem_erase ht))
        have hcard : M.card = M'.card + 1 := (Finset.card_erase_add_one hmM).symm
        have hfm : 3 * f m ≤ 2 * f (m + 1) := hMstep m hmM
        have hfmN : f (m + 1) ≤ f N := hmono (m + 1) N hmN
        rw [hcard, pow_succ, pow_succ]
        calc 3 ^ M'.card * 3 ≤ (2 ^ M'.card * f m) * 3 := Nat.mul_le_mul_right 3 hih
          _ = 2 ^ M'.card * (3 * f m) := by ring
          _ ≤ 2 ^ M'.card * (2 * f (m + 1)) := Nat.mul_le_mul_left _ hfm
          _ ≤ 2 ^ M'.card * (2 * f N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 hfmN)
          _ = 2 ^ M'.card * 2 * f N := by ring
  have h1 : 3 ^ S.card ≤ 2 ^ S.card * f T := hpow S T hST hstep
  by_contra hge
  push Not at hge
  have h3pow : 2 ^ S.card * 2 ^ L < 3 ^ S.card := by
    have h1' : 2 ^ L * 2 ^ (2 * L) < 3 ^ (2 * L) := by
      have h89 : 8 ^ L < 9 ^ L := by
        have hLpos : 0 < L := by
          by_contra h0
          have hL0 : L = 0 := by omega
          rw [hL0] at hb
          have : f T = 0 := by omega
          have := hf0.trans (hmono 0 T (Nat.zero_le T))
          omega
        exact Nat.pow_lt_pow_left (by decide : 8 < 9) (by omega)
      have h8 : 8 ^ L = 2 ^ L * 2 ^ (2 * L) := by
        calc 8 ^ L = (2 ^ 3) ^ L := by norm_num
          _ = 2 ^ (3 * L) := (pow_mul 2 3 L).symm
          _ = 2 ^ (L + 2 * L) := by congr 1; ring
          _ = 2 ^ L * 2 ^ (2 * L) := pow_add 2 L (2 * L)
      have h9 : 9 ^ L = 3 ^ (2 * L) := by
        calc 9 ^ L = (3 ^ 2) ^ L := by norm_num
          _ = 3 ^ (2 * L) := (pow_mul 3 2 L).symm
      rw [← h8, ← h9]
      exact h89
    have hdiff : 2 ^ (S.card - 2 * L) ≤ 3 ^ (S.card - 2 * L) :=
      Nat.pow_le_pow_left (by decide : 2 ≤ 3) _
    have h2split : 2 ^ S.card = 2 ^ (2 * L) * 2 ^ (S.card - 2 * L) := by
      rw [← pow_add, Nat.add_sub_of_le hge]
    have h3split : 3 ^ S.card = 3 ^ (2 * L) * 3 ^ (S.card - 2 * L) := by
      rw [← pow_add, Nat.add_sub_of_le hge]
    rw [h2split, h3split]
    have hpos : 0 < 2 ^ (S.card - 2 * L) := Nat.pos_of_ne_zero (by positivity)
    calc 2 ^ (2 * L) * 2 ^ (S.card - 2 * L) * 2 ^ L
        = (2 ^ L * 2 ^ (2 * L)) * 2 ^ (S.card - 2 * L) := by ring
      _ < 3 ^ (2 * L) * 2 ^ (S.card - 2 * L) := Nat.mul_lt_mul_of_pos_right h1' hpos
      _ ≤ 3 ^ (2 * L) * 3 ^ (S.card - 2 * L) := Nat.mul_le_mul_left _ hdiff
  have h2 : 2 ^ S.card * f T < 2 ^ S.card * 2 ^ L := by
    have hpos : 0 < 2 ^ S.card := Nat.pos_of_ne_zero (by positivity)
    exact Nat.mul_lt_mul_of_pos_left (lt_of_le_of_lt hfT hb) hpos
  omega

-- Helper: doubling set size bound (if elements of D ≥ 1, ≤ b < 2^L, and distinct elements have factor ≥ 2, then D.card ≤ L)
lemma card_doubling_set_le {b L : ℕ} (hb : b < 2 ^ L)
    (D : Finset ℕ) (hDpos : ∀ d ∈ D, 1 ≤ d) (hDle : ∀ d ∈ D, d ≤ b)
    (hDdbl : ∀ x ∈ D, ∀ y ∈ D, x < y → 2 * x ≤ y) :
    D.card ≤ L := by
  have hpow : ∀ (M : Finset ℕ), (∀ d ∈ M, 1 ≤ d) →
      (∀ x ∈ M, ∀ y ∈ M, x < y → 2 * x ≤ y) →
      ∀ hne : M.Nonempty, 2 ^ (M.card - 1) ≤ M.max' hne := by
    intro M
    induction M using Finset.strongInduction with
    | H M ih =>
      intro hpos hdbl hne
      set mx := M.max' hne
      have hmxM : mx ∈ M := Finset.max'_mem M hne
      set M' := M.erase mx
      by_cases hM'e : M' = ∅
      · have hcard : M.card = 1 := by
          have := Finset.card_erase_add_one hmxM
          rw [show M.erase mx = M' from rfl, hM'e, Finset.card_empty] at this
          omega
        rw [hcard]
        simpa using hpos mx hmxM
      · have hM'ne : M'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hM'e
        have hM'ss : M' ⊂ M := Finset.erase_ssubset hmxM
        have hih := ih M' hM'ss (fun d hd => hpos d (Finset.mem_of_mem_erase hd))
          (fun x hx y hy hxy => hdbl x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hxy) hM'ne
        set mx' := M'.max' hM'ne
        have hmx'M' : mx' ∈ M' := Finset.max'_mem M' hM'ne
        have hmx'M : mx' ∈ M := Finset.mem_of_mem_erase hmx'M'
        have hlt : mx' < mx := lt_of_le_of_ne (Finset.le_max' M mx' hmx'M) (Finset.ne_of_mem_erase hmx'M')
        have h2le : 2 * mx' ≤ mx := hdbl mx' hmx'M mx hmxM hlt
        have hcard : M.card - 1 = (M'.card - 1) + 1 := by
          have h1 : M'.card + 1 = M.card := Finset.card_erase_add_one hmxM
          have h2 : 1 ≤ M'.card := hM'ne.card_pos
          omega
        rw [hcard, pow_succ']
        exact (Nat.mul_le_mul_left 2 hih).trans h2le
  by_cases hDe : D = ∅
  · subst hDe; simp
  · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr hDe
    have h1 := hpow D hDpos hDdbl hDne
    have h2 := hDle (D.max' hDne) (Finset.max'_mem D hDne)
    have h3 : 2 ^ (D.card - 1) < 2 ^ L := lt_of_le_of_lt (h1.trans h2) hb
    have h4 : D.card - 1 < L := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h3
    omega

section Lemma62

variable
  (h_zmod_char : ∀ (b : ℕ) [NeZero b] (H : AddSubgroup (ZMod b)),
    let d := b / (subFinset H).card
    d ∣ b ∧ 0 < d ∧ (subFinset H).card * d = b ∧
      (H = ⊤ ↔ d = 1) ∧
      (∀ x : ℕ, (x : ZMod b) ∈ H ↔ d ∣ x))
  (h_cos_sub : ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (K : AddSubgroup G) (P : Finset G) (_h0 : (0 : G) ∈ P)
    (_hPK : P ⊆ subFinset K) (_hgen : K ≤ AddSubgroup.closure (P : Set G))
    (k : ℕ) (_hk : 1 ≤ k),
    (subFinset K).card ≤ (finsetListSum (List.replicate k P)).card ∨
      k * P.card ≤ 2 * (finsetListSum (List.replicate k P)).card)
  (h_ssm_univ : ∀ {d : ℕ} [NeZero d] (A : Finset ℕ)
    (_hdiv : ∀ d' : ℕ, d' ∣ d → 1 < d' → d' - 1 ≤ (A.filter (fun a => ¬ d' ∣ a)).card),
    subsetSumMod d A = Finset.univ)
  (h_chernoff_half : ∀ {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset α) (c : Bool),
    ((Finset.univ.filter (fun f : α → Bool =>
        4 * (E.filter (fun a => f a = c)).card ≤ E.card)).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card α * Real.exp (- (E.card : ℝ) / 24))
  (h_small_growth : ∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A : Finset G) (d : ℕ) (_hd : d ≤ A.card),
    (Finset.univ.filter (fun x : G => ((x +ᵥ A) \ A).card ≤ d)).card * (A.card - d) ≤
      A.card * A.card)
  (h_sdiff_list : ∀ {G : Type} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (L : List G),
    ((L.sum +ᵥ A) \ A).card ≤ (L.map (fun x => ((x +ᵥ A) \ A).card)).sum)

-- Random partition helper for Lemma 6.2
include h_chernoff_half in
set_option maxHeartbeats 400000 in
lemma exists_good_split {b : ℕ} (hb : 2 ≤ b) (A A_inj : Finset ℕ)
    (hAinj_sub : A_inj ⊆ A)
    (hm1_big : 1600 * (log2P b) ^ 2 ≤ A_inj.card)
    (hdiv : ∀ d : ℕ, d ∣ b → 2 ≤ d → d ≤ 8 * b / A_inj.card →
      1200 * (log2P b) ^ 2 + 8 * d ≤ (A.filter (fun a => ¬ d ∣ a)).card) :
    ∃ A_init A_work : Finset ℕ,
      Disjoint A_init A_work ∧ A_init ∪ A_work = A ∧
      A_inj.card / 4 < (A_init ∩ A_inj).card ∧
      A_inj.card / 4 < (A_work ∩ A_inj).card ∧
      (∀ d : ℕ, d ∣ b → 2 ≤ d → d ≤ 8 * b / A_inj.card →
        300 * (log2P b) ^ 2 + 2 * d ≤ (A_work.filter (fun a => ¬ d ∣ a)).card) := by
  set L := log2P b
  set m1 := A_inj.card
  have hL2 : 2 ≤ L := by
    have : 1 ≤ Nat.log 2 b := Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 1 ≤ b)
    dsimp [L, log2P]; omega
  have hm1_pos : 1600 ≤ m1 := by
    have : 1 ≤ L ^ 2 := by nlinarith
    nlinarith
  -- Model random split as f : A → Bool (true = A_init, false = A_work)
  let E_inj : Finset A := Finset.univ.filter (fun x : A => x.1 ∈ A_inj)
  have hEinj_card : E_inj.card = m1 := by
    have hbij : E_inj.image Subtype.val = A_inj := by
      ext x
      simp only [E_inj, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨a, _, ha, heq⟩ => heq ▸ ha, fun hx => ⟨x, hAinj_sub hx, hx, rfl⟩⟩
    dsimp [m1]; rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
  let D_set : Finset ℕ := (Finset.Icc 2 (8 * b / m1)).filter (fun d => d ∣ b)
  let bad_init : Finset (A → Bool) := Finset.univ.filter (fun f =>
    4 * (E_inj.filter (fun x => f x = true)).card ≤ E_inj.card)
  let bad_work : Finset (A → Bool) := Finset.univ.filter (fun f =>
    4 * (E_inj.filter (fun x => f x = false)).card ≤ E_inj.card)
  let bad_div (d : ℕ) : Finset (A → Bool) :=
    let Ed : Finset A := Finset.univ.filter (fun x : A => ¬ d ∣ x.1)
    Finset.univ.filter (fun f => 4 * (Ed.filter (fun x => f x = false)).card ≤ Ed.card)
  let all_bad : Finset (A → Bool) := bad_init ∪ bad_work ∪ D_set.biUnion bad_div
  have hbad_lt : (all_bad.card : ℝ) < (2 : ℝ) ^ Fintype.card A := by
    have hcard_union : all_bad.card ≤ bad_init.card + bad_work.card + ∑ d ∈ D_set, (bad_div d).card := by
      calc all_bad.card
          ≤ (bad_init ∪ bad_work).card + (D_set.biUnion bad_div).card := Finset.card_union_le _ _
        _ ≤ bad_init.card + bad_work.card + ∑ d ∈ D_set, (bad_div d).card :=
            Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le
    have hcard_R : (all_bad.card : ℝ) ≤
        (bad_init.card : ℝ) + (bad_work.card : ℝ) + ∑ d ∈ D_set, ((bad_div d).card : ℝ) := by
      exact_mod_cast hcard_union
    have hb1 : (bad_init.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A * Real.exp (- (m1 : ℝ) / 24) := by
      dsimp [bad_init]; rw [← hEinj_card]; exact h_chernoff_half E_inj true
    have hb2 : (bad_work.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A * Real.exp (- (m1 : ℝ) / 24) := by
      dsimp [bad_work]; rw [← hEinj_card]; exact h_chernoff_half E_inj false
    have hbd : ∀ d ∈ D_set, ((bad_div d).card : ℝ) ≤
        (2 : ℝ) ^ Fintype.card A * Real.exp (- (50 * (L : ℝ) ^ 2)) := by
      intro d hd
      obtain ⟨hdI, hddvd⟩ := Finset.mem_filter.mp hd
      obtain ⟨hd2, hdub⟩ := Finset.mem_Icc.mp hdI
      let Ed : Finset A := Finset.univ.filter (fun x : A => ¬ d ∣ x.1)
      have hEd_card : Ed.card = (A.filter (fun a => ¬ d ∣ a)).card := by
        have hbij : Ed.image Subtype.val = A.filter (fun a => ¬ d ∣ a) := by
          ext x
          simp only [Ed, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
          exact ⟨fun ⟨a, haA, hnd, heq⟩ => heq ▸ ⟨haA, hnd⟩, fun ⟨hxA, hnd⟩ => ⟨x, hxA, hnd, rfl⟩⟩
        rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
      have hEd_ge : 1200 * L ^ 2 ≤ Ed.card := by
        rw [hEd_card]
        have := hdiv d hddvd hd2 hdub
        omega
      have hch := h_chernoff_half Ed false
      have hexp_le : Real.exp (- (Ed.card : ℝ) / 24) ≤ Real.exp (- (50 * (L : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        have hR : (1200 * L ^ 2 : ℝ) ≤ (Ed.card : ℝ) := by exact_mod_cast hEd_ge
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp_le (by positivity))
    have hDcard : (D_set.card : ℝ) ≤ (b : ℝ) := by
      have hsub : D_set ⊆ Finset.Icc 1 b := by
        intro d hd
        obtain ⟨hdI, hddvd⟩ := Finset.mem_filter.mp hd
        have hd2 := (Finset.mem_Icc.mp hdI).1
        exact Finset.mem_Icc.mpr ⟨by omega, Nat.le_of_dvd (by omega) hddvd⟩
      have hle : D_set.card ≤ b := by simpa using Finset.card_le_card hsub
      exact_mod_cast hle
    have hsum_d : ∑ d ∈ D_set, ((bad_div d).card : ℝ) ≤
        (2 : ℝ) ^ Fintype.card A * ((b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2))) := by
      calc ∑ d ∈ D_set, ((bad_div d).card : ℝ)
          ≤ ∑ _d ∈ D_set, ((2 : ℝ) ^ Fintype.card A * Real.exp (- (50 * (L : ℝ) ^ 2))) :=
            Finset.sum_le_sum hbd
        _ = (D_set.card : ℝ) * ((2 : ℝ) ^ Fintype.card A * Real.exp (- (50 * (L : ℝ) ^ 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (b : ℝ) * ((2 : ℝ) ^ Fintype.card A * Real.exp (- (50 * (L : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_right hDcard (by positivity)
        _ = (2 : ℝ) ^ Fintype.card A * ((b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2))) := by ring
    -- Bound exp(-m1/24) < 1/4 and b * exp(-50*L^2) < 1/4
    have hexp1 : Real.exp (- (m1 : ℝ) / 24) < 1 / 4 := by
      have h1 : Real.exp (- (m1 : ℝ) / 24) ≤ Real.exp (-2 : ℝ) := by
        apply Real.exp_le_exp.mpr
        have hm1R : (1600 : ℝ) ≤ (m1 : ℝ) := by exact_mod_cast hm1_pos
        linarith
      have h2 : Real.exp (-2 : ℝ) < 1 / 4 := by
        rw [Real.exp_neg]
        have he : (2.5 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he2 : (4 : ℝ) < Real.exp 2 := by
          have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [this]; nlinarith
        have hinv : (Real.exp 2)⁻¹ < (4 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he2
        linarith
      linarith
    have hexp2 : (b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2)) < 1 / 4 := by
      have hb_lt : (b : ℝ) < Real.exp (L : ℝ) := by
        have h1 : (b : ℝ) < (2 : ℝ) ^ L := by exact_mod_cast (lt_two_pow_log2P (n := b))
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have h3 : (2 : ℝ) ^ L ≤ (Real.exp 1) ^ L := pow_le_pow_left₀ (by norm_num) h2 L
        rw [← Real.exp_nat_mul, mul_one] at h3
        linarith
      have hmul_lt : (b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2)) <
          Real.exp (L : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2)) :=
        mul_lt_mul_of_pos_right hb_lt (Real.exp_pos _)
      rw [← Real.exp_add] at hmul_lt
      have hle2 : Real.exp ((L : ℝ) + -(50 * (L : ℝ) ^ 2)) ≤ Real.exp (-2 : ℝ) := by
        apply Real.exp_le_exp.mpr
        have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
        nlinarith
      have h2 : Real.exp (-2 : ℝ) < 1 / 4 := by
        rw [Real.exp_neg]
        have he : (2.5 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have he2 : (4 : ℝ) < Real.exp 2 := by
          have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          rw [this]; nlinarith
        have hinv : (Real.exp 2)⁻¹ < (4 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he2
        linarith
      linarith
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card A := by positivity
    calc (all_bad.card : ℝ)
        ≤ (bad_init.card : ℝ) + (bad_work.card : ℝ) + ∑ d ∈ D_set, ((bad_div d).card : ℝ) := hcard_R
      _ ≤ (2 : ℝ) ^ Fintype.card A * Real.exp (- (m1 : ℝ) / 24) +
            (2 : ℝ) ^ Fintype.card A * Real.exp (- (m1 : ℝ) / 24) +
            (2 : ℝ) ^ Fintype.card A * ((b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2))) := by linarith
      _ = (2 : ℝ) ^ Fintype.card A * (2 * Real.exp (- (m1 : ℝ) / 24) +
            (b : ℝ) * Real.exp (- (50 * (L : ℝ) ^ 2))) := by ring
      _ < (2 : ℝ) ^ Fintype.card A * 1 := by
          apply mul_lt_mul_of_pos_left _ h2pos
          linarith
      _ = (2 : ℝ) ^ Fintype.card A := mul_one _
  have hlt_nat : all_bad.card < (Finset.univ : Finset (A → Bool)).card := by
    have hcard_univ : ((Finset.univ : Finset (A → Bool)).card : ℝ) = (2 : ℝ) ^ Fintype.card A := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
      push_cast; rfl
    exact_mod_cast (hcard_univ.symm ▸ hbad_lt)
  obtain ⟨f, _, hf_not_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_nat
  have hf_not_init : f ∉ bad_init := fun h =>
    hf_not_bad (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hf_not_work : f ∉ bad_work := fun h =>
    hf_not_bad (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hf_not_div : ∀ d ∈ D_set, f ∉ bad_div d := fun d hd h =>
    hf_not_bad (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, h⟩))
  let A_init : Finset ℕ := (Finset.univ.filter (fun x : A => f x = true)).image Subtype.val
  let A_work : Finset ℕ := (Finset.univ.filter (fun x : A => f x = false)).image Subtype.val
  refine ⟨A_init, A_work, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp ha1
    obtain ⟨x2, hx2, heq⟩ := Finset.mem_image.mp ha2
    have hx12 : x1 = x2 := Subtype.ext heq.symm
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    rw [hx12, h2] at h1
    contradiction
  · ext a
    simp only [A_init, A_work, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Subtype.exists]
    constructor
    · rintro (⟨x, hxA, _, rfl⟩ | ⟨x, hxA, _, rfl⟩) <;> exact hxA
    · intro haA
      cases hfa : f ⟨a, haA⟩
      · right; exact ⟨a, haA, hfa, rfl⟩
      · left; exact ⟨a, haA, hfa, rfl⟩
  · have hgt : E_inj.card < 4 * (E_inj.filter (fun x => f x = true)).card := by
      by_contra hle; push Not at hle
      exact hf_not_init (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    have hbij : (E_inj.filter (fun x => f x = true)).image Subtype.val = A_init ∩ A_inj := by
      ext a
      simp only [E_inj, A_init, Finset.mem_image, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_univ, true_and, Subtype.exists]
      constructor
      · rintro ⟨x, hxA, ⟨hxinj, hfx⟩, rfl⟩
        exact ⟨⟨x, hxA, hfx, rfl⟩, hxinj⟩
      · rintro ⟨⟨x, hxA, hfx, rfl⟩, hxinj⟩
        exact ⟨x, hxA, ⟨hxinj, hfx⟩, rfl⟩
    have hcard_eq : (E_inj.filter (fun x => f x = true)).card = (A_init ∩ A_inj).card := by
      rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hEinj_card, hcard_eq] at hgt
    omega
  · have hgt : E_inj.card < 4 * (E_inj.filter (fun x => f x = false)).card := by
      by_contra hle; push Not at hle
      exact hf_not_work (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    have hbij : (E_inj.filter (fun x => f x = false)).image Subtype.val = A_work ∩ A_inj := by
      ext a
      simp only [E_inj, A_work, Finset.mem_image, Finset.mem_filter, Finset.mem_inter,
        Finset.mem_univ, true_and, Subtype.exists]
      constructor
      · rintro ⟨x, hxA, ⟨hxinj, hfx⟩, rfl⟩
        exact ⟨⟨x, hxA, hfx, rfl⟩, hxinj⟩
      · rintro ⟨⟨x, hxA, hfx, rfl⟩, hxinj⟩
        exact ⟨x, hxA, ⟨hxinj, hfx⟩, rfl⟩
    have hcard_eq : (E_inj.filter (fun x => f x = false)).card = (A_work ∩ A_inj).card := by
      rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hEinj_card, hcard_eq] at hgt
    omega
  · intro d hddvd hd2 hdub
    have hdD : d ∈ D_set := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd2, hdub⟩, hddvd⟩
    let Ed : Finset A := Finset.univ.filter (fun x : A => ¬ d ∣ x.1)
    have hgt : Ed.card < 4 * (Ed.filter (fun x => f x = false)).card := by
      by_contra hle; push Not at hle
      exact hf_not_div d hdD (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    have hEd_card : Ed.card = (A.filter (fun a => ¬ d ∣ a)).card := by
      have hbij : Ed.image Subtype.val = A.filter (fun a => ¬ d ∣ a) := by
        ext x
        simp only [Ed, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
        exact ⟨fun ⟨a, haA, hnd, heq⟩ => heq ▸ ⟨haA, hnd⟩, fun ⟨hxA, hnd⟩ => ⟨x, hxA, hnd, rfl⟩⟩
      rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
    have hbij2 : (Ed.filter (fun x => f x = false)).image Subtype.val =
        A_work.filter (fun a => ¬ d ∣ a) := by
      ext a
      simp only [Ed, A_work, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Subtype.exists]
      constructor
      · rintro ⟨x, hxA, ⟨hnd, hfx⟩, rfl⟩
        exact ⟨⟨x, hxA, hfx, rfl⟩, hnd⟩
      · rintro ⟨⟨x, hxA, hfx, rfl⟩, hnd⟩
        exact ⟨x, hxA, ⟨hnd, hfx⟩, rfl⟩
    have hcard_eq : (Ed.filter (fun x => f x = false)).card =
        (A_work.filter (fun a => ¬ d ∣ a)).card := by
      rw [← hbij2, Finset.card_image_of_injective _ Subtype.val_injective]
    have hdiv_ge := hdiv d hddvd hd2 hdub
    rw [hEd_card, hcard_eq] at hgt
    omega

include h_zmod_char h_cos_sub h_ssm_univ h_chernoff_half h_small_growth h_sdiff_list in
set_option maxHeartbeats 800000 in
theorem lemma_6_2 {b : ℕ} (hb : 2 ≤ b) (A A_inj : Finset ℕ)
    (hAinj_sub : A_inj ⊆ A)
    (hAinj_lt : ∀ x ∈ A_inj, x < b)
    (hA_le : A.card ≤ 16 * A_inj.card)
    (hm1_big : 1600 * (log2P b) ^ 2 ≤ A_inj.card)
    (hdiv : ∀ d : ℕ, d ∣ b → 2 ≤ d → d ≤ 8 * b / A_inj.card →
      1200 * (log2P b) ^ 2 + 8 * d ≤ (A.filter (fun a => ¬ d ∣ a)).card) :
    let k := 8192 * b / A_inj.card + 2
    min (A_inj.card * A_inj.card / 131072) (b / 4) ≤ (subsetSumModLe b (k + 1) A).card := by
  haveI : NeZero b := ⟨by omega⟩
  set L := log2P b
  set m1 := A_inj.card
  set k := 8192 * b / m1 + 2
  have hL2 : 2 ≤ L := by
    have : 1 ≤ Nat.log 2 b := Nat.le_log_of_pow_le (by decide) (by omega : 2 ^ 1 ≤ b)
    dsimp [L, log2P]; omega
  have hm1_ge : 6400 ≤ m1 := by
    have : 4 ≤ L ^ 2 := by nlinarith
    nlinarith
  obtain ⟨A_init, A_work, hdisj_iw, hunion_iw, hinit_gt, hwork_gt, hwork_div⟩ :=
    exists_good_split h_chernoff_half hb A A_inj hAinj_sub hm1_big hdiv
  have hinit_sub : A_init ⊆ A := hunion_iw ▸ Finset.subset_union_left
  have hwork_sub : A_work ⊆ A := hunion_iw ▸ Finset.subset_union_right
  have hinj_mod : Set.InjOn (fun x : ℕ => (x : ZMod b)) (A_inj : Set ℕ) := by
    intro x hx y hy heq
    have hxlt := hAinj_lt x hx
    have hylt := hAinj_lt y hy
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt hxlt, ZMod.val_natCast_of_lt hylt] at hval
    exact hval
  set S0 : Finset (ZMod b) := A_init.image (fun x : ℕ => (x : ZMod b))
  have hS0_card : m1 / 4 < S0.card := by
    have hsub : (A_init ∩ A_inj).image (fun x : ℕ => (x : ZMod b)) ⊆ S0 :=
      Finset.image_subset_image Finset.inter_subset_left
    have heq : ((A_init ∩ A_inj).image (fun x : ℕ => (x : ZMod b))).card = (A_init ∩ A_inj).card :=
      Finset.card_image_of_injOn (hinj_mod.mono (by intro x hx; exact (Finset.mem_inter.mp hx).2))
    have hle := Finset.card_le_card hsub
    omega
  -- Define phase predicates and greedy step on U ⊆ A_work
  let remOf (U : Finset ℕ) : Finset ℕ := A_work \ U
  let ROf (U : Finset ℕ) : Finset (ZMod b) := (remOf U).image (fun x : ℕ => (x : ZMod b))
  let HOf (U : Finset ℕ) : AddSubgroup (ZMod b) := AddSubgroup.closure ((ROf U : Finset (ZMod b)) : Set (ZMod b))
  let SOf (U : Finset ℕ) : Finset (ZMod b) := S0 + subsetSumMod b U
  let SHOf (U : Finset ℕ) : Finset (ZMod b) :=
    subsetSumMod b (U.filter (fun a : ℕ => (a : ZMod b) ∈ HOf U))
  let sliceOf (U : Finset ℕ) (u : ZMod b) : Finset (ZMod b) :=
    (SOf U).filter (fun x => x - u ∈ HOf U)
  let isGrowth (U : Finset ℕ) : Prop :=
    ∃ u : ZMod b, (sliceOf U u).Nonempty ∧ 128 * (sliceOf U u).card ≤ (ROf U).card
  let isUnsat (U : Finset ℕ) : Prop :=
    ¬ isGrowth U ∧
    ∃ u : ZMod b, (sliceOf U u).Nonempty ∧ 4 * (sliceOf U u).card < (subFinset (HOf U)).card
  let isSat (U : Finset ℕ) : Prop := ¬ isGrowth U ∧ ¬ isUnsat U
  let pickElem (U : Finset ℕ) (hne : (remOf U).Nonempty) : ℕ :=
    if isGrowth U then
      if hg : ∃ a ∈ remOf U, (SHOf U).card ≤ 2 * (((a : ZMod b) +ᵥ SHOf U) \ SHOf U).card then
        Classical.choose hg
      else Classical.choose hne
    else
      if hu : ∃ a ∈ remOf U, (ROf U).card ≤ 528 * (((a : ZMod b) +ᵥ SOf U) \ SOf U).card then
        Classical.choose hu
      else Classical.choose hne
  have hpick_mem : ∀ (U : Finset ℕ) (hne : (remOf U).Nonempty), pickElem U hne ∈ remOf U := by
    intro U hne
    dsimp [pickElem]
    split_ifs with h1 h2 h3
    · exact (Classical.choose_spec h2).1
    · exact Classical.choose_spec hne
    · exact (Classical.choose_spec h3).1
    · exact Classical.choose_spec hne
  let stepU : ℕ → Finset ℕ := fun t => Nat.rec ∅ (fun _ U =>
    if hne : (remOf U).Nonempty then insert (pickElem U hne) U else U) t
  have hstepU_zero : stepU 0 = ∅ := rfl
  have hstepU_succ : ∀ t, stepU (t + 1) =
      if hne : (remOf (stepU t)).Nonempty then insert (pickElem (stepU t) hne) (stepU t)
      else stepU t := fun _ => rfl
  have hstepU_sub : ∀ t, stepU t ⊆ A_work := by
    intro t
    induction t with
    | zero => exact Finset.empty_subset _
    | succ t ih =>
      rw [hstepU_succ]
      split_ifs with hne
      · exact Finset.insert_subset (Finset.mem_sdiff.mp (hpick_mem _ hne)).1 ih
      · exact ih
  have hstepU_mono : ∀ t1 t2, t1 ≤ t2 → stepU t1 ⊆ stepU t2 := by
    intro t1 t2 hle
    induction hle with
    | refl => exact Finset.Subset.refl _
    | @step m _ ih =>
      rw [hstepU_succ]
      split_ifs with hne
      · exact ih.trans (Finset.subset_insert _ _)
      · exact ih
  have hstepU_card_le : ∀ t, (stepU t).card ≤ t := by
    intro t
    induction t with
    | zero => simp [hstepU_zero]
    | succ t ih =>
      rw [hstepU_succ]
      split_ifs with hne
      · have hnot : pickElem (stepU t) hne ∉ stepU t :=
          (Finset.mem_sdiff.mp (hpick_mem _ hne)).2
        rw [Finset.card_insert_of_notMem hnot]; omega
      · omega
  -- Helper: SOf (stepU t) ⊆ subsetSumModLe b (t + 1) A
  have hS_sub_modLe : ∀ t, SOf (stepU t) ⊆ subsetSumModLe b (t + 1) A := by
    intro t x hx
    obtain ⟨s0z, hs0z, tz, htz, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨s0, hs0, rfl⟩ := Finset.mem_image.mp hs0z
    obtain ⟨S, hSU, rfl⟩ := Finset.mem_image.mp htz
    have hSU' : S ⊆ stepU t := Finset.mem_powerset.mp hSU
    have hs0_notS : s0 ∉ S := fun h =>
      Finset.disjoint_left.mp hdisj_iw hs0 (hstepU_sub t (hSU' h))
    refine Finset.mem_image.mpr ⟨(insert s0 S).sum id, ?_, ?_⟩
    · refine Finset.mem_image.mpr ⟨insert s0 S, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (Finset.insert_subset (hinit_sub hs0) ((hSU'.trans (hstepU_sub t)).trans hwork_sub)), ?_⟩, rfl⟩
      rw [Finset.card_insert_of_notMem hs0_notS]
      have h1 : S.card ≤ (stepU t).card := Finset.card_le_card hSU'
      have h2 := hstepU_card_le t
      omega
    · rw [Finset.sum_insert hs0_notS, id_eq, Nat.cast_add]
  -- Helper: for t ≤ m1 / 8, remOf (stepU t) has ≥ m1 / 8 elements in A_inj, hence (ROf (stepU t)).card ≥ m1 / 8
  have hR_ge : ∀ t ≤ m1 / 8, m1 / 8 ≤ (ROf (stepU t)).card ∧ (remOf (stepU t)).Nonempty := by
    intro t ht
    have hcard_inter : m1 / 8 ≤ (remOf (stepU t) ∩ A_inj).card := by
      have hsub : A_work ∩ A_inj ⊆ (remOf (stepU t) ∩ A_inj) ∪ stepU t := by
        intro a ha
        obtain ⟨haW, haI⟩ := Finset.mem_inter.mp ha
        rcases Classical.em (a ∈ stepU t) with haU | haU
        · exact Finset.mem_union_right _ haU
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨haW, haU⟩, haI⟩)
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_union_le (remOf (stepU t) ∩ A_inj) (stepU t)
      have h3 := hstepU_card_le t
      omega
    have hsubR : (remOf (stepU t) ∩ A_inj).image (fun x : ℕ => (x : ZMod b)) ⊆ ROf (stepU t) :=
      Finset.image_subset_image Finset.inter_subset_left
    have heq : ((remOf (stepU t) ∩ A_inj).image (fun x : ℕ => (x : ZMod b))).card =
        (remOf (stepU t) ∩ A_inj).card :=
      Finset.card_image_of_injOn (hinj_mod.mono (by intro x hx; exact (Finset.mem_inter.mp hx).2))
    have hRcard : m1 / 8 ≤ (ROf (stepU t)).card := by
      have := Finset.card_le_card hsubR
      omega
    have hne : (remOf (stepU t)).Nonempty := by
      have hpos : 0 < (remOf (stepU t) ∩ A_inj).card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact ⟨x, (Finset.mem_inter.mp hx).1⟩
    exact ⟨hRcard, hne⟩
  -- For t ≤ m1 / 8, d_t = b / |H_t| satisfies d_t ∣ b, 1 ≤ d_t ≤ 8 * b / m1
  let dOf (U : Finset ℕ) : ℕ := b / (subFinset (HOf U)).card
  have hd_props : ∀ t ≤ m1 / 8,
      dOf (stepU t) ∣ b ∧ 0 < dOf (stepU t) ∧
      (subFinset (HOf (stepU t))).card * dOf (stepU t) = b ∧
      dOf (stepU t) ≤ 8 * b / m1 ∧
      (HOf (stepU t) = ⊤ ↔ dOf (stepU t) = 1) ∧
      (∀ x : ℕ, (x : ZMod b) ∈ HOf (stepU t) ↔ dOf (stepU t) ∣ x) := by
    intro t ht
    obtain ⟨hd_dvd, hd_pos, hmul, htop, hchar⟩ := h_zmod_char b (HOf (stepU t))
    have hRsubH : ROf (stepU t) ⊆ subFinset (HOf (stepU t)) := fun y hy =>
      mem_subFinset.mpr (AddSubgroup.subset_closure hy)
    have hHge : m1 / 8 ≤ (subFinset (HOf (stepU t))).card :=
      (hR_ge t ht).1.trans (Finset.card_le_card hRsubH)
    have hd_ub : dOf (stepU t) ≤ 8 * b / m1 := by
      have h1 : (m1 / 8) * dOf (stepU t) ≤ b := by
        calc (m1 / 8) * dOf (stepU t) ≤ (subFinset (HOf (stepU t))).card * dOf (stepU t) :=
              Nat.mul_le_mul_right _ hHge
          _ = b := hmul
      have h2 : m1 ≤ 9 * (m1 / 8) := by omega
      have h3 : m1 * dOf (stepU t) ≤ 8 * b := by
        -- Wait: we have m1 / 8 ≤ (R).card, in fact (m1 / 4 + 1) - t ≥ m1 / 8 + 1!
        -- Actually let's check: (m1 / 8) * 8 ≤ m1 ≤ (m1 / 8) * 8 + 7.
        -- Even simpler: (rem ∩ A_inj).card ≥ (m1/4 + 1) - m1/8 ≥ (m1 + 7)/8! Wait:
        -- hwork_gt gives m1 / 4 < (A_work ∩ A_inj).card, so (A_work ∩ A_inj).card ≥ m1 / 4 + 1.
        -- Subtracting t ≤ m1 / 8 gives (rem ∩ A_inj).card ≥ m1 / 4 + 1 - m1 / 8 = (m1 + 8) / 8?
        -- Let's check: 8 * (m1 / 4 + 1 - m1 / 8) ≥ m1 ALWAYS!
        have hcard_exact : m1 ≤ 8 * (subFinset (HOf (stepU t))).card := by
          have hsub : A_work ∩ A_inj ⊆ (remOf (stepU t) ∩ A_inj) ∪ stepU t := by
            intro a ha
            obtain ⟨haW, haI⟩ := Finset.mem_inter.mp ha
            rcases Classical.em (a ∈ stepU t) with haU | haU
            · exact Finset.mem_union_right _ haU
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨haW, haU⟩, haI⟩)
          have h1' := Finset.card_le_card hsub
          have h2' := Finset.card_union_le (remOf (stepU t) ∩ A_inj) (stepU t)
          have h3' := hstepU_card_le t
          have hsubR : (remOf (stepU t) ∩ A_inj).image (fun x : ℕ => (x : ZMod b)) ⊆ ROf (stepU t) :=
            Finset.image_subset_image Finset.inter_subset_left
          have heq : ((remOf (stepU t) ∩ A_inj).image (fun x : ℕ => (x : ZMod b))).card =
              (remOf (stepU t) ∩ A_inj).card :=
            Finset.card_image_of_injOn (hinj_mod.mono (by intro x hx; exact (Finset.mem_inter.mp hx).2))
          have h4' := Finset.card_le_card hsubR
          have h5' := Finset.card_le_card hRsubH
          omega
        calc m1 * dOf (stepU t) ≤ (8 * (subFinset (HOf (stepU t))).card) * dOf (stepU t) :=
              Nat.mul_le_mul_right _ hcard_exact
          _ = 8 * ((subFinset (HOf (stepU t))).card * dOf (stepU t)) := by ring
          _ = 8 * b := by rw [hmul]
      exact (Nat.le_div_iff_mul_le (by omega : 0 < m1)).mpr (by rw [mul_comm]; exact h3)
    exact ⟨hd_dvd, hd_pos, hmul, hd_ub, htop, hchar⟩
  -- Claim 1: For t ≤ 200 * L ^ 2 (and t ≤ m1 / 8), step t is NOT a growth phase
  have hClaim1 : ∀ t ≤ 200 * L ^ 2, t ≤ m1 / 8 → ¬ isGrowth (stepU t) := by
    intro t htL htm
    obtain ⟨hd_dvd, hd_pos, hmul, hd_ub, htop, hchar⟩ := hd_props t htm
    have hd1 : dOf (stepU t) = 1 := by
      by_contra hne
      have hd2 : 2 ≤ dOf (stepU t) := by omega
      have hwd : 300 * L ^ 2 + 2 * dOf (stepU t) ≤ (A_work.filter (fun a => ¬ dOf (stepU t) ∣ a)).card :=
        hwork_div (dOf (stepU t)) hd_dvd hd2 hd_ub
      have hLsq_lt : 200 * L ^ 2 < 300 * L ^ 2 := by nlinarith
      have hcard_rem_nd : 1 ≤ ((remOf (stepU t)).filter (fun a => ¬ dOf (stepU t) ∣ a)).card := by
        have hsub : A_work.filter (fun a => ¬ dOf (stepU t) ∣ a) ⊆
            (remOf (stepU t)).filter (fun a => ¬ dOf (stepU t) ∣ a) ∪ stepU t := by
          intro a ha
          obtain ⟨haW, hnd⟩ := Finset.mem_filter.mp ha
          rcases Classical.em (a ∈ stepU t) with haU | haU
          · exact Finset.mem_union_right _ haU
          · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨haW, haU⟩, hnd⟩)
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le ((remOf (stepU t)).filter (fun a => ¬ dOf (stepU t) ∣ a)) (stepU t)
        have h3 := hstepU_card_le t
        omega
      obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard_rem_nd
      obtain ⟨harem, hnd⟩ := Finset.mem_filter.mp ha
      have haH : (a : ZMod b) ∈ HOf (stepU t) :=
        AddSubgroup.subset_closure (Finset.mem_image_of_mem _ harem)
      exact hnd ((hchar a).mp haH)
    have hHtop : HOf (stepU t) = ⊤ := htop.mpr hd1
    intro ⟨u, _, hle⟩
    have hslice_eq : sliceOf (stepU t) u = SOf (stepU t) := by
      ext x
      simp only [sliceOf, Finset.mem_filter, hHtop, AddSubgroup.mem_top, and_true]
    have hS0_le : S0.card ≤ (SOf (stepU t)).card := by
      have hsub : S0 ⊆ SOf (stepU t) := fun x hx =>
        Finset.mem_add.mpr ⟨x, hx, 0, zero_mem_subsetSumMod b _, add_zero x⟩
      exact Finset.card_le_card hsub
    have hR_le : (ROf (stepU t)).card ≤ A.card := by
      calc (ROf (stepU t)).card ≤ (remOf (stepU t)).card := Finset.card_image_le
        _ ≤ A_work.card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ A.card := Finset.card_le_card hwork_sub
    rw [hslice_eq] at hle
    omega
  -- Growth step guarantee: if t ≤ m1 / 8 and isGrowth (stepU t), then picking a gives 3 * |SH| ≤ 2 * |SH_next|
  have hGrowth_step : ∀ t ≤ m1 / 8, isGrowth (stepU t) →
      ∃ a ∈ remOf (stepU t), (SHOf (stepU t)).card ≤
        2 * (((a : ZMod b) +ᵥ SHOf (stepU t)) \ SHOf (stepU t)).card := by
    intro t htm ⟨u, hune, hule⟩
    have h511 := card_coset_ge_sub A_init (stepU t) (HOf (stepU t)) u hune
    set S := SHOf (stepU t)
    have hSle : 128 * S.card ≤ (ROf (stepU t)).card := by
      have : S.card ≤ (sliceOf (stepU t) u).card := h511
      omega
    have hSpos : 1 ≤ S.card := Finset.card_pos.mpr ⟨0, zero_mem_subsetSumMod b _⟩
    have hRge : m1 / 8 ≤ (ROf (stepU t)).card := (hR_ge t htm).1
    by_cases hS1 : S.card = 1
    · have hR2 : 2 ≤ (ROf (stepU t)).card := by omega
      have hex : ∃ z ∈ ROf (stepU t), z ≠ 0 := by
        by_contra hall
        push Not at hall
        have hsub : ROf (stepU t) ⊆ {0} := fun z hz => Finset.mem_singleton.mpr (hall z hz)
        have := Finset.card_le_card hsub
        simp at this; omega
      obtain ⟨z, hzR, hz0⟩ := hex
      obtain ⟨a, harem, rfl⟩ := Finset.mem_image.mp hzR
      refine ⟨a, harem, ?_⟩
      have h0S : (0 : ZMod b) ∈ S := zero_mem_subsetSumMod b _
      have hSeq : S = {0} := Finset.eq_singleton_iff_unique_mem.mpr
        ⟨h0S, fun y hy => by
          by_contra hne
          have hsub : ({0, y} : Finset (ZMod b)) ⊆ S := by
            intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl <;> assumption
          have := Finset.card_le_card hsub
          rw [Finset.card_pair (Ne.symm hne)] at this; omega⟩
      have hdiff1 : (((a : ZMod b) +ᵥ S) \ S).card = 1 := by
        have hmem : (a : ZMod b) ∈ ((a : ZMod b) +ᵥ S) \ S := by
          rw [hSeq]
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_vadd_finset.mpr ⟨0, by simp, by simp [vadd_eq_add]⟩, ?_⟩
          simpa using hz0
        have hsub : ((a : ZMod b) +ᵥ S) \ S ⊆ {(a : ZMod b)} := by
          intro w hw
          obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp (Finset.mem_sdiff.mp hw).1
          rw [hSeq, Finset.mem_singleton] at hy
          simp [hy, vadd_eq_add]
        have hle1 := Finset.card_le_card hsub
        have hge1 : 1 ≤ (((a : ZMod b) +ᵥ S) \ S).card := Finset.card_pos.mpr ⟨_, hmem⟩
        simp at hle1; omega
      omega
    · have hS2 : 2 ≤ S.card := by omega
      set d0 := (S.card - 1) / 2
      have hd0le : d0 ≤ S.card := by omega
      have h26 := h_small_growth S d0 hd0le
      set Gd := Finset.univ.filter (fun x : ZMod b => ((x +ᵥ S) \ S).card ≤ d0)
      have hGd_le : Gd.card ≤ 2 * S.card := by
        have hdiff_ge : S.card ≤ 2 * (S.card - d0) := by omega
        have h1 : Gd.card * S.card ≤ Gd.card * (2 * (S.card - d0)) := Nat.mul_le_mul_left _ hdiff_ge
        have h2 : Gd.card * (2 * (S.card - d0)) = 2 * (Gd.card * (S.card - d0)) := by ring
        have h3 : 2 * (Gd.card * (S.card - d0)) ≤ 2 * (S.card * S.card) := Nat.mul_le_mul_left 2 h26
        have h4 : Gd.card * S.card ≤ (2 * S.card) * S.card := by linarith
        exact Nat.le_of_mul_le_mul_right h4 (by omega)
      have hlt : Gd.card < (ROf (stepU t)).card := by omega
      obtain ⟨z, hzR, hznot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨a, harem, rfl⟩ := Finset.mem_image.mp hzR
      have hgt : d0 < (((a : ZMod b) +ᵥ S) \ S).card := by
        by_contra hle; push Not at hle
        exact hznot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
      exact ⟨a, harem, by omega⟩
  -- Claim 2: For any T ≤ m1 / 8, at most 2 * L ^ 2 steps t < T are growth phases
  have hClaim2 : ∀ T ≤ m1 / 8,
      ((Finset.range T).filter (fun t => isGrowth (stepU t))).card ≤ 2 * L ^ 2 := by
    intro T hTm
    set Gsteps := (Finset.range T).filter (fun t => isGrowth (stepU t))
    set Dvals := (Finset.range T).image (fun t => dOf (stepU t))
    have hH_anti : ∀ t1 t2, t1 ≤ t2 → HOf (stepU t2) ≤ HOf (stepU t1) := by
      intro t1 t2 hle
      apply AddSubgroup.closure_mono
      intro z hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨haW, haU2⟩ := Finset.mem_sdiff.mp ha
      exact Finset.mem_image_of_mem _ (Finset.mem_sdiff.mpr ⟨haW, fun h => haU2 (hstepU_mono t1 t2 hle h)⟩)
    have hd_dvd_mono : ∀ t1 t2, t1 ≤ t2 → t2 < T → dOf (stepU t1) ∣ dOf (stepU t2) := by
      intro t1 t2 h12 h2T
      have ht1 : t1 ≤ m1 / 8 := by omega
      have ht2 : t2 ≤ m1 / 8 := by omega
      obtain ⟨_, hd1pos, hmul1, _, _, hchar1⟩ := hd_props t1 ht1
      obtain ⟨_, hd2pos, hmul2, _, _, hchar2⟩ := hd_props t2 ht2
      have hmem : (dOf (stepU t2) : ZMod b) ∈ HOf (stepU t2) := (hchar2 _).mpr dvd_rfl
      exact (hchar1 _).mp (hH_anti t1 t2 h12 hmem)
    have hDvals_le : Dvals.card ≤ L := by
      refine card_doubling_set_le (lt_two_pow_log2P (n := b)) Dvals ?_ ?_ ?_
      · intro d hd
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
        have ht' : t ≤ m1 / 8 := by have := Finset.mem_range.mp ht; omega
        exact (hd_props t ht').2.1
      · intro d hd
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
        have ht' : t ≤ m1 / 8 := by have := Finset.mem_range.mp ht; omega
        exact Nat.le_of_dvd (by omega) (hd_props t ht').1
      · intro x hx y hy hxy
        obtain ⟨t1, ht1, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨t2, ht2, rfl⟩ := Finset.mem_image.mp hy
        have ht1T := Finset.mem_range.mp ht1
        have ht2T := Finset.mem_range.mp ht2
        rcases le_total t1 t2 with h12 | h21
        · obtain ⟨c, hc⟩ := hd_dvd_mono t1 t2 h12 ht2T
          have hc2 : 2 ≤ c := by
            by_contra hc1
            have : c = 0 ∨ c = 1 := by omega
            rcases this with rfl | rfl <;> omega
          nlinarith
        · have hdvd := hd_dvd_mono t2 t1 h21 ht1T
          have hpos : 0 < dOf (stepU t1) := (hd_props t1 (by omega)).2.1
          have hle := Nat.le_of_dvd hpos hdvd
          omega
    have hfib : ∀ d ∈ Dvals, (Gsteps.filter (fun t => dOf (stepU t) = d)).card ≤ 2 * L := by
      intro d hd
      obtain ⟨t0, ht0, rfl⟩ := Finset.mem_image.mp hd
      set H0 := HOf (stepU t0)
      have ht0m : t0 ≤ m1 / 8 := by have := Finset.mem_range.mp ht0; omega
      have hchar0 := (hd_props t0 ht0m).2.2.2.2.2
      -- Any t < T with dOf (stepU t) = dOf (stepU t0) has HOf (stepU t) = H0
      have hHeq : ∀ t < T, dOf (stepU t) = dOf (stepU t0) → HOf (stepU t) = H0 := by
        intro t htT heqd
        have hchart := (hd_props t (by omega)).2.2.2.2.2
        ext y
        have hy : ((y.val : ℕ) : ZMod b) = y := ZMod.natCast_zmod_val y
        rw [← hy, hchart, hchar0, heqd]
      let f : ℕ → ℕ := fun t => (subsetSumMod b ((stepU t).filter (fun a : ℕ => (a : ZMod b) ∈ H0))).card
      have hf0 : 1 ≤ f 0 := Finset.card_pos.mpr ⟨0, zero_mem_subsetSumMod b _⟩
      have hfT : f T ≤ b := by dsimp [f]; exact (Finset.card_le_univ _).trans (by rw [ZMod.card])
      have hmono : ∀ t1 t2, t1 ≤ t2 → f t1 ≤ f t2 := fun t1 t2 h12 =>
        Finset.card_le_card (subsetSumMod_mono b (Finset.filter_subset_filter _ (hstepU_mono t1 t2 h12)))
      have hSsub : Gsteps.filter (fun t => dOf (stepU t) = dOf (stepU t0)) ⊆ Finset.range T :=
        fun t ht => (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
      have hSstep : ∀ t ∈ Gsteps.filter (fun t => dOf (stepU t) = dOf (stepU t0)),
          3 * f t ≤ 2 * f (t + 1) := by
        intro t ht
        obtain ⟨htG, hdeq⟩ := Finset.mem_filter.mp ht
        obtain ⟨htR, hgrow⟩ := Finset.mem_filter.mp htG
        have htT := Finset.mem_range.mp htR
        have htm : t ≤ m1 / 8 := by omega
        have hHt : HOf (stepU t) = H0 := hHeq t htT hdeq
        have hne : (remOf (stepU t)).Nonempty := (hR_ge t htm).2
        have hex := hGrowth_step t htm hgrow
        set a := pickElem (stepU t) hne
        have ha_spec : a ∈ remOf (stepU t) ∧
            (SHOf (stepU t)).card ≤ 2 * (((a : ZMod b) +ᵥ SHOf (stepU t)) \ SHOf (stepU t)).card := by
          dsimp [a, pickElem]
          rw [if_pos hgrow, dif_pos hex]
          exact Classical.choose_spec hex
        have ha_notU : a ∉ stepU t := (Finset.mem_sdiff.mp ha_spec.1).2
        have ha_H0 : (a : ZMod b) ∈ H0 := by
          rw [← hHt]
          exact AddSubgroup.subset_closure (Finset.mem_image_of_mem _ ha_spec.1)
        have hU_next : stepU (t + 1) = insert a (stepU t) := by
          rw [hstepU_succ, dif_pos hne]
        have hfilt_next : (stepU (t + 1)).filter (fun x : ℕ => (x : ZMod b) ∈ H0) =
            insert a ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0)) := by
          rw [hU_next, Finset.filter_insert, if_pos ha_H0]
        have ha_notF : a ∉ (stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0) := fun h =>
          ha_notU (Finset.mem_filter.mp h).1
        have hS_next : subsetSumMod b ((stepU (t + 1)).filter (fun x : ℕ => (x : ZMod b) ∈ H0)) =
            subsetSumMod b ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0)) ∪
              ((a : ZMod b) +ᵥ subsetSumMod b ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0))) := by
          rw [hfilt_next, subsetSumMod_insert_eq b a _ ha_notF]
        have hf_next : f (t + 1) = f t +
            (((a : ZMod b) +ᵥ subsetSumMod b ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0))) \
              subsetSumMod b ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0))).card := by
          dsimp [f]
          rw [hS_next, ← Finset.union_sdiff_self_eq_union,
            Finset.card_union_of_disjoint Finset.disjoint_sdiff]
        have hSH_eq : SHOf (stepU t) = subsetSumMod b ((stepU t).filter (fun x : ℕ => (x : ZMod b) ∈ H0)) := by
          dsimp [SHOf]; rw [hHt]
        rw [hSH_eq] at ha_spec
        have hspec2 := ha_spec.2
        dsimp [f] at hf_next ⊢
        omega
      exact Nat.le_of_lt (card_growth_steps_lt (lt_two_pow_log2P (n := b)) f hf0 hfT hmono _ hSsub hSstep)
    calc Gsteps.card
        = ∑ d ∈ Dvals, (Gsteps.filter (fun t => dOf (stepU t) = d)).card :=
          Finset.card_eq_sum_card_fiberwise (fun t ht =>
            Finset.mem_image_of_mem _ (Finset.mem_filter.mp ht).1)
      _ ≤ ∑ _d ∈ Dvals, (2 * L) := Finset.sum_le_sum hfib
      _ = Dvals.card * (2 * L) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ L * (2 * L) := Nat.mul_le_mul_right _ hDvals_le
      _ = 2 * L ^ 2 := by ring
  -- Claim 3: Unsaturated phase step gains ≥ R.card / 528
  have hClaim3 : ∀ t ≤ m1 / 8, isUnsat (stepU t) →
      (ROf (stepU t)).card ≤ 528 * ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card) := by
    intro t htm ⟨hnotGrow, u0, hu0ne, hu0lt⟩
    set U := stepU t
    set R := ROf U
    set H := HOf U
    set Su := sliceOf U u0
    have hRge : m1 / 8 ≤ R.card := (hR_ge t htm).1
    have hne : (remOf U).Nonempty := (hR_ge t htm).2
    have hSu_gt : R.card < 128 * Su.card := by
      by_contra hle; push Not at hle
      exact hnotGrow ⟨u0, hu0ne, hle⟩
    have hSu_ge6 : 6 ≤ Su.card := by omega
    have hRpos : 0 < R.card := by omega
    set ki := 4 * Su.card / R.card + 1
    have hki_ge1 : 1 ≤ ki := Nat.le_add_left 1 _
    have hki_gt : 4 * Su.card < ki * R.card := by
      have := Nat.lt_mul_div_succ (4 * Su.card) hRpos
      dsimp [ki]; rwa [mul_comm R.card] at this
    have hki_le : ki * R.card ≤ 132 * Su.card := by
      have h1 : (4 * Su.card / R.card) * R.card ≤ 4 * Su.card := Nat.div_mul_le_self _ _
      calc ki * R.card = (4 * Su.card / R.card) * R.card + R.card := by dsimp [ki]; ring
        _ ≤ 4 * Su.card + 128 * Su.card := by omega
        _ = 132 * Su.card := by ring
    -- Define P = {a ∈ subFinset H | 4 * ki * |(a +ᵥ Su) \ Su| < Su.card}
    set P : Finset (ZMod b) := (subFinset H).filter (fun a => 4 * ki * ((a +ᵥ Su) \ Su).card < Su.card)
    have h0P : (0 : ZMod b) ∈ P := by
      refine Finset.mem_filter.mpr ⟨mem_subFinset.mpr H.zero_mem, ?_⟩
      simp only [zero_vadd, Finset.sdiff_self, Finset.card_empty, mul_zero]
      omega
    have hPsubH : P ⊆ subFinset H := Finset.filter_subset _ _
    have hex_outside : ∃ a ∈ remOf U, (a : ZMod b) ∉ P := by
      by_contra hall
      push Not at hall
      have hRsubP : R ⊆ P := by
        intro z hz
        obtain ⟨a, harem, rfl⟩ := Finset.mem_image.mp hz
        exact hall a harem
      have hgen : H ≤ AddSubgroup.closure (P : Set (ZMod b)) :=
        AddSubgroup.closure_mono (by intro z hz; exact hRsubP hz)
      have hcos := h_cos_sub H P h0P hPsubH hgen ki hki_ge1
      set kP := finsetListSum (List.replicate ki P)
      -- Bound kP.card ≤ 2 * Su.card via Lemma 2.7 + Lemma 2.6
      have hkP_le : kP.card ≤ 2 * Su.card := by
        set d0 := (Su.card - 1) / 4
        have hd0le : d0 ≤ Su.card := by omega
        have hkP_sub : kP ⊆ Finset.univ.filter (fun x : ZMod b => ((x +ᵥ Su) \ Su).card ≤ d0) := by
          intro x hx
          obtain ⟨Ls, hLlen, hLsP, rfl⟩ := exists_list_of_mem_finsetListSum_replicate hx
          have h27 := h_sdiff_list Su Ls
          have hsum_lt : 4 * ki * (Ls.map (fun y => ((y +ᵥ Su) \ Su).card)).sum < ki * Su.card := by
            have haux : ∀ (M : List (ZMod b)), (∀ y ∈ M, 4 * ki * ((y +ᵥ Su) \ Su).card < Su.card) →
                M ≠ [] → 4 * ki * (M.map (fun y => ((y +ᵥ Su) \ Su).card)).sum < M.length * Su.card := by
              intro M
              induction M with
              | nil => intro _ hne'; contradiction
              | cons y M ihM =>
                intro hM _
                have hy := hM y (by simp)
                cases M with
                | nil => simpa using hy
                | cons z M' =>
                  have hih := ihM (fun w hw => hM w (by simp [hw])) (List.cons_ne_nil _ _)
                  simp only [List.map_cons, List.sum_cons, List.length_cons] at hih ⊢
                  linarith
            have hLsne : Ls ≠ [] := by intro h; rw [h] at hLlen; simp at hLlen
            have h := haux Ls (fun y hy => (Finset.mem_filter.mp (hLsP y hy)).2) hLsne
            rwa [hLlen] at h
          have h4lt : 4 * ((Ls.sum +ᵥ Su) \ Su).card < Su.card := by
            have h1 : 4 * ki * ((Ls.sum +ᵥ Su) \ Su).card < ki * Su.card :=
              lt_of_le_of_lt (Nat.mul_le_mul_left _ h27) hsum_lt
            have h2 : ki * (4 * ((Ls.sum +ᵥ Su) \ Su).card) < ki * Su.card := by linarith
            exact Nat.lt_of_mul_lt_mul_left h2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
        have h26 := h_small_growth Su d0 hd0le
        set Gd := Finset.univ.filter (fun x : ZMod b => ((x +ᵥ Su) \ Su).card ≤ d0)
        have hGd_le : Gd.card ≤ 2 * Su.card := by
          have hdiff : Su.card ≤ 2 * (Su.card - d0) := by omega
          have h1 : Gd.card * Su.card ≤ Gd.card * (2 * (Su.card - d0)) := Nat.mul_le_mul_left _ hdiff
          have h2 : Gd.card * (2 * (Su.card - d0)) = 2 * (Gd.card * (Su.card - d0)) := by ring
          have h3 : 2 * (Gd.card * (Su.card - d0)) ≤ 2 * (Su.card * Su.card) := Nat.mul_le_mul_left 2 h26
          have h4 : Gd.card * Su.card ≤ (2 * Su.card) * Su.card := by linarith
          exact Nat.le_of_mul_le_mul_right h4 (by omega)
        exact (Finset.card_le_card hkP_sub).trans hGd_le
      rcases hcos with hbig | hlin
      · omega
      · have hRleP : R.card ≤ P.card := Finset.card_le_card hRsubP
        have h1 : ki * R.card ≤ ki * P.card := Nat.mul_le_mul_left ki hRleP
        omega
    -- Show every a ∈ remOf U with (a : ZMod b) ∉ P achieves gain ≥ R.card / 528 on SOf U
    have hex_good : ∃ a ∈ remOf U, R.card ≤ 528 * (((a : ZMod b) +ᵥ SOf U) \ SOf U).card := by
      obtain ⟨a, harem, hanotP⟩ := hex_outside
      refine ⟨a, harem, ?_⟩
      have haH : (a : ZMod b) ∈ H := AddSubgroup.subset_closure (Finset.mem_image_of_mem _ harem)
      have hge_Su : Su.card ≤ 4 * ki * (((a : ZMod b) +ᵥ Su) \ Su).card := by
        by_contra hlt; push Not at hlt
        exact hanotP (Finset.mem_filter.mpr ⟨mem_subFinset.mpr haH, hlt⟩)
      have hsub_sdiff : ((a : ZMod b) +ᵥ Su) \ Su ⊆ ((a : ZMod b) +ᵥ SOf U) \ SOf U := by
        intro z hz
        obtain ⟨hzv, hznotSu⟩ := Finset.mem_sdiff.mp hz
        obtain ⟨y, hySu, rfl⟩ := Finset.mem_vadd_finset.mp hzv
        obtain ⟨hyS, hyuH⟩ := Finset.mem_filter.mp hySu
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_vadd_finset.mpr ⟨y, hyS, rfl⟩, ?_⟩
        intro hzS
        apply hznotSu
        refine Finset.mem_filter.mpr ⟨hzS, ?_⟩
        have heq : ((a : ZMod b) +ᵥ y) - u0 = (a : ZMod b) + (y - u0) := by rw [vadd_eq_add]; abel
        rw [heq]
        exact H.add_mem haH hyuH
      have hgain_le : (((a : ZMod b) +ᵥ Su) \ Su).card ≤ (((a : ZMod b) +ᵥ SOf U) \ SOf U).card :=
        Finset.card_le_card hsub_sdiff
      set g := (((a : ZMod b) +ᵥ SOf U) \ SOf U).card
      have h1 : R.card * Su.card ≤ R.card * (4 * ki * g) :=
        Nat.mul_le_mul_left _ (hge_Su.trans (Nat.mul_le_mul_left _ hgain_le))
      have h2 : R.card * (4 * ki * g) = 4 * (ki * R.card) * g := by ring
      have h3 : 4 * (ki * R.card) * g ≤ 4 * (132 * Su.card) * g :=
        Nat.mul_le_mul_right g (Nat.mul_le_mul_left 4 hki_le)
      have h4 : R.card * Su.card ≤ (528 * g) * Su.card := by linarith
      exact Nat.le_of_mul_le_mul_right h4 (by omega)
    set a := pickElem U hne
    have ha_spec : a ∈ remOf U ∧ R.card ≤ 528 * (((a : ZMod b) +ᵥ SOf U) \ SOf U).card := by
      dsimp [a, pickElem]
      rw [if_neg hnotGrow, dif_pos hex_good]
      exact Classical.choose_spec hex_good
    have ha_notU : a ∉ U := (Finset.mem_sdiff.mp ha_spec.1).2
    have hU_next : stepU (t + 1) = insert a U := by rw [hstepU_succ, dif_pos hne]
    have hS_next : SOf (stepU (t + 1)) = SOf U ∪ ((a : ZMod b) +ᵥ SOf U) := by
      dsimp [SOf]
      rw [hU_next, subsetSumMod_insert_eq b a U ha_notU]
      ext z
      simp only [Finset.mem_add, Finset.mem_union, Finset.mem_vadd_finset, vadd_eq_add]
      constructor
      · rintro ⟨x, hx, y, hy | ⟨w, hw, rfl⟩, rfl⟩
        · left; exact ⟨x, hx, y, hy, rfl⟩
        · right; exact ⟨x + w, ⟨x, hx, w, hw, rfl⟩, by abel⟩
      · rintro (⟨x, hx, y, hy, rfl⟩ | ⟨_, ⟨x, hx, w, hw, rfl⟩, rfl⟩)
        · exact ⟨x, hx, y, Or.inl hy, rfl⟩
        · exact ⟨x, hx, (a : ZMod b) + w, Or.inr ⟨w, hw, rfl⟩, by abel⟩
    have hcard_next : (SOf (stepU (t + 1))).card = (SOf U).card + (((a : ZMod b) +ᵥ SOf U) \ SOf U).card := by
      rw [hS_next, ← Finset.union_sdiff_self_eq_union, Finset.card_union_of_disjoint Finset.disjoint_sdiff]
    have hsub_eq : (SOf (stepU (t + 1))).card - (SOf U).card = (((a : ZMod b) +ᵥ SOf U) \ SOf U).card := by
      omega
    rw [hsub_eq]
    exact ha_spec.2
  -- Claim 4: For any t ≤ m1 / 8, every coset slice u of HOf (stepU t) is nonempty
  have hClaim4 : ∀ t ≤ m1 / 8, ∀ u : ZMod b, (sliceOf (stepU t) u).Nonempty := by
    intro t htm u
    obtain ⟨hd_dvd, hd_pos, hmul, hd_ub, htop, hchar⟩ := hd_props t htm
    have hinit_ne : A_init.Nonempty := by
      have hpos : 0 < (A_init ∩ A_inj).card := by omega
      obtain ⟨s0, hs0⟩ := Finset.card_pos.mp hpos
      exact ⟨s0, (Finset.mem_inter.mp hs0).1⟩
    obtain ⟨s0, hs0⟩ := hinit_ne
    set dt := dOf (stepU t)
    haveI : NeZero dt := ⟨Nat.ne_of_gt hd_pos⟩
    have hUdiv : ∀ d' : ℕ, d' ∣ dt → 1 < d' → d' - 1 ≤ ((stepU t).filter (fun a => ¬ d' ∣ a)).card := by
      intro d' hd'dvd hd'1
      have hd'b : d' ∣ b := hd'dvd.trans hd_dvd
      have hd'ub : d' ≤ 8 * b / m1 := (Nat.le_of_dvd hd_pos hd'dvd).trans hd_ub
      have hwd := hwork_div d' hd'b (by omega) hd'ub
      have hsub : A_work.filter (fun a => ¬ d' ∣ a) ⊆ (stepU t).filter (fun a => ¬ d' ∣ a) := by
        intro a ha
        obtain ⟨haW, hnd'⟩ := Finset.mem_filter.mp ha
        refine Finset.mem_filter.mpr ⟨?_, hnd'⟩
        exact Classical.byContradiction fun hanotU => by
          have harem : a ∈ remOf (stepU t) := Finset.mem_sdiff.mpr ⟨haW, hanotU⟩
          have haH : (a : ZMod b) ∈ HOf (stepU t) :=
            AddSubgroup.subset_closure (Finset.mem_image_of_mem _ harem)
          have hdt_dvd : dt ∣ a := (hchar a).mp haH
          exact hnd' (hd'dvd.trans hdt_dvd)
      have hle := Finset.card_le_card hsub
      omega
    have huniv : subsetSumMod dt (stepU t) = Finset.univ := h_ssm_univ (stepU t) hUdiv
    set r : ℕ := (u - (s0 : ZMod b)).val
    have hr_cast : (r : ZMod b) = u - (s0 : ZMod b) := ZMod.natCast_zmod_val _
    have hmem_univ : (r : ZMod dt) ∈ subsetSumMod dt (stepU t) := huniv ▸ Finset.mem_univ _
    obtain ⟨S, hSU, hSeq⟩ := Finset.mem_image.mp hmem_univ
    have hmod_eq : S.sum id ≡ r [MOD dt] := (ZMod.natCast_eq_natCast_iff (S.sum id) r dt).mp hSeq
    have hdiff_H : ((S.sum id : ℕ) : ZMod b) - (r : ZMod b) ∈ HOf (stepU t) := by
      rcases le_total (S.sum id) r with hle | hge
      · have hdvd : dt ∣ r - S.sum id := (Nat.modEq_iff_dvd' hle).mp hmod_eq
        have hmem := (hchar (r - S.sum id)).mpr hdvd
        have heq : ((S.sum id : ℕ) : ZMod b) - (r : ZMod b) = -(((r - S.sum id : ℕ) : ZMod b)) := by
          rw [Nat.cast_sub hle]; abel
        rw [heq]
        exact (HOf (stepU t)).neg_mem hmem
      · have hdvd : dt ∣ S.sum id - r := (Nat.modEq_iff_dvd' hge).mp hmod_eq.symm
        have hmem := (hchar (S.sum id - r)).mpr hdvd
        rw [Nat.cast_sub hge] at hmem
        exact hmem
    refine ⟨(s0 : ZMod b) + ((S.sum id : ℕ) : ZMod b), Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_add.mpr ⟨(s0 : ZMod b), Finset.mem_image_of_mem _ hs0,
        ((S.sum id : ℕ) : ZMod b), Finset.mem_image.mpr ⟨S, hSU, rfl⟩, rfl⟩
    · have heq : (s0 : ZMod b) + ((S.sum id : ℕ) : ZMod b) - u =
          ((S.sum id : ℕ) : ZMod b) - (r : ZMod b) := by
        rw [hr_cast]; abel
      rw [heq]
      exact hdiff_H
  -- Final assembly: consider T = min (m1 / 8) k
  set T := min (m1 / 8) k
  have hTm : T ≤ m1 / 8 := min_le_left _ _
  have hTk : T ≤ k := min_le_right _ _
  have hS_mono_t : ∀ t1 t2, t1 ≤ t2 → (SOf (stepU t1)).card ≤ (SOf (stepU t2)).card := fun t1 t2 h12 =>
    Finset.card_le_card (Finset.add_subset_add_left (subsetSumMod_mono b (hstepU_mono t1 t2 h12)))
  by_cases hsat : ∃ t < T, isSat (stepU t)
  · -- Saturated phase at some t < T: double count over all u : ZMod b gives b ≤ 4 * |SOf (stepU t)|
    obtain ⟨t, htT, hnotGrow, hnotUnsat⟩ := hsat
    have htm : t ≤ m1 / 8 := by omega
    have hall_ge : ∀ u : ZMod b, (subFinset (HOf (stepU t))).card ≤ 4 * (sliceOf (stepU t) u).card := by
      intro u
      by_contra hlt; push Not at hlt
      exact hnotUnsat ⟨hnotGrow, u, hClaim4 t htm u, hlt⟩
    have hdouble : ∑ u : ZMod b, (sliceOf (stepU t) u).card =
        (SOf (stepU t)).card * (subFinset (HOf (stepU t))).card := by
      have h1 : ∀ u : ZMod b, (sliceOf (stepU t) u).card =
          ∑ x ∈ SOf (stepU t), if x - u ∈ HOf (stepU t) then 1 else 0 := fun u => by
        rw [Finset.card_filter]
      simp_rw [h1]
      rw [Finset.sum_comm]
      have hinner : ∀ x ∈ SOf (stepU t),
          (∑ u : ZMod b, if x - u ∈ HOf (stepU t) then 1 else 0) = (subFinset (HOf (stepU t))).card := by
        intro x _
        rw [← Finset.card_filter]
        refine Finset.card_bij (fun u _ => x - u) ?_ ?_ ?_
        · intro u hu; exact mem_subFinset.mpr (Finset.mem_filter.mp hu).2
        · intro u1 _ u2 _ heq; exact sub_right_inj.mp heq
        · intro h hh
          exact ⟨x - h, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
            simpa [sub_sub_cancel] using mem_subFinset.mp hh⟩, sub_sub_cancel x h⟩
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, smul_eq_mul]
    have hsum_ge : b * (subFinset (HOf (stepU t))).card ≤ 4 * ∑ u : ZMod b, (sliceOf (stepU t) u).card := by
      calc b * (subFinset (HOf (stepU t))).card
          = ∑ _u : ZMod b, (subFinset (HOf (stepU t))).card := by
            rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        _ ≤ ∑ u : ZMod b, (4 * (sliceOf (stepU t) u).card) := Finset.sum_le_sum fun u _ => hall_ge u
        _ = 4 * ∑ u : ZMod b, (sliceOf (stepU t) u).card := (Finset.mul_sum _ _ _).symm
    rw [hdouble] at hsum_ge
    have hHpos : 0 < (subFinset (HOf (stepU t))).card := Finset.card_pos.mpr ⟨0, mem_subFinset.mpr (HOf _).zero_mem⟩
    have hb_le : b ≤ 4 * (SOf (stepU t)).card := by
      have : b * (subFinset (HOf (stepU t))).card ≤ (4 * (SOf (stepU t)).card) * (subFinset (HOf (stepU t))).card := by
        linarith
      exact Nat.le_of_mul_le_mul_right this hHpos
    have hSle : (SOf (stepU t)).card ≤ (subsetSumModLe b (k + 1) A).card := by
      have h1 := hS_mono_t t k (by omega)
      have h2 := Finset.card_le_card (hS_sub_modLe k)
      exact h1.trans h2
    exact (min_le_right _ _).trans (by omega)
  · -- No saturated phase for t < T: at least T / 2 steps are unsaturated
    push Not at hsat
    set Usteps := (Finset.range T).filter (fun t => isUnsat (stepU t))
    set Gsteps := (Finset.range T).filter (fun t => isGrowth (stepU t))
    have hUsteps_ge : T / 2 ≤ Usteps.card := by
      have hpart : Usteps.card + Gsteps.card = T := by
        have hdisj : Disjoint Usteps Gsteps := by
          rw [Finset.disjoint_left]
          intro t htU htG
          exact (Finset.mem_filter.mp htU).2.1 (Finset.mem_filter.mp htG).2
        have hunion : Usteps ∪ Gsteps = Finset.range T := by
          ext t
          simp only [Usteps, Gsteps, Finset.mem_union, Finset.mem_filter, Finset.mem_range]
          constructor
          · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
          · intro htT
            by_cases hg : isGrowth (stepU t)
            · right; exact ⟨htT, hg⟩
            · left
              have hnotSat := hsat t htT
              have huns : isUnsat (stepU t) := by
                by_contra hnu; exact hnotSat ⟨hg, hnu⟩
              exact ⟨htT, huns⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_range]
      by_cases hTsmall : T ≤ 200 * L ^ 2
      · have hG0 : Gsteps.card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro t ht
          obtain ⟨htT, hgrow⟩ := Finset.mem_filter.mp ht
          have htR := Finset.mem_range.mp htT
          exact hClaim1 t (by omega) (by omega) hgrow
        omega
      · have hG2 : Gsteps.card ≤ 2 * L ^ 2 := hClaim2 T hTm
        omega
    -- Telescoping sum of gains over unsaturated steps
    have htel : ∑ t ∈ Finset.range T, ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card) ≤
        (SOf (stepU T)).card := by
      have haux : ∀ n, ∑ t ∈ Finset.range n, ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card) +
          (SOf (stepU 0)).card = (SOf (stepU n)).card := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn =>
          rw [Finset.sum_range_succ]
          have hle := hS_mono_t n (n + 1) (Nat.le_succ n)
          omega
      have := haux T
      omega
    have hgain_sum : Usteps.card * (m1 / 8) ≤ 528 * (SOf (stepU T)).card := by
      calc Usteps.card * (m1 / 8)
          = ∑ _t ∈ Usteps, (m1 / 8) := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ t ∈ Usteps, (528 * ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card)) := by
            apply Finset.sum_le_sum
            intro t ht
            obtain ⟨htR, huns⟩ := Finset.mem_filter.mp ht
            have htm : t ≤ m1 / 8 := by have := Finset.mem_range.mp htR; omega
            exact (hR_ge t htm).1.trans (hClaim3 t htm huns)
        _ = 528 * ∑ t ∈ Usteps, ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card) :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ 528 * ∑ t ∈ Finset.range T, ((SOf (stepU (t + 1))).card - (SOf (stepU t)).card) :=
            Nat.mul_le_mul_left 528 (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
        _ ≤ 528 * (SOf (stepU T)).card := Nat.mul_le_mul_left 528 htel
    have hSle : (SOf (stepU T)).card ≤ (subsetSumModLe b (k + 1) A).card :=
      (hS_mono_t T k hTk).trans (Finset.card_le_card (hS_sub_modLe k))
    have hprod_ge : (T / 2) * (m1 / 8) ≤ 528 * (subsetSumModLe b (k + 1) A).card := by
      calc (T / 2) * (m1 / 8) ≤ Usteps.card * (m1 / 8) := Nat.mul_le_mul_right _ hUsteps_ge
        _ ≤ 528 * (SOf (stepU T)).card := hgain_sum
        _ ≤ 528 * (subsetSumModLe b (k + 1) A).card := Nat.mul_le_mul_left 528 hSle
    rcases le_total (m1 / 8) k with hmk | hkm
    · have hTeq : T = m1 / 8 := min_eq_left hmk
      rw [hTeq] at hprod_ge
      have h1 : m1 * m1 / 131072 ≤ (subsetSumModLe b (k + 1) A).card := by
        have hm8 : m1 ≤ 9 * (m1 / 8) := by omega
        have hm16 : m1 / 8 ≤ 3 * (m1 / 8 / 2) := by omega
        have hsq : m1 * m1 ≤ 131072 * (subsetSumModLe b (k + 1) A).card := by
          calc m1 * m1 ≤ (9 * (m1 / 8)) * (9 * (m1 / 8)) := Nat.mul_le_mul hm8 hm8
            _ = 81 * ((m1 / 8) * (m1 / 8)) := by ring
            _ ≤ 81 * ((3 * (m1 / 8 / 2)) * (m1 / 8)) := Nat.mul_le_mul_left 81 (Nat.mul_le_mul_right _ hm16)
            _ = 243 * ((m1 / 8 / 2) * (m1 / 8)) := by ring
            _ ≤ 243 * (528 * (subsetSumModLe b (k + 1) A).card) := Nat.mul_le_mul_left 243 hprod_ge
            _ = 128304 * (subsetSumModLe b (k + 1) A).card := by ring
            _ ≤ 131072 * (subsetSumModLe b (k + 1) A).card := Nat.mul_le_mul_right _ (by decide)
        exact (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 131072)).mpr (by omega)
      exact (min_le_left _ _).trans h1
    · have hTeq : T = k := min_eq_right hkm
      rw [hTeq] at hprod_ge
      have h1 : b / 4 ≤ (subsetSumModLe b (k + 1) A).card := by
        have hk2 : 4096 * b / m1 + 1 ≤ k / 2 := by
          dsimp [k]
          have : 8192 * b / m1 = (2 * (4096 * b)) / m1 := by congr 1; ring
          have hdiv2 : 2 * (4096 * b / m1) ≤ 8192 * b / m1 := by
            have h1 := Nat.mul_div_le_mul_div_assoc 2 (4096 * b) m1
            have h2 : 2 * (4096 * b) = 8192 * b := by ring
            rwa [h2] at h1
          omega
        have hm8 : m1 ≤ 9 * (m1 / 8) := by omega
        have hbm : 4096 * b < (4096 * b / m1 + 1) * m1 := by
          have := Nat.lt_mul_div_succ (4096 * b) (by omega : 0 < m1)
          rwa [mul_comm m1] at this
        have hb_le : 4096 * b ≤ 9 * ((k / 2) * (m1 / 8)) := by
          calc 4096 * b ≤ (4096 * b / m1 + 1) * m1 := Nat.le_of_lt hbm
            _ ≤ (k / 2) * (9 * (m1 / 8)) := Nat.mul_le_mul hk2 hm8
            _ = 9 * ((k / 2) * (m1 / 8)) := by ring
        have hfinal : 4096 * b ≤ 4752 * (subsetSumModLe b (k + 1) A).card := by
          calc 4096 * b ≤ 9 * ((k / 2) * (m1 / 8)) := hb_le
            _ ≤ 9 * (528 * (subsetSumModLe b (k + 1) A).card) := Nat.mul_le_mul_left 9 hprod_ge
            _ = 4752 * (subsetSumModLe b (k + 1) A).card := by ring
        -- Wait: 4752 > 4096 * 4? No! 4096 * 4 = 16384 >> 4752!
        -- So b ≤ (4752 / 4096) * |S| < 4 * |S|, i.e. b / 4 ≤ |S|!!
        omega
      exact (min_le_right _ _).trans h1

end Lemma62

-- Deterministic helpers
lemma split_top_k (S : Finset ℕ) (k : ℕ) (hk : k ≤ S.card) :
    ∃ Lo Hi : Finset ℕ,
      Disjoint Lo Hi ∧ Lo ∪ Hi = S ∧ Hi.card = k ∧
      ∀ x ∈ Lo, ∀ y ∈ Hi, x < y := by
  set L := S.sort (· ≤ ·)
  have hLlen : L.length = S.card := Finset.length_sort _
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  have hLpw : L.Pairwise (· ≤ ·) := Finset.pairwise_sort S (· ≤ ·)
  have hLto : L.toFinset = S := by
    ext x; simp [L, Finset.mem_sort]
  set p := S.card - k
  set LoL := L.take p
  set HiL := L.drop p
  have hLapp : LoL ++ HiL = L := List.take_append_drop p L
  have hLo_nd : LoL.Nodup := hLnd.take
  have hHi_nd : HiL.Nodup := hLnd.drop
  have hLo_len : LoL.length = p := by simp [LoL, hLlen]; omega
  have hHi_len : HiL.length = k := by simp [HiL, hLlen]; omega
  refine ⟨LoL.toFinset, HiL.toFinset, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [List.mem_toFinset] at hx1 hx2
    have hnd_app : (LoL ++ HiL).Nodup := hLapp.symm ▸ hLnd
    exact (List.nodup_append.mp hnd_app).2.2 x hx1 x hx2 rfl
  · rw [← List.toFinset_append, hLapp, hLto]
  · rw [List.toFinset_card_of_nodup hHi_nd, hHi_len]
  · intro x hx y hy
    rw [List.mem_toFinset] at hx hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    have hi_lt_p : i < p := by omega
    have hpi : i < L.length := by omega
    have hpj : p + j < L.length := by omega
    have hget1 : LoL[i] = L[i] := List.getElem_take
    have hget2 : HiL[j] = L[p + j] := List.getElem_drop
    rw [hget1, hget2]
    have hle : L[i] ≤ L[p + j] := (List.pairwise_iff_getElem.mp hLpw) i (p + j) hpi hpj (by omega)
    have hne : L[i] ≠ L[p + j] := by
      intro heq
      have hidx := (List.Nodup.getElem_inj_iff hLnd).mp heq
      omega
    exact lt_of_le_of_ne hle hne

lemma sum_distinct_pos_ge (S : Finset ℕ) (hpos : ∀ x ∈ S, 1 ≤ x) :
    S.card * (S.card + 1) ≤ 2 * S.sum id := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hSe : S = ∅
    · subst hSe; simp
    · have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSe
      set mx := S.max' hSne
      have hmx : mx ∈ S := Finset.max'_mem S hSne
      have hsub : S ⊆ Finset.Icc 1 mx := fun x hx =>
        Finset.mem_Icc.mpr ⟨hpos x hx, Finset.le_max' S x hx⟩
      have hcard_le_mx : S.card ≤ mx := by simpa using Finset.card_le_card hsub
      set S' := S.erase mx
      have hih := ih S' (Finset.erase_ssubset hmx) (fun x hx => hpos x (Finset.mem_of_mem_erase hx))
      have hcard : S.card = S'.card + 1 := (Finset.card_erase_add_one hmx).symm
      have hsum : S.sum id = S'.sum id + mx := by
        dsimp [S']
        rw [← Finset.add_sum_erase S id hmx, id_eq, add_comm]
      rw [hcard, hsum]
      have h1 : (S'.card + 1) * (S'.card + 1 + 1) = S'.card * (S'.card + 1) + 2 * (S'.card + 1) := by ring
      omega

lemma extend_interval_subsetSum (A_core A_ext : Finset ℕ) (hdisj : Disjoint A_core A_ext)
    (a Q : ℕ) (hIcc : Finset.Icc a (a + Q) ⊆ A_core.powerset.image (fun S => S.sum id))
    (hExt : ∀ x ∈ A_ext, x ≤ Q) :
    Finset.Icc a (a + Q + A_ext.sum id) ⊆ (A_core ∪ A_ext).powerset.image (fun S => S.sum id) := by
  have haux : ∀ (E : Finset ℕ), Disjoint A_core E → (∀ x ∈ E, x ≤ Q) →
      Finset.Icc a (a + Q + E.sum id) ⊆ (A_core ∪ E).powerset.image (fun S => S.sum id) := by
    intro E
    induction E using Finset.induction_on with
    | empty =>
      intro _ _
      simpa using hIcc
    | @insert x E hxE ih =>
      intro hdisj' hExt'
      have hdisjE : Disjoint A_core E :=
        hdisj'.mono_right (Finset.subset_insert x E)
      have hx_notC : x ∉ A_core := Finset.disjoint_right.mp hdisj' (Finset.mem_insert_self x E)
      have hih := ih hdisjE (fun y hy => hExt' y (Finset.mem_insert_of_mem hy))
      have hxQ : x ≤ Q := hExt' x (Finset.mem_insert_self x E)
      rw [Finset.sum_insert hxE, id_eq]
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_Icc.mp hz
      change z ≤ a + Q + (x + E.sum id) at hz2
      by_cases hle : z ≤ a + Q + E.sum id
      · have hzE := hih (Finset.mem_Icc.mpr ⟨hz1, hle⟩)
        obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hzE
        exact Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr
          ((Finset.mem_powerset.mp hS).trans (Finset.union_subset_union_right (Finset.subset_insert x E))), rfl⟩
      · have hzx : a ≤ z - x ∧ z - x ≤ a + Q + E.sum id := by omega
        have hmem := hih (Finset.mem_Icc.mpr hzx)
        obtain ⟨S, hS, hSsum⟩ := Finset.mem_image.mp hmem
        have hSsub : S ⊆ A_core ∪ E := Finset.mem_powerset.mp hS
        have hxS : x ∉ S := fun h => by
          rcases Finset.mem_union.mp (hSsub h) with hc | he
          · exact hx_notC hc
          · exact hxE he
        refine Finset.mem_image.mpr ⟨insert x S, Finset.mem_powerset.mpr ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyS
          · exact Finset.mem_union_right A_core (Finset.mem_insert_self _ E)
          · exact (Finset.union_subset_union_right (Finset.subset_insert x E)) (hSsub hyS)
        · rw [Finset.sum_insert hxS, id_eq, hSsum]
          omega
  exact haux A_ext hdisj hExt

lemma finsetListSum_ofFn_subset_powerset {r : ℕ} (P : Fin r → Finset ℕ) (S : Fin r → Finset ℕ)
    (hdisj : ∀ i j : Fin r, i ≠ j → Disjoint (P i) (P j))
    (hsub : ∀ i : Fin r, S i ⊆ (P i).powerset.image (fun T => T.sum id)) :
    finsetListSum (List.ofFn S) ⊆ ((Finset.univ.biUnion P).powerset).image (fun T => T.sum id) := by
  have haux : ∀ (L : List (Fin r)), L.Nodup →
      finsetListSum (L.map S) ⊆ ((L.toFinset.biUnion P).powerset).image (fun T => T.sum id) := by
    intro L
    induction L with
    | nil =>
      intro _ x hx
      simp only [List.map_nil, finsetListSum, Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), by simp⟩
    | cons i L ih =>
      intro hnd
      rw [List.nodup_cons] at hnd
      have hih := ih hnd.2
      intro z hz
      simp only [List.map_cons, finsetListSum] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨Tx, hTx, rfl⟩ := Finset.mem_image.mp (hsub i hx)
      obtain ⟨Ty, hTy, rfl⟩ := Finset.mem_image.mp (hih hy)
      have hTx' : Tx ⊆ P i := Finset.mem_powerset.mp hTx
      have hTy' : Ty ⊆ L.toFinset.biUnion P := Finset.mem_powerset.mp hTy
      have hTdisj : Disjoint Tx Ty := by
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        obtain ⟨j, hjL, haj⟩ := Finset.mem_biUnion.mp (hTy' ha2)
        have hne : i ≠ j := fun h => hnd.1 (h ▸ List.mem_toFinset.mp hjL)
        exact Finset.disjoint_left.mp (hdisj i j hne) (hTx' ha1) haj
      refine Finset.mem_image.mpr ⟨Tx ∪ Ty, Finset.mem_powerset.mpr ?_, ?_⟩
      · intro a ha
        rcases Finset.mem_union.mp ha with h1 | h2
        · exact Finset.mem_biUnion.mpr ⟨i, by simp, hTx' h1⟩
        · obtain ⟨j, hjL, haj⟩ := Finset.mem_biUnion.mp (hTy' h2)
          exact Finset.mem_biUnion.mpr ⟨j, by simp [List.mem_toFinset.mp hjL], haj⟩
      · rw [Finset.sum_union hTdisj]
  have h1 := haux (List.finRange r) (List.nodup_finRange r)
  have hofFn : List.ofFn S = (List.finRange r).map S := List.ofFn_eq_map
  have htoFin : (List.finRange r).toFinset = Finset.univ := by
    ext i; simp
  rw [hofFn]
  rwa [htoFin] at h1

-- Real exponential helper: n < exp(log2P n)
lemma nat_lt_exp_log2P (n : ℕ) : (n : ℝ) < Real.exp (log2P n : ℝ) := by
  have h1 : (n : ℝ) < (2 : ℝ) ^ log2P n := by exact_mod_cast (lt_two_pow_log2P (n := n))
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h3 : (2 : ℝ) ^ log2P n ≤ (Real.exp 1) ^ log2P n := pow_le_pow_left₀ (by norm_num) h2 _
  rw [← Real.exp_nat_mul, mul_one] at h3
  linarith

lemma exp_neg_four_lt : Real.exp (-4 : ℝ) < 1 / 16 := by
  rw [Real.exp_neg]
  have he : (2.5 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he2 : (6 : ℝ) < Real.exp 2 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have he4 : (16 : ℝ) < Real.exp 4 := by
    have : Real.exp 4 = Real.exp 2 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hinv : (Real.exp 4)⁻¹ < (16 : ℝ)⁻¹ := inv_strictAnti₀ (by norm_num) he4
  linarith

section Theorem61

variable
  (h_chernoff_lower : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Finset α) (C : Finset β) (_hβ : 0 < Fintype.card β),
    let p : ℝ := (C.card : ℝ) / (Fintype.card β : ℝ)
    ((Finset.univ.filter (fun f : α → β =>
        4 * ((E.filter (fun a => f a ∈ C)).card : ℝ) ≤ p * (E.card : ℝ))).card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ) / 4))
  (h_chernoff_upper : ∀ {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (E : Finset α) (C : Finset β) (_hβ : 0 < Fintype.card β),
    let p : ℝ := (C.card : ℝ) / (Fintype.card β : ℝ)
    ((Finset.univ.filter (fun f : α → β =>
        3 * p * (E.card : ℝ) ≤ ((E.filter (fun a => f a ∈ C)).card : ℝ))).card : ℝ) ≤
      (Fintype.card β : ℝ) ^ Fintype.card α * Real.exp (- p * (E.card : ℝ)))
  (h_chernoff_half : ∀ {α : Type} [Fintype α] [DecidableEq α]
    (E : Finset α) (c : Bool),
    ((Finset.univ.filter (fun f : α → Bool =>
        4 * (E.filter (fun a => f a = c)).card ≤ E.card)).card : ℝ) ≤
      (2 : ℝ) ^ Fintype.card α * Real.exp (- (E.card : ℝ) / 24))
  (h_card_union_vadd : ∀ (T : Finset ℕ) (q : ℕ), 0 < q →
    T.card + (T.image (fun x : ℕ => (x : ZMod q))).card ≤ (T ∪ (q +ᵥ T)).card)
  (h_subsetSumLe_ins : ∀ (h : ℕ) (A : Finset ℕ) (m : ℕ), m ∉ A →
    subsetSumLe h A ∪ (m +ᵥ subsetSumLe h A) ⊆ subsetSumLe (h + 1) (insert m A))
  (h_lemma_6_2 : ∀ {b : ℕ}, 2 ≤ b → ∀ (A A_inj : Finset ℕ),
    A_inj ⊆ A → (∀ x ∈ A_inj, x < b) → A.card ≤ 16 * A_inj.card →
    1600 * (log2P b) ^ 2 ≤ A_inj.card →
    (∀ d : ℕ, d ∣ b → 2 ≤ d → d ≤ 8 * b / A_inj.card →
      1200 * (log2P b) ^ 2 + 8 * d ≤ (A.filter (fun a => ¬ d ∣ a)).card) →
    let k := 8192 * b / A_inj.card + 2
    min (A_inj.card * A_inj.card / 131072) (b / 4) ≤ (subsetSumModLe b (k + 1) A).card)
  (h_lemma_6_3 : ∀ {ℓ n : ℕ}, 1 ≤ ℓ → 2 ≤ n → ∀ (A : Finset ℕ),
    A ⊆ Finset.Icc 1 n →
    200000 * ℓ * (log2P n) ^ 3 + 1048576 * ℓ ^ 2 * n / A.card + 100 ≤ A.card / 4 →
    ∃ d_tot : ℕ, ∃ A' : Finset ℕ,
      1 ≤ d_tot ∧ d_tot ≤ 3 * n / A.card ∧
      IsNice ℓ n A.card A' ∧
      A.card / 2 ≤ A'.card ∧
      (∀ x ∈ A', 1 ≤ x ∧ d_tot * x ∈ A))
  (h_weak_lev : ∀ {α_inv Q : ℕ}, 1 ≤ α_inv → 4 * α_inv ≤ Q →
    ∀ (S : Fin (2 * (16 * α_inv * (4 * α_inv))) → Finset ℕ),
    (∀ j, S j ⊆ Finset.Icc 0 Q) →
    (∀ j, 0 ∈ S j) →
    (∀ j, Q ≤ α_inv * (S j).card) →
    (∀ j, ∀ d ≥ 2, ∃ x ∈ S j, ¬ d ∣ x) →
    ∃ a : ℕ, 0 < a ∧ a ≤ (16 * α_inv * (4 * α_inv)) * Q ∧
      Finset.Icc a (a + Q) ⊆ finsetListSum (List.ofFn S))

-- Claim 1 iteration helper: adding B2 one element at a time using Lemma 2.5
include h_card_union_vadd h_subsetSumLe_ins in
lemma card_subsetSumLe_iter_vadd (B1 B2 : Finset ℕ) (hdisj : Disjoint B1 B2) (h1 : ℕ)
    (g : ℕ → ℕ) (hg : ∀ b ∈ B2, 0 < b ∧ g b ≤ (subsetSumModLe b h1 B1).card) :
    ∑ b ∈ B2, g b ≤ (subsetSumLe (h1 + B2.card) (B1 ∪ B2)).card := by
  induction B2 using Finset.induction_on with
  | empty => simp
  | @insert b B2 hbB2 ih =>
    have hdisj' : Disjoint B1 B2 := hdisj.mono_right (Finset.subset_insert b B2)
    have hb_notB1 : b ∉ B1 := Finset.disjoint_right.mp hdisj (Finset.mem_insert_self b B2)
    have hb_notU : b ∉ B1 ∪ B2 := fun h => (Finset.mem_union.mp h).elim hb_notB1 hbB2
    have hih := ih hdisj' (fun x hx => hg x (Finset.mem_insert_of_mem hx))
    obtain ⟨hbpos, hgb⟩ := hg b (Finset.mem_insert_self b B2)
    set T := subsetSumLe (h1 + B2.card) (B1 ∪ B2)
    have hB1subT : subsetSumLe h1 B1 ⊆ T := by
      intro x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hSp, hSc⟩ := Finset.mem_filter.mp hS
      exact Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hSp).trans Finset.subset_union_left),
          by omega⟩, rfl⟩
    have hmod_le : (subsetSumModLe b h1 B1).card ≤ (T.image (fun x : ℕ => (x : ZMod b))).card :=
      Finset.card_le_card (Finset.image_subset_image hB1subT)
    have h25 := h_card_union_vadd T b hbpos
    have hins : T ∪ (b +ᵥ T) ⊆ subsetSumLe (h1 + B2.card + 1) (insert b (B1 ∪ B2)) :=
      h_subsetSumLe_ins (h1 + B2.card) (B1 ∪ B2) b hb_notU
    have hunion_eq : insert b (B1 ∪ B2) = B1 ∪ insert b B2 := by
      ext x; simp [or_left_comm]
    have hcard_eq : h1 + (insert b B2).card = h1 + B2.card + 1 := by
      rw [Finset.card_insert_of_notMem hbB2]; omega
    rw [Finset.sum_insert hbB2, hcard_eq, ← hunion_eq]
    have hle_ins := Finset.card_le_card hins
    omega

-- Step 1: Split nice set A' = A_core ⊔ A_ext preserving divisibility and dyadic density
include h_chernoff_half in
lemma split_nice_set {ℓ n m : ℕ} (hℓ : 1 ≤ ℓ) (hn : 2 ≤ n)
    (hL100 : 100 ≤ log2P n) (hm_big : 10000 * ℓ * log2P n ≤ m)
    (A' : Finset ℕ) (hA'_card : m / 2 ≤ A'.card) (hNice : IsNice ℓ n m A') :
    ∃ A_core A_ext : Finset ℕ,
      Disjoint A_core A_ext ∧ A_core ∪ A_ext = A' ∧
      m / 8 ≤ A_core.card ∧ m / 8 ≤ A_ext.card ∧
      (∀ d : ℕ, 2 ≤ d → d ≤ 1024 * ℓ * n / m →
        16000 * ℓ * (log2P n) ^ 2 + 128 * ℓ * d ≤ (A_core.filter (fun a => ¬ d ∣ a)).card) ∧
      (∀ j : ℕ, j < log2P n →
        (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).Nonempty →
        64 * ℓ * log2P n ≤ (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card) := by
  set L := log2P n
  change 10000 * ℓ * L ≤ m at hm_big
  have h10000 : 10000 * ℓ * L = 2 * (5000 * ℓ * L) := by ring
  have hA'_ge : 5000 * ℓ * L ≤ A'.card := by omega
  let D_set : Finset ℕ := Finset.Icc 2 (1024 * ℓ * n / m)
  let J_set : Finset ℕ := (Finset.range L).filter (fun j =>
    (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).Nonempty)
  let bad_core : Finset (A' → Bool) := Finset.univ.filter (fun f =>
    4 * (Finset.univ.filter (fun x : A' => f x = true)).card ≤ (Finset.univ : Finset A').card)
  let bad_ext : Finset (A' → Bool) := Finset.univ.filter (fun f =>
    4 * (Finset.univ.filter (fun x : A' => f x = false)).card ≤ (Finset.univ : Finset A').card)
  let bad_div (d : ℕ) : Finset (A' → Bool) :=
    let Ed : Finset A' := Finset.univ.filter (fun x : A' => ¬ d ∣ x.1)
    Finset.univ.filter (fun f => 4 * (Ed.filter (fun x => f x = true)).card ≤ Ed.card)
  let bad_dyad (j : ℕ) : Finset (A' → Bool) :=
    let Ej : Finset A' := Finset.univ.filter (fun x : A' => 2 ^ j ≤ x.1 ∧ x.1 < 2 ^ (j + 1))
    Finset.univ.filter (fun f => 4 * (Ej.filter (fun x => f x = true)).card ≤ Ej.card)
  let all_bad : Finset (A' → Bool) :=
    bad_core ∪ bad_ext ∪ D_set.biUnion bad_div ∪ J_set.biUnion bad_dyad
  have hbad_lt : (all_bad.card : ℝ) < (2 : ℝ) ^ Fintype.card A' := by
    have hcu : all_bad.card ≤ bad_core.card + bad_ext.card +
        ∑ d ∈ D_set, (bad_div d).card + ∑ j ∈ J_set, (bad_dyad j).card := by
      calc all_bad.card
          ≤ (bad_core ∪ bad_ext ∪ D_set.biUnion bad_div).card + (J_set.biUnion bad_dyad).card :=
            Finset.card_union_le _ _
        _ ≤ ((bad_core ∪ bad_ext).card + (D_set.biUnion bad_div).card) + (J_set.biUnion bad_dyad).card :=
            Nat.add_le_add_right (Finset.card_union_le _ _) _
        _ ≤ (bad_core.card + bad_ext.card + ∑ d ∈ D_set, (bad_div d).card) +
              ∑ j ∈ J_set, (bad_dyad j).card :=
            Nat.add_le_add (Nat.add_le_add (Finset.card_union_le _ _) Finset.card_biUnion_le)
              Finset.card_biUnion_le
    have hcuR : (all_bad.card : ℝ) ≤ (bad_core.card : ℝ) + (bad_ext.card : ℝ) +
        (∑ d ∈ D_set, ((bad_div d).card : ℝ)) + (∑ j ∈ J_set, ((bad_dyad j).card : ℝ)) := by
      exact_mod_cast hcu
    have hcardU : (Finset.univ : Finset A').card = A'.card := by simp
    have hcore_le : (bad_core.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) := by
      have h1 := h_chernoff_half (Finset.univ : Finset A') true
      have h2 : Real.exp (- ((Finset.univ : Finset A').card : ℝ) / 24) ≤ Real.exp (-4 : ℝ) := by
        apply Real.exp_le_exp.mpr
        rw [hcardU]
        have hA100 : (500000 : ℝ) ≤ (A'.card : ℝ) := by
          have : 500000 ≤ A'.card := by nlinarith
          exact_mod_cast this
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans exp_neg_four_lt.le) (by positivity))
    have hext_le : (bad_ext.card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) := by
      have h1 := h_chernoff_half (Finset.univ : Finset A') false
      have h2 : Real.exp (- ((Finset.univ : Finset A').card : ℝ) / 24) ≤ Real.exp (-4 : ℝ) := by
        apply Real.exp_le_exp.mpr
        rw [hcardU]
        have hA100 : (500000 : ℝ) ≤ (A'.card : ℝ) := by
          have : 500000 ≤ A'.card := by nlinarith
          exact_mod_cast this
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans exp_neg_four_lt.le) (by positivity))
    have hD_sum : ∑ d ∈ D_set, ((bad_div d).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) := by
      have hterm : ∀ d ∈ D_set, ((bad_div d).card : ℝ) ≤
          (2 : ℝ) ^ Fintype.card A' * Real.exp (- (2000 * (L : ℝ) ^ 2)) := by
        intro d hd
        obtain ⟨hd2, hdub⟩ := Finset.mem_Icc.mp hd
        let Ed : Finset A' := Finset.univ.filter (fun x : A' => ¬ d ∣ x.1)
        have hEd_card : Ed.card = (A'.filter (fun a => ¬ d ∣ a)).card := by
          have hbij : Ed.image Subtype.val = A'.filter (fun a => ¬ d ∣ a) := by
            ext x
            simp only [Ed, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
            exact ⟨fun ⟨a, ha, hnd, heq⟩ => heq ▸ ⟨ha, hnd⟩, fun ⟨hx, hnd⟩ => ⟨x, hx, hnd, rfl⟩⟩
          rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
        have hEd_ge : 64000 * L ^ 2 ≤ Ed.card := by
          rw [hEd_card]
          have h1 : 64000 * ℓ * L ^ 2 + 512 * ℓ * d ≤ (A'.filter (fun a => ¬ d ∣ a)).card := hNice.1 d hd2 hdub
          have h2 : 64000 * L ^ 2 ≤ 64000 * ℓ * L ^ 2 := by
            calc 64000 * L ^ 2 = 64000 * 1 * L ^ 2 := by ring
              _ ≤ 64000 * ℓ * L ^ 2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hℓ)
          omega
        have hch := h_chernoff_half Ed true
        have hexp : Real.exp (- (Ed.card : ℝ) / 24) ≤ Real.exp (- (2000 * (L : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          have hR : (64000 * L ^ 2 : ℝ) ≤ (Ed.card : ℝ) := by exact_mod_cast hEd_ge
          linarith
        exact hch.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      have hDle_n : D_set.card ≤ n := by
        have h1024 : 1024 * ℓ ≤ m := by
          have h1 : 1024 * ℓ ≤ 10000 * ℓ * L := by
            calc 1024 * ℓ = 1024 * ℓ * 1 := by ring
              _ ≤ 10000 * ℓ * L := Nat.mul_le_mul (by omega) (by omega)
          exact h1.trans hm_big
        have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < 1024 * ℓ) h1024
        have h1 : 1024 * ℓ * n / m ≤ n := by
          have h2 : 1024 * ℓ * n ≤ m * n := Nat.mul_le_mul_right n h1024
          exact (Nat.div_le_iff_le_mul_add_pred hmpos).mpr (h2.trans (Nat.le_add_right _ _))
        have h2 : D_set.card ≤ 1024 * ℓ * n / m := by simp [D_set]
        omega
      have hDexp : (D_set.card : ℝ) * Real.exp (- (2000 * (L : ℝ) ^ 2)) ≤ 1 / 16 := by
        have h1 : (D_set.card : ℝ) ≤ Real.exp (L : ℝ) :=
          le_trans (by exact_mod_cast hDle_n) (nat_lt_exp_log2P n).le
        have h2 : (D_set.card : ℝ) * Real.exp (- (2000 * (L : ℝ) ^ 2)) ≤
            Real.exp ((L : ℝ) + - (2000 * (L : ℝ) ^ 2)) := by
          rw [Real.exp_add]
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        have h3 : Real.exp ((L : ℝ) + - (2000 * (L : ℝ) ^ 2)) ≤ Real.exp (-4 : ℝ) := by
          apply Real.exp_le_exp.mpr
          have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
          nlinarith
        exact h2.trans (h3.trans exp_neg_four_lt.le)
      calc ∑ d ∈ D_set, ((bad_div d).card : ℝ)
          ≤ ∑ _d ∈ D_set, ((2 : ℝ) ^ Fintype.card A' * Real.exp (- (2000 * (L : ℝ) ^ 2))) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ Fintype.card A' * ((D_set.card : ℝ) * Real.exp (- (2000 * (L : ℝ) ^ 2))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) :=
            mul_le_mul_of_nonneg_left hDexp (by positivity)
    have hJ_sum : ∑ j ∈ J_set, ((bad_dyad j).card : ℝ) ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) := by
      have hterm : ∀ j ∈ J_set, ((bad_dyad j).card : ℝ) ≤
          (2 : ℝ) ^ Fintype.card A' * Real.exp (- (10 * (L : ℝ))) := by
        intro j hj
        obtain ⟨hjL, hjne⟩ := Finset.mem_filter.mp hj
        have hjL' := Finset.mem_range.mp hjL
        let Ej : Finset A' := Finset.univ.filter (fun x : A' => 2 ^ j ≤ x.1 ∧ x.1 < 2 ^ (j + 1))
        have hEj_card : Ej.card = (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card := by
          have hbij : Ej.image Subtype.val = A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) := by
            ext x
            simp only [Ej, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
            exact ⟨fun ⟨a, ha, hp, heq⟩ => heq ▸ ⟨ha, hp⟩, fun ⟨hx, hp⟩ => ⟨x, hx, hp, rfl⟩⟩
          rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
        have hEj_ge : 256 * L ≤ Ej.card := by
          rw [hEj_card]
          rcases hNice.2 j hjL' with h0 | hbig
          · exfalso
            have hpos := hjne.card_pos
            omega
          · have h1 : 256 * L ≤ 256 * ℓ * L := by
              calc 256 * L = 256 * 1 * L := by ring
                _ ≤ 256 * ℓ * L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hℓ)
            exact h1.trans hbig
        have hch := h_chernoff_half Ej true
        have hexp : Real.exp (- (Ej.card : ℝ) / 24) ≤ Real.exp (- (10 * (L : ℝ))) := by
          apply Real.exp_le_exp.mpr
          have hR : (256 * L : ℝ) ≤ (Ej.card : ℝ) := by exact_mod_cast hEj_ge
          linarith
        exact hch.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
      have hJle : J_set.card ≤ L := by
        calc J_set.card ≤ (Finset.range L).card := Finset.card_le_card (Finset.filter_subset _ _)
          _ = L := Finset.card_range L
      have hJexp : (J_set.card : ℝ) * Real.exp (- (10 * (L : ℝ))) ≤ 1 / 16 := by
        have h1 : (J_set.card : ℝ) ≤ Real.exp (L : ℝ) := by
          have hJL : (J_set.card : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJle
          have hLexp : (L : ℝ) ≤ Real.exp (L : ℝ) := by linarith [Real.add_one_le_exp (L : ℝ)]
          linarith
        have h2 : (J_set.card : ℝ) * Real.exp (- (10 * (L : ℝ))) ≤
            Real.exp ((L : ℝ) + - (10 * (L : ℝ))) := by
          rw [Real.exp_add]
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
        have h3 : Real.exp ((L : ℝ) + - (10 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
          apply Real.exp_le_exp.mpr
          have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
          linarith
        exact h2.trans (h3.trans exp_neg_four_lt.le)
      calc ∑ j ∈ J_set, ((bad_dyad j).card : ℝ)
          ≤ ∑ _j ∈ J_set, ((2 : ℝ) ^ Fintype.card A' * Real.exp (- (10 * (L : ℝ)))) :=
            Finset.sum_le_sum hterm
        _ = (2 : ℝ) ^ Fintype.card A' * ((J_set.card : ℝ) * Real.exp (- (10 * (L : ℝ)))) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ ≤ (2 : ℝ) ^ Fintype.card A' * (1 / 16) :=
            mul_le_mul_of_nonneg_left hJexp (by positivity)
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ Fintype.card A' := by positivity
    linarith
  have hlt_nat : all_bad.card < (Finset.univ : Finset (A' → Bool)).card := by
    have hcard_u : ((Finset.univ : Finset (A' → Bool)).card : ℝ) = (2 : ℝ) ^ Fintype.card A' := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool]; push_cast; rfl
    exact_mod_cast (hcard_u.symm ▸ hbad_lt)
  obtain ⟨f, _, hf_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_nat
  let A_core : Finset ℕ := (Finset.univ.filter (fun x : A' => f x = true)).image Subtype.val
  let A_ext : Finset ℕ := (Finset.univ.filter (fun x : A' => f x = false)).image Subtype.val
  have hnot_core : f ∉ bad_core := fun h =>
    hf_not (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
  have hnot_ext : f ∉ bad_ext := fun h =>
    hf_not (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
  have hnot_div : ∀ d ∈ D_set, f ∉ bad_div d := fun d hd h =>
    hf_not (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨d, hd, h⟩)))
  have hnot_dyad : ∀ j ∈ J_set, f ∉ bad_dyad j := fun j hj h =>
    hf_not (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, hj, h⟩))
  refine ⟨A_core, A_ext, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp ha1
    obtain ⟨x2, hx2, heq⟩ := Finset.mem_image.mp ha2
    have h1 := (Finset.mem_filter.mp hx1).2
    have h2 := (Finset.mem_filter.mp hx2).2
    rw [Subtype.ext heq.symm, h2] at h1; contradiction
  · ext a
    simp only [A_core, A_ext, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and, Subtype.exists]
    constructor
    · rintro (⟨x, hx, _, rfl⟩ | ⟨x, hx, _, rfl⟩) <;> exact hx
    · intro ha
      cases hfa : f ⟨a, ha⟩
      · right; exact ⟨a, ha, hfa, rfl⟩
      · left; exact ⟨a, ha, hfa, rfl⟩
  · have hgt : (Finset.univ : Finset A').card < 4 * (Finset.univ.filter (fun x : A' => f x = true)).card := by
      by_contra hle; push Not at hle
      exact hnot_core (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simp only [Finset.card_univ, Fintype.card_coe] at hgt
    omega
  · have hgt : (Finset.univ : Finset A').card < 4 * (Finset.univ.filter (fun x : A' => f x = false)).card := by
      by_contra hle; push Not at hle
      exact hnot_ext (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    simp only [Finset.card_univ, Fintype.card_coe] at hgt
    omega
  · intro d hd2 hdub
    have hdD : d ∈ D_set := Finset.mem_Icc.mpr ⟨hd2, hdub⟩
    let Ed : Finset A' := Finset.univ.filter (fun x : A' => ¬ d ∣ x.1)
    have hgt : Ed.card < 4 * (Ed.filter (fun x => f x = true)).card := by
      by_contra hle; push Not at hle
      exact hnot_div d hdD (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    have hEd_card : Ed.card = (A'.filter (fun a => ¬ d ∣ a)).card := by
      have hbij : Ed.image Subtype.val = A'.filter (fun a => ¬ d ∣ a) := by
        ext x
        simp only [Ed, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
        exact ⟨fun ⟨a, ha, hnd, heq⟩ => heq ▸ ⟨ha, hnd⟩, fun ⟨hx, hnd⟩ => ⟨x, hx, hnd, rfl⟩⟩
      rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
    have hbij2 : (Ed.filter (fun x => f x = true)).image Subtype.val =
        A_core.filter (fun a => ¬ d ∣ a) := by
      ext a
      simp only [Ed, A_core, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨x, hx, ⟨hnd, hfx⟩, heq⟩ => heq ▸ ⟨⟨x, hx, hfx, rfl⟩, hnd⟩,
        fun ⟨⟨x, hx, hfx, heq⟩, hnd⟩ => ⟨x, hx, ⟨heq ▸ hnd, hfx⟩, heq⟩⟩
    have hcard2 : (Ed.filter (fun x => f x = true)).card = (A_core.filter (fun a => ¬ d ∣ a)).card := by
      rw [← hbij2, Finset.card_image_of_injective _ Subtype.val_injective]
    have hdiv : 64000 * ℓ * L ^ 2 + 512 * ℓ * d ≤ (A'.filter (fun a => ¬ d ∣ a)).card := hNice.1 d hd2 hdub
    have h64 : 64000 * ℓ * L ^ 2 + 512 * ℓ * d = 4 * (16000 * ℓ * L ^ 2 + 128 * ℓ * d) := by ring
    rw [hEd_card, hcard2] at hgt
    omega
  · intro j hjL hjne
    have hjJ : j ∈ J_set := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjL, hjne⟩
    let Ej : Finset A' := Finset.univ.filter (fun x : A' => 2 ^ j ≤ x.1 ∧ x.1 < 2 ^ (j + 1))
    have hgt : Ej.card < 4 * (Ej.filter (fun x => f x = true)).card := by
      by_contra hle; push Not at hle
      exact hnot_dyad j hjJ (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    have hEj_card : Ej.card = (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card := by
      have hbij : Ej.image Subtype.val = A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) := by
        ext x
        simp only [Ej, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
        exact ⟨fun ⟨a, ha, hp, heq⟩ => heq ▸ ⟨ha, hp⟩, fun ⟨hx, hp⟩ => ⟨x, hx, hp, rfl⟩⟩
      rw [← hbij, Finset.card_image_of_injective _ Subtype.val_injective]
    have hbij2 : (Ej.filter (fun x => f x = true)).image Subtype.val =
        A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) := by
      ext a
      simp only [Ej, A_core, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨x, hx, ⟨hp, hfx⟩, heq⟩ => heq ▸ ⟨⟨x, hx, hfx, rfl⟩, hp⟩,
        fun ⟨⟨x, hx, hfx, heq⟩, hp⟩ => ⟨x, hx, ⟨heq ▸ hp, hfx⟩, heq⟩⟩
    have hcard2 : (Ej.filter (fun x => f x = true)).card =
        (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card := by
      rw [← hbij2, Finset.card_image_of_injective _ Subtype.val_injective]
    have hdy : 256 * ℓ * L ≤ (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card := by
      rcases hNice.2 j hjL with h0 | hbig
      · exfalso; have := hjne.card_pos; omega
      · exact hbig
    have h256 : 256 * ℓ * L = 4 * (64 * ℓ * L) := by ring
    rw [hEj_card, hcard2] at hgt
    omega

-- Step 2: Good coloring of A_core → Fin ℓ × Bool using Chernoff bounds
include h_chernoff_lower h_chernoff_upper in
set_option maxHeartbeats 600000 in
lemma exists_good_coloring {ℓ n m k' : ℕ} (hℓ : 1 ≤ ℓ) (hn : 2 ≤ n)
    (hL_big : 100 * (log2P ℓ + 1) ≤ log2P n)
    (hm_big : 65536 * ℓ * log2P n ≤ m)
    (hk'_ge : 4 * log2P n ≤ k')
    (A_core A_lo A_hi X : Finset ℕ)
    (hlo_sub : A_lo ⊆ A_core) (hhi_sub : A_hi ⊆ A_core) (hX_sub : X ⊆ A_hi)
    (hlo_card : m / 16 ≤ A_lo.card) (hhi_card : m / 16 ≤ A_hi.card)
    (hX_card : X.card = 8 * ℓ * k')
    (hcore_div : ∀ d : ℕ, 2 ≤ d → d ≤ 1024 * ℓ * n / m →
      16000 * ℓ * (log2P n) ^ 2 + 128 * ℓ * d ≤ (A_core.filter (fun a => ¬ d ∣ a)).card) :
    ∃ f : A_core → Fin ℓ × Bool,
      ∀ i : Fin ℓ,
        let C_all : Finset (Fin ℓ × Bool) := {(i, false), (i, true)}
        let C_f : Finset (Fin ℓ × Bool) := {(i, false)}
        let C_t : Finset (Fin ℓ × Bool) := {(i, true)}
        let img (S : Finset ℕ) (C : Finset (Fin ℓ × Bool)) : Finset ℕ :=
          (Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C)).image Subtype.val
        A_lo.card < 4 * ℓ * (img A_lo C_all).card ∧
        2 * ℓ * (img A_hi C_f).card < 3 * A_hi.card ∧
        2 * ℓ * (img X C_t).card < 3 * X.card ∧
        (∀ d : ℕ, 2 ≤ d → d ≤ 1024 * ℓ * n / m →
          (A_core.filter (fun a => ¬ d ∣ a)).card <
            8 * ℓ * (img (A_core.filter (fun a => ¬ d ∣ a)) C_f).card) ∧
        (∀ j : ℕ, j < log2P n →
          16 * ℓ * log2P n ≤ (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card →
          (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card <
            8 * ℓ * (img (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) C_t).card) ∧
        (∀ j : ℕ, j < log2P n →
          64 * ℓ * log2P n ≤ (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card →
          ℓ * (img (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) C_all).card <
            3 * (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card) := by
  set L := log2P n
  change 65536 * ℓ * L ≤ m at hm_big
  change 4 * L ≤ k' at hk'_ge
  have hL100 : 100 ≤ L := by omega
  have hβ_card : Fintype.card (Fin ℓ × Bool) = 2 * ℓ := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  have hβ_pos : 0 < Fintype.card (Fin ℓ × Bool) := by rw [hβ_card]; omega
  -- Helper lifting S ⊆ A_core to Finset A_core
  let lift (S : Finset ℕ) : Finset A_core := Finset.univ.filter (fun x : A_core => x.1 ∈ S)
  have hlift_card : ∀ S : Finset ℕ, S ⊆ A_core → (lift S).card = S.card := by
    intro S hS
    have hbij : (lift S).image Subtype.val = S := by
      ext a
      simp only [lift, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists]
      exact ⟨fun ⟨x, _, hxS, heq⟩ => heq ▸ hxS, fun ha => ⟨a, hS ha, ha, rfl⟩⟩
    calc (lift S).card = ((lift S).image Subtype.val).card := (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ = S.card := by rw [hbij]
  let C_all (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, false), (i, true)}
  let C_f (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, false)}
  let C_t (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, true)}
  have hCall_card : ∀ i : Fin ℓ, (C_all i).card = 2 := fun i =>
    Finset.card_pair (by intro h; injection h with _ h2; cases h2)
  have hCf_card : ∀ i : Fin ℓ, (C_f i).card = 1 := fun i => Finset.card_singleton _
  have hCt_card : ∀ i : Fin ℓ, (C_t i).card = 1 := fun i => Finset.card_singleton _
  -- Index sets for bad events
  let D_set : Finset ℕ := Finset.Icc 2 (1024 * ℓ * n / m)
  let J5_set : Finset ℕ := (Finset.range L).filter (fun j =>
    16 * ℓ * L ≤ (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card)
  let J6_set : Finset ℕ := (Finset.range L).filter (fun j =>
    64 * ℓ * L ≤ (A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card)
  -- Define the 6 families of bad events
  let bad1 (i : Fin ℓ) : Finset (A_core → Fin ℓ × Bool) :=
    Finset.univ.filter (fun f =>
      4 * (((lift A_lo).filter (fun a => f a ∈ C_all i)).card : ℝ) ≤
        ((C_all i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * ((lift A_lo).card : ℝ))
  let bad2 (i : Fin ℓ) : Finset (A_core → Fin ℓ × Bool) :=
    Finset.univ.filter (fun f =>
      3 * (((C_f i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * ((lift A_hi).card : ℝ) ≤
        (((lift A_hi).filter (fun a => f a ∈ C_f i)).card : ℝ))
  let bad4 (i : Fin ℓ) : Finset (A_core → Fin ℓ × Bool) :=
    Finset.univ.filter (fun f =>
      3 * (((C_t i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * ((lift X).card : ℝ) ≤
        (((lift X).filter (fun a => f a ∈ C_t i)).card : ℝ))
  let bad3 (p : Fin ℓ × ℕ) : Finset (A_core → Fin ℓ × Bool) :=
    let Ed := lift (A_core.filter (fun a => ¬ p.2 ∣ a))
    Finset.univ.filter (fun f =>
      4 * ((Ed.filter (fun a => f a ∈ C_f p.1)).card : ℝ) ≤
        ((C_f p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * (Ed.card : ℝ))
  let bad5 (p : Fin ℓ × ℕ) : Finset (A_core → Fin ℓ × Bool) :=
    let Ej := lift (X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1)))
    Finset.univ.filter (fun f =>
      4 * ((Ej.filter (fun a => f a ∈ C_t p.1)).card : ℝ) ≤
        ((C_t p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * (Ej.card : ℝ))
  let bad6 (p : Fin ℓ × ℕ) : Finset (A_core → Fin ℓ × Bool) :=
    let Ej := lift (A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1)))
    Finset.univ.filter (fun f =>
      3 * (((C_all p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * (Ej.card : ℝ) ≤
        ((Ej.filter (fun a => f a ∈ C_all p.1)).card : ℝ))
  let all_bad : Finset (A_core → Fin ℓ × Bool) :=
    Finset.univ.biUnion bad1 ∪ Finset.univ.biUnion bad2 ∪ Finset.univ.biUnion bad4 ∪
    (Finset.univ ×ˢ D_set).biUnion bad3 ∪ (Finset.univ ×ˢ J5_set).biUnion bad5 ∪
    (Finset.univ ×ˢ J6_set).biUnion bad6
  -- Common real exponential helpers
  set W : ℝ := (Fintype.card (Fin ℓ × Bool) : ℝ) ^ Fintype.card A_core
  have hWpos : 0 < W := by dsimp [W]; positivity
  have hℓ_lt_exp : (ℓ : ℝ) < Real.exp ((L : ℝ) / 100) := by
    have h1 := nat_lt_exp_log2P ℓ
    have h2 : (log2P ℓ : ℝ) ≤ (L : ℝ) / 100 := by
      have : 100 * log2P ℓ ≤ L := by omega
      have hR : (100 * log2P ℓ : ℝ) ≤ (L : ℝ) := by exact_mod_cast this
      linarith
    exact h1.trans_le (Real.exp_le_exp.mpr h2)
  have hL_le_expL : (L : ℝ) ≤ Real.exp (L : ℝ) := by linarith [Real.add_one_le_exp (L : ℝ)]
  have hℓposR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  -- Bound each of the 6 union sums by W * (1 / 16)
  have hsum1 : ∑ i : Fin ℓ, ((bad1 i).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ i : Fin ℓ, ((bad1 i).card : ℝ) ≤ W * Real.exp (- (10 * (L : ℝ))) := by
      intro i
      have hch := h_chernoff_lower (lift A_lo) (C_all i) hβ_pos
      have hcard_lo : (lift A_lo).card = A_lo.card := hlift_card A_lo hlo_sub
      have hEge : 40 * ℓ * L ≤ A_lo.card := by
        have h64 : 65536 * ℓ * L = 16 * (4096 * ℓ * L) := by ring
        have h40 : 40 * ℓ * L ≤ 4096 * ℓ * L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        omega
      have hexp : Real.exp (- (((C_all i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          ((lift A_lo).card : ℝ) / 4) ≤ Real.exp (- (10 * (L : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hCall_card, hβ_card, hcard_lo]
        push_cast
        have hR : (40 * (ℓ : ℝ) * (L : ℝ)) ≤ (A_lo.card : ℝ) := by exact_mod_cast hEge
        rw [show -(2 / (2 * (ℓ : ℝ))) * (A_lo.card : ℝ) / 4 = -((A_lo.card : ℝ) / (4 * (ℓ : ℝ))) by
          field_simp]
        have hdiv : (10 * (L : ℝ)) ≤ (A_lo.card : ℝ) / (4 * (ℓ : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    calc ∑ i : Fin ℓ, ((bad1 i).card : ℝ)
        ≤ ∑ _i : Fin ℓ, (W * Real.exp (- (10 * (L : ℝ)))) := Finset.sum_le_sum fun i _ => hterm i
      _ = W * ((ℓ : ℝ) * Real.exp (- (10 * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * Real.exp (- (10 * (L : ℝ))) ≤
              Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) := by
            rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hℓ_lt_exp.le (Real.exp_pos _).le
          have h2 : Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            linarith
          exact h1.trans (h2.trans exp_neg_four_lt.le)
  have hsum2 : ∑ i : Fin ℓ, ((bad2 i).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ i : Fin ℓ, ((bad2 i).card : ℝ) ≤ W * Real.exp (- (10 * (L : ℝ))) := by
      intro i
      have hch := h_chernoff_upper (lift A_hi) (C_f i) hβ_pos
      have hcard_hi : (lift A_hi).card = A_hi.card := hlift_card A_hi hhi_sub
      have hEge : 20 * ℓ * L ≤ A_hi.card := by
        have h64 : 65536 * ℓ * L = 16 * (4096 * ℓ * L) := by ring
        have h20 : 20 * ℓ * L ≤ 4096 * ℓ * L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        omega
      have hexp : Real.exp (- (((C_f i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          ((lift A_hi).card : ℝ)) ≤ Real.exp (- (10 * (L : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hCf_card, hβ_card, hcard_hi]
        push_cast
        have hR : (20 * (ℓ : ℝ) * (L : ℝ)) ≤ (A_hi.card : ℝ) := by exact_mod_cast hEge
        rw [show -(1 / (2 * (ℓ : ℝ))) * (A_hi.card : ℝ) = -((A_hi.card : ℝ) / (2 * (ℓ : ℝ))) by
          field_simp]
        have hdiv : (10 * (L : ℝ)) ≤ (A_hi.card : ℝ) / (2 * (ℓ : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    calc ∑ i : Fin ℓ, ((bad2 i).card : ℝ)
        ≤ ∑ _i : Fin ℓ, (W * Real.exp (- (10 * (L : ℝ)))) := Finset.sum_le_sum fun i _ => hterm i
      _ = W * ((ℓ : ℝ) * Real.exp (- (10 * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * Real.exp (- (10 * (L : ℝ))) ≤
              Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) := by
            rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hℓ_lt_exp.le (Real.exp_pos _).le
          have h2 : Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            linarith
          exact h1.trans (h2.trans exp_neg_four_lt.le)
  have hsum4 : ∑ i : Fin ℓ, ((bad4 i).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ i : Fin ℓ, ((bad4 i).card : ℝ) ≤ W * Real.exp (- (10 * (L : ℝ))) := by
      intro i
      have hch := h_chernoff_upper (lift X) (C_t i) hβ_pos
      have hcard_X : (lift X).card = X.card := hlift_card X (hX_sub.trans hhi_sub)
      have hEge : 20 * ℓ * L ≤ X.card := by
        rw [hX_card]
        have h32 : 32 * ℓ * L ≤ 8 * ℓ * k' := by
          calc 32 * ℓ * L = 8 * ℓ * (4 * L) := by ring
            _ ≤ 8 * ℓ * k' := Nat.mul_le_mul_left _ hk'_ge
        have h20 : 20 * ℓ * L ≤ 32 * ℓ * L := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
        omega
      have hexp : Real.exp (- (((C_t i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          ((lift X).card : ℝ)) ≤ Real.exp (- (10 * (L : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hCt_card, hβ_card, hcard_X]
        push_cast
        have hR : (20 * (ℓ : ℝ) * (L : ℝ)) ≤ (X.card : ℝ) := by exact_mod_cast hEge
        rw [show -(1 / (2 * (ℓ : ℝ))) * (X.card : ℝ) = -((X.card : ℝ) / (2 * (ℓ : ℝ))) by
          field_simp]
        have hdiv : (10 * (L : ℝ)) ≤ (X.card : ℝ) / (2 * (ℓ : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    calc ∑ i : Fin ℓ, ((bad4 i).card : ℝ)
        ≤ ∑ _i : Fin ℓ, (W * Real.exp (- (10 * (L : ℝ)))) := Finset.sum_le_sum fun i _ => hterm i
      _ = W * ((ℓ : ℝ) * Real.exp (- (10 * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * Real.exp (- (10 * (L : ℝ))) ≤
              Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) := by
            rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hℓ_lt_exp.le (Real.exp_pos _).le
          have h2 : Real.exp ((L : ℝ) / 100 + - (10 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            linarith
          exact h1.trans (h2.trans exp_neg_four_lt.le)
  have hsum3 : ∑ p ∈ Finset.univ ×ˢ D_set, ((bad3 p).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ p ∈ Finset.univ ×ˢ D_set, ((bad3 p).card : ℝ) ≤ W * Real.exp (- (1000 * (L : ℝ) ^ 2)) := by
      intro p hp
      obtain ⟨_, hdD⟩ := Finset.mem_product.mp hp
      obtain ⟨hd2, hdub⟩ := Finset.mem_Icc.mp hdD
      let Ed := lift (A_core.filter (fun a => ¬ p.2 ∣ a))
      have hch := h_chernoff_lower Ed (C_f p.1) hβ_pos
      have hEd_card : Ed.card = (A_core.filter (fun a => ¬ p.2 ∣ a)).card :=
        hlift_card _ (Finset.filter_subset _ _)
      have hEd_ge : 8000 * ℓ * L ^ 2 ≤ Ed.card := by
        rw [hEd_card]
        have h1 : 16000 * ℓ * L ^ 2 + 128 * ℓ * p.2 ≤ (A_core.filter (fun a => ¬ p.2 ∣ a)).card := hcore_div p.2 hd2 hdub
        have h2 : 16000 * ℓ * L ^ 2 = 2 * (8000 * ℓ * L ^ 2) := by ring
        omega
      have hexp : Real.exp (- (((C_f p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          (Ed.card : ℝ) / 4) ≤ Real.exp (- (1000 * (L : ℝ) ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [hCf_card, hβ_card]; push_cast
        have hR : (8000 * (ℓ : ℝ) * (L : ℝ) ^ 2) ≤ (Ed.card : ℝ) := by exact_mod_cast hEd_ge
        rw [show -(1 / (2 * (ℓ : ℝ))) * (Ed.card : ℝ) / 4 = -((Ed.card : ℝ) / (8 * (ℓ : ℝ))) by
          field_simp; ring]
        have hdiv : (1000 * (L : ℝ) ^ 2) ≤ (Ed.card : ℝ) / (8 * (ℓ : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    have hDle_n : D_set.card ≤ n := by
      have h1024 : 1024 * ℓ ≤ m := by
        have h1 : 1024 * ℓ ≤ 65536 * ℓ * L := by
          calc 1024 * ℓ = 1024 * ℓ * 1 := by ring
            _ ≤ 65536 * ℓ * L := Nat.mul_le_mul (by omega) (by omega)
        exact h1.trans hm_big
      have hmpos : 0 < m := lt_of_lt_of_le (by omega : 0 < 1024 * ℓ) h1024
      have h1 : 1024 * ℓ * n / m ≤ n := by
        have h2 : 1024 * ℓ * n ≤ m * n := Nat.mul_le_mul_right n h1024
        exact (Nat.div_le_iff_le_mul_add_pred hmpos).mpr (h2.trans (Nat.le_add_right _ _))
      have h2 : D_set.card ≤ 1024 * ℓ * n / m := by simp [D_set]
      omega
    calc ∑ p ∈ Finset.univ ×ˢ D_set, ((bad3 p).card : ℝ)
        ≤ ∑ _p ∈ Finset.univ ×ˢ D_set, (W * Real.exp (- (1000 * (L : ℝ) ^ 2))) := Finset.sum_le_sum hterm
      _ = W * (((ℓ : ℝ) * (D_set.card : ℝ)) * Real.exp (- (1000 * (L : ℝ) ^ 2))) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * (D_set.card : ℝ) ≤ Real.exp ((L : ℝ) / 100) * Real.exp (L : ℝ) := by
            apply mul_le_mul hℓ_lt_exp.le (le_trans (by exact_mod_cast hDle_n) (nat_lt_exp_log2P n).le)
              (by positivity) (Real.exp_pos _).le
          have h2 : ((ℓ : ℝ) * (D_set.card : ℝ)) * Real.exp (- (1000 * (L : ℝ) ^ 2)) ≤
              Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (1000 * (L : ℝ) ^ 2)) := by
            rw [Real.exp_add, Real.exp_add]
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          have h3 : Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (1000 * (L : ℝ) ^ 2)) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            have hLsq : (100 : ℝ) * (L : ℝ) ≤ (L : ℝ) ^ 2 := by
              rw [sq]; exact mul_le_mul_of_nonneg_right hLR (by positivity)
            linarith
          exact h2.trans (h3.trans exp_neg_four_lt.le)
  have hsum5 : ∑ p ∈ Finset.univ ×ˢ J5_set, ((bad5 p).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ p ∈ Finset.univ ×ˢ J5_set, ((bad5 p).card : ℝ) ≤ W * Real.exp (- (2 * (L : ℝ))) := by
      intro p hp
      obtain ⟨_, hjJ⟩ := Finset.mem_product.mp hp
      have hge := (Finset.mem_filter.mp hjJ).2
      let Ej := lift (X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1)))
      have hch := h_chernoff_lower Ej (C_t p.1) hβ_pos
      have hEj_card : Ej.card = (X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card :=
        hlift_card _ ((Finset.filter_subset _ _).trans (hX_sub.trans hhi_sub))
      have hexp : Real.exp (- (((C_t p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          (Ej.card : ℝ) / 4) ≤ Real.exp (- (2 * (L : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hCt_card, hβ_card, hEj_card]; push_cast
        have hR : (16 * (ℓ : ℝ) * (L : ℝ)) ≤ ((X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) := by
          exact_mod_cast hge
        rw [show -(1 / (2 * (ℓ : ℝ))) * ((X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) / 4 =
            -(((X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) / (8 * (ℓ : ℝ))) by
          field_simp; ring]
        have hdiv : (2 * (L : ℝ)) ≤
            ((X.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) / (8 * (ℓ : ℝ)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    have hJle : J5_set.card ≤ L :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    calc ∑ p ∈ Finset.univ ×ˢ J5_set, ((bad5 p).card : ℝ)
        ≤ ∑ _p ∈ Finset.univ ×ˢ J5_set, (W * Real.exp (- (2 * (L : ℝ)))) := Finset.sum_le_sum hterm
      _ = W * (((ℓ : ℝ) * (J5_set.card : ℝ)) * Real.exp (- (2 * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * (J5_set.card : ℝ) ≤ Real.exp ((L : ℝ) / 100) * Real.exp (L : ℝ) :=
            mul_le_mul hℓ_lt_exp.le (le_trans (by exact_mod_cast hJle) hL_le_expL)
              (by positivity) (Real.exp_pos _).le
          have h2 : ((ℓ : ℝ) * (J5_set.card : ℝ)) * Real.exp (- (2 * (L : ℝ))) ≤
              Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (2 * (L : ℝ))) := by
            rw [Real.exp_add, Real.exp_add]
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          have h3 : Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (2 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            linarith
          exact h2.trans (h3.trans exp_neg_four_lt.le)
  have hsum6 : ∑ p ∈ Finset.univ ×ˢ J6_set, ((bad6 p).card : ℝ) ≤ W * (1 / 16) := by
    have hterm : ∀ p ∈ Finset.univ ×ˢ J6_set, ((bad6 p).card : ℝ) ≤ W * Real.exp (- (64 * (L : ℝ))) := by
      intro p hp
      obtain ⟨_, hjJ⟩ := Finset.mem_product.mp hp
      have hge := (Finset.mem_filter.mp hjJ).2
      let Ej := lift (A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1)))
      have hch := h_chernoff_upper Ej (C_all p.1) hβ_pos
      have hEj_card : Ej.card = (A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card :=
        hlift_card _ (Finset.filter_subset _ _)
      have hexp : Real.exp (- (((C_all p.1).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) *
          (Ej.card : ℝ)) ≤ Real.exp (- (64 * (L : ℝ))) := by
        apply Real.exp_le_exp.mpr
        rw [hCall_card, hβ_card, hEj_card]; push_cast
        have hR : (64 * (ℓ : ℝ) * (L : ℝ)) ≤ ((A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) := by
          exact_mod_cast hge
        rw [show -(2 / (2 * (ℓ : ℝ))) * ((A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) =
            -(((A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) / (ℓ : ℝ)) by
          field_simp]
        have hdiv : (64 * (L : ℝ)) ≤
            ((A_core.filter (fun a => 2 ^ p.2 ≤ a ∧ a < 2 ^ (p.2 + 1))).card : ℝ) / (ℓ : ℝ) := by
          rw [le_div_iff₀ hℓposR]; linarith
        linarith
      exact hch.trans (mul_le_mul_of_nonneg_left hexp hWpos.le)
    have hJle : J6_set.card ≤ L :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
    calc ∑ p ∈ Finset.univ ×ˢ J6_set, ((bad6 p).card : ℝ)
        ≤ ∑ _p ∈ Finset.univ ×ˢ J6_set, (W * Real.exp (- (64 * (L : ℝ)))) := Finset.sum_le_sum hterm
      _ = W * (((ℓ : ℝ) * (J6_set.card : ℝ)) * Real.exp (- (64 * (L : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
      _ ≤ W * (1 / 16) := by
          apply mul_le_mul_of_nonneg_left _ hWpos.le
          have h1 : (ℓ : ℝ) * (J6_set.card : ℝ) ≤ Real.exp ((L : ℝ) / 100) * Real.exp (L : ℝ) :=
            mul_le_mul hℓ_lt_exp.le (le_trans (by exact_mod_cast hJle) hL_le_expL)
              (by positivity) (Real.exp_pos _).le
          have h2 : ((ℓ : ℝ) * (J6_set.card : ℝ)) * Real.exp (- (64 * (L : ℝ))) ≤
              Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (64 * (L : ℝ))) := by
            rw [Real.exp_add, Real.exp_add]
            exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
          have h3 : Real.exp ((L : ℝ) / 100 + (L : ℝ) + - (64 * (L : ℝ))) ≤ Real.exp (-4 : ℝ) := by
            apply Real.exp_le_exp.mpr
            have hLR : (100 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL100
            linarith
          exact h2.trans (h3.trans exp_neg_four_lt.le)
  have hall_lt : (all_bad.card : ℝ) < W := by
    have hcu : all_bad.card ≤
        (∑ i : Fin ℓ, (bad1 i).card) + (∑ i : Fin ℓ, (bad2 i).card) +
        (∑ i : Fin ℓ, (bad4 i).card) + (∑ p ∈ Finset.univ ×ˢ D_set, (bad3 p).card) +
        (∑ p ∈ Finset.univ ×ˢ J5_set, (bad5 p).card) + (∑ p ∈ Finset.univ ×ˢ J6_set, (bad6 p).card) := by
      have u1 := Finset.card_union_le (Finset.univ.biUnion bad1 ∪ Finset.univ.biUnion bad2 ∪ Finset.univ.biUnion bad4 ∪
        (Finset.univ ×ˢ D_set).biUnion bad3 ∪ (Finset.univ ×ˢ J5_set).biUnion bad5) ((Finset.univ ×ˢ J6_set).biUnion bad6)
      have u2 := Finset.card_union_le (Finset.univ.biUnion bad1 ∪ Finset.univ.biUnion bad2 ∪ Finset.univ.biUnion bad4 ∪
        (Finset.univ ×ˢ D_set).biUnion bad3) ((Finset.univ ×ˢ J5_set).biUnion bad5)
      have u3 := Finset.card_union_le (Finset.univ.biUnion bad1 ∪ Finset.univ.biUnion bad2 ∪ Finset.univ.biUnion bad4)
        ((Finset.univ ×ˢ D_set).biUnion bad3)
      have u4 := Finset.card_union_le (Finset.univ.biUnion bad1 ∪ Finset.univ.biUnion bad2) (Finset.univ.biUnion bad4)
      have u5 := Finset.card_union_le (Finset.univ.biUnion bad1) (Finset.univ.biUnion bad2)
      have b1 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin ℓ))) (t := bad1)
      have b2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin ℓ))) (t := bad2)
      have b4 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin ℓ))) (t := bad4)
      have b3 := Finset.card_biUnion_le (s := Finset.univ ×ˢ D_set) (t := bad3)
      have b5 := Finset.card_biUnion_le (s := Finset.univ ×ˢ J5_set) (t := bad5)
      have b6 := Finset.card_biUnion_le (s := Finset.univ ×ˢ J6_set) (t := bad6)
      dsimp [all_bad]; omega
    have hcuR : (all_bad.card : ℝ) ≤
        (∑ i : Fin ℓ, ((bad1 i).card : ℝ)) + (∑ i : Fin ℓ, ((bad2 i).card : ℝ)) +
        (∑ i : Fin ℓ, ((bad4 i).card : ℝ)) + (∑ p ∈ Finset.univ ×ˢ D_set, ((bad3 p).card : ℝ)) +
        (∑ p ∈ Finset.univ ×ˢ J5_set, ((bad5 p).card : ℝ)) + (∑ p ∈ Finset.univ ×ˢ J6_set, ((bad6 p).card : ℝ)) := by
      exact_mod_cast hcu
    linarith
  have hlt_nat : all_bad.card < (Finset.univ : Finset (A_core → Fin ℓ × Bool)).card := by
    have hcard_u : ((Finset.univ : Finset (A_core → Fin ℓ × Bool)).card : ℝ) = W := by
      rw [Finset.card_univ, Fintype.card_fun]; push_cast; rfl
    exact_mod_cast (hcard_u.symm ▸ hall_lt)
  obtain ⟨f, _, hf_not⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt_nat
  -- Helper connecting lift-filter card with img card
  have himg_eq : ∀ (S : Finset ℕ) (C : Finset (Fin ℓ × Bool)),
      ((Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C)).image Subtype.val).card =
        ((lift S).filter (fun x => f x ∈ C)).card := by
    intro S C
    rw [Finset.card_image_of_injective _ Subtype.val_injective]
    congr 1
    ext x; simp [lift]
  refine ⟨f, fun i => ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- E1
    have hnb : f ∉ bad1 i := fun h =>
      hf_not (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩))))))
    have hgt : ((C_all i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * ((lift A_lo).card : ℝ) <
        4 * (((lift A_lo).filter (fun a => f a ∈ C_all i)).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCall_card, hβ_card, hlift_card A_lo hlo_sub, ← himg_eq A_lo (C_all i)] at hgt
    push_cast at hgt
    have hmul : (A_lo.card : ℝ) < 4 * (ℓ : ℝ) * (((Finset.univ.filter (fun x : A_core => x.1 ∈ A_lo ∧ f x ∈ C_all i)).image Subtype.val).card : ℝ) := by
      have h1 : (2 : ℝ) / (2 * (ℓ : ℝ)) * (A_lo.card : ℝ) = (A_lo.card : ℝ) / (ℓ : ℝ) := by field_simp
      rw [h1, div_lt_iff₀ hℓposR] at hgt
      linarith
    exact_mod_cast hmul
  · -- E2
    have hnb : f ∉ bad2 i := fun h =>
      hf_not (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩))))))
    have hlt : (((lift A_hi).filter (fun a => f a ∈ C_f i)).card : ℝ) <
        3 * (((C_f i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * ((lift A_hi).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCf_card, hβ_card, hlift_card A_hi hhi_sub, ← himg_eq A_hi (C_f i)] at hlt
    push_cast at hlt
    have hmul : 2 * (ℓ : ℝ) * (((Finset.univ.filter (fun x : A_core => x.1 ∈ A_hi ∧ f x ∈ C_f i)).image Subtype.val).card : ℝ) <
        3 * (A_hi.card : ℝ) := by
      have h1 : 3 * (1 / (2 * (ℓ : ℝ))) * (A_hi.card : ℝ) = (3 * (A_hi.card : ℝ)) / (2 * (ℓ : ℝ)) := by field_simp
      rw [h1, lt_div_iff₀ (by positivity)] at hlt
      linarith
    exact_mod_cast hmul
  · -- E4
    have hnb : f ∉ bad4 i := fun h =>
      hf_not (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩)))))
    have hlt : (((lift X).filter (fun a => f a ∈ C_t i)).card : ℝ) <
        3 * (((C_t i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * ((lift X).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCt_card, hβ_card, hlift_card X (hX_sub.trans hhi_sub), ← himg_eq X (C_t i)] at hlt
    push_cast at hlt
    have hmul : 2 * (ℓ : ℝ) * (((Finset.univ.filter (fun x : A_core => x.1 ∈ X ∧ f x ∈ C_t i)).image Subtype.val).card : ℝ) <
        3 * (X.card : ℝ) := by
      have h1 : 3 * (1 / (2 * (ℓ : ℝ))) * (X.card : ℝ) = (3 * (X.card : ℝ)) / (2 * (ℓ : ℝ)) := by field_simp
      rw [h1, lt_div_iff₀ (by positivity)] at hlt
      linarith
    exact_mod_cast hmul
  · -- E3
    intro d hd2 hdub
    have hp : (i, d) ∈ Finset.univ ×ˢ D_set := Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_Icc.mpr ⟨hd2, hdub⟩⟩
    have hnb : f ∉ bad3 (i, d) := fun h =>
      hf_not (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, d), hp, h⟩))))
    set S := A_core.filter (fun a => ¬ d ∣ a)
    have hgt : ((C_f i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * ((lift S).card : ℝ) <
        4 * (((lift S).filter (fun a => f a ∈ C_f i)).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCf_card, hβ_card, hlift_card S (Finset.filter_subset _ _), ← himg_eq S (C_f i)] at hgt
    push_cast at hgt
    have hmul : (S.card : ℝ) < 8 * (ℓ : ℝ) *
        (((Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C_f i)).image Subtype.val).card : ℝ) := by
      have h1 : (1 : ℝ) / (2 * (ℓ : ℝ)) * (S.card : ℝ) = (S.card : ℝ) / (2 * (ℓ : ℝ)) := by field_simp
      rw [h1, div_lt_iff₀ (by positivity)] at hgt
      linarith
    exact_mod_cast hmul
  · -- E5
    intro j hjL hge
    have hp : (i, j) ∈ Finset.univ ×ˢ J5_set :=
      Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjL, hge⟩⟩
    have hnb : f ∉ bad5 (i, j) := fun h =>
      hf_not (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), hp, h⟩)))
    set S := X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
    have hgt : ((C_t i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ) * ((lift S).card : ℝ) <
        4 * (((lift S).filter (fun a => f a ∈ C_t i)).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCt_card, hβ_card, hlift_card S ((Finset.filter_subset _ _).trans (hX_sub.trans hhi_sub)),
      ← himg_eq S (C_t i)] at hgt
    push_cast at hgt
    have hmul : (S.card : ℝ) < 8 * (ℓ : ℝ) *
        (((Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C_t i)).image Subtype.val).card : ℝ) := by
      have h1 : (1 : ℝ) / (2 * (ℓ : ℝ)) * (S.card : ℝ) = (S.card : ℝ) / (2 * (ℓ : ℝ)) := by field_simp
      rw [h1, div_lt_iff₀ (by positivity)] at hgt
      linarith
    exact_mod_cast hmul
  · -- E6
    intro j hjL hge
    have hp : (i, j) ∈ Finset.univ ×ˢ J6_set :=
      Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjL, hge⟩⟩
    have hnb : f ∉ bad6 (i, j) := fun h =>
      hf_not (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(i, j), hp, h⟩))
    set S := A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
    have hlt : (((lift S).filter (fun a => f a ∈ C_all i)).card : ℝ) <
        3 * (((C_all i).card : ℝ) / (Fintype.card (Fin ℓ × Bool) : ℝ)) * ((lift S).card : ℝ) := by
      by_contra hle; push Not at hle
      exact hnb (Finset.mem_filter.mpr ⟨Finset.mem_univ f, hle⟩)
    rw [hCall_card, hβ_card, hlift_card S (Finset.filter_subset _ _), ← himg_eq S (C_all i)] at hlt
    push_cast at hlt
    have hmul : (ℓ : ℝ) *
        (((Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C_all i)).image Subtype.val).card : ℝ) <
        3 * (S.card : ℝ) := by
      have h1 : 3 * (2 / (2 * (ℓ : ℝ))) * (S.card : ℝ) = (3 * (S.card : ℝ)) / (ℓ : ℝ) := by field_simp
      rw [h1, lt_div_iff₀ hℓposR] at hlt
      linarith
    exact_mod_cast hmul

-- Step 3: Main Theorem 6.1 (homogeneous AP of length ≥ m^2 / 256 inside subset sums of A)
include h_chernoff_lower h_chernoff_upper h_chernoff_half h_card_union_vadd h_subsetSumLe_ins h_lemma_6_2 h_lemma_6_3 h_weak_lev in
set_option maxHeartbeats 1200000 in
theorem theorem_6_1 {α_inv n : ℕ} (hα4096 : 4096 ≤ α_inv) (hn : 2 ≤ n)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 n)
    (hL_big : 100 * (log2P (2 * (16 * α_inv * (4 * α_inv))) + 1) ≤ log2P n)
    (hm_quad : (65536 * (2 * (16 * α_inv * (4 * α_inv)))) ^ 2 * n ≤ A.card ^ 2)
    (hm_log : 1000000 * (2 * (16 * α_inv * (4 * α_inv))) * (log2P n) ^ 3 ≤ A.card) :
    ∃ d_tot a len : ℕ,
      1 ≤ d_tot ∧ d_tot ≤ 3 * n / A.card ∧
      0 < a ∧ A.card * A.card / 256 ≤ len ∧
      d_tot * a ≤ (A.card / 4) * n ∧
      ∀ x ∈ Finset.Icc a (a + len), d_tot * x ∈ A.powerset.image (fun S => S.sum id) := by
  let r : ℕ := 16 * α_inv * (4 * α_inv)
  let ℓ : ℕ := 2 * r
  set m := A.card
  set L := log2P n
  have hα : 1 ≤ α_inv := by omega
  have hℓ : 1 ≤ ℓ := by
    have hr : 1 ≤ r := Nat.mul_pos (Nat.mul_pos (by decide) hα) (Nat.mul_pos (by decide) hα)
    dsimp [ℓ]; omega
  have hL100 : 100 ≤ L := by omega
  have hm_ge_65536 : 65536 * ℓ * L ≤ m := by
    have hL2 : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
    calc 65536 * ℓ * L = 65536 * ℓ * L * 1 := by ring
      _ ≤ 65536 * ℓ * L * L ^ 2 := Nat.mul_le_mul_left _ hL2
      _ = 65536 * (ℓ * L ^ 3) := by ring
      _ ≤ 1000000 * (ℓ * L ^ 3) := Nat.mul_le_mul_right _ (by decide)
      _ = 1000000 * ℓ * L ^ 3 := by ring
      _ ≤ m := hm_log
  have hm_ge_65536_c : 65536 ≤ m := by
    have h1 : 1 ≤ ℓ * L := Nat.mul_pos hℓ (by omega)
    calc 65536 = 65536 * 1 := by ring
      _ ≤ 65536 * (ℓ * L) := Nat.mul_le_mul_left 65536 h1
      _ = 65536 * ℓ * L := by ring
      _ ≤ m := hm_ge_65536
  have hm_pos : 0 < m := by omega
  -- Verify Lemma 6.3 hypothesis
  have h63_hyp : 200000 * ℓ * L ^ 3 + 1048576 * ℓ ^ 2 * n / m + 100 ≤ m / 4 := by
    have hdiv_le : 1048576 * ℓ ^ 2 * n / m ≤ m / 100 := by
      have h1 : 100 * (1048576 * ℓ ^ 2 * n) ≤ m ^ 2 := by
        calc 100 * (1048576 * ℓ ^ 2 * n) = 104857600 * (ℓ ^ 2 * n) := by ring
          _ ≤ 4294967296 * (ℓ ^ 2 * n) := Nat.mul_le_mul_right _ (by decide)
          _ = (65536 * ℓ) ^ 2 * n := by ring
          _ ≤ m ^ 2 := hm_quad
      have h2 : 1048576 * ℓ ^ 2 * n ≤ (m / 100) * m + (m - 1) := by
        have hm100 : 100 * (m / 100) + 99 ≥ m := by omega
        -- Actually even simpler: 1000 * (1048576 * ℓ^2 * n) ≤ m^2 and m ≥ 10000, so
        -- 1048576 * ℓ^2 * n ≤ (m / 100) * m directly!
        have h1' : 200 * (1048576 * ℓ ^ 2 * n) ≤ m ^ 2 := by
          calc 200 * (1048576 * ℓ ^ 2 * n) = 209715200 * (ℓ ^ 2 * n) := by ring
            _ ≤ 4294967296 * (ℓ ^ 2 * n) := Nat.mul_le_mul_right _ (by decide)
            _ = (65536 * ℓ) ^ 2 * n := by ring
            _ ≤ m ^ 2 := hm_quad
        have hm2 : m ≤ 200 * (m / 100) := by omega
        have h3 : 200 * (1048576 * ℓ ^ 2 * n) ≤ (200 * (m / 100)) * m := by
          calc 200 * (1048576 * ℓ ^ 2 * n) ≤ m * m := by simpa [sq] using h1'
            _ ≤ (200 * (m / 100)) * m := Nat.mul_le_mul_right m hm2
        have h4 : 200 * (1048576 * ℓ ^ 2 * n) ≤ 200 * ((m / 100) * m) := by linarith
        exact (Nat.le_of_mul_le_mul_left h4 (by decide : 0 < 200)).trans (Nat.le_add_right _ _)
      exact (Nat.div_le_iff_le_mul_add_pred hm_pos).mpr (by rw [mul_comm m (m / 100)]; exact h2)
    have hL3 : 200000 * ℓ * L ^ 3 ≤ m / 5 := by
      have h5 : 5 * (200000 * ℓ * L ^ 3) = 1000000 * ℓ * L ^ 3 := by ring
      have hle : 5 * (200000 * ℓ * L ^ 3) ≤ m := h5 ▸ hm_log
      omega
    have h100 : 100 ≤ m / 100 := by omega
    omega
  obtain ⟨d_tot, A', hd_pos, hd_le_3, hNice, hA'_card, hA'_prop⟩ :=
    h_lemma_6_3 hℓ hn A hAsub h63_hyp
  set n' := n / d_tot
  have hA'_le_n' : ∀ x ∈ A', 1 ≤ x ∧ x ≤ n' := by
    intro x hx
    refine ⟨(hA'_prop x hx).1, ?_⟩
    have hle : d_tot * x ≤ n := (Finset.mem_Icc.mp (hAsub (hA'_prop x hx).2)).2
    exact (Nat.le_div_iff_mul_le hd_pos).mpr (by rw [mul_comm]; exact hle)
  have hA'_lt_2L : ∀ x ∈ A', x < 2 ^ L := fun x hx =>
    lt_of_le_of_lt ((hA'_le_n' x hx).2.trans (Nat.div_le_self n d_tot)) lt_two_pow_log2P
  -- Split A' = A_core ⊔ A_ext
  obtain ⟨A_core, A_ext, hdisj_ce, hunion_ce, hcore_card, hext_card, hcore_div, hcore_dyad⟩ :=
    split_nice_set h_chernoff_half hℓ hn hL100 (by
      calc 10000 * ℓ * L = 10000 * (ℓ * L) := by ring
        _ ≤ 65536 * (ℓ * L) := Nat.mul_le_mul_right _ (by decide)
        _ = 65536 * ℓ * L := by ring
        _ ≤ m := hm_ge_65536) A' hA'_card hNice
  have hcore_sub : A_core ⊆ A' := hunion_ce ▸ Finset.subset_union_left
  have hext_sub : A_ext ⊆ A' := hunion_ce ▸ Finset.subset_union_right
  -- Split A_core = A_lo ⊔ A_hi at median
  obtain ⟨A_lo, A_hi, hdisj_lh, hunion_lh, hhi_card_eq, hlh_lt⟩ :=
    split_top_k A_core (A_core.card - A_core.card / 2) (Nat.sub_le _ _)
  have hlo_sub : A_lo ⊆ A_core := hunion_lh ▸ Finset.subset_union_left
  have hhi_sub : A_hi ⊆ A_core := hunion_lh ▸ Finset.subset_union_right
  have hlo_card_eq : A_lo.card = A_core.card / 2 := by
    have := Finset.card_union_of_disjoint hdisj_lh
    rw [hunion_lh, hhi_card_eq] at this; omega
  have hlo_ge : m / 16 ≤ A_lo.card := by omega
  have hhi_ge : m / 16 ≤ A_hi.card := by omega
  have hhi_le_lo1 : A_hi.card ≤ A_lo.card + 1 := by omega
  -- Define uniform m_lo and k'
  set m_lo := A_lo.card / (4 * ℓ)
  have hm_lo_ge : m / (80 * ℓ) ≤ m_lo := by
    have h1 : m / 16 ≤ A_lo.card := hlo_ge
    have h2 : (m / (80 * ℓ)) * (4 * ℓ) ≤ m / 16 := by
      have h3 : (m / (80 * ℓ)) * (80 * ℓ) ≤ m := Nat.div_mul_le_self m (80 * ℓ)
      have h4 : 16 * ((m / (80 * ℓ)) * (4 * ℓ)) ≤ m := by
        calc 16 * ((m / (80 * ℓ)) * (4 * ℓ)) = (m / (80 * ℓ)) * (64 * ℓ) := by ring
          _ ≤ (m / (80 * ℓ)) * (80 * ℓ) := Nat.mul_le_mul_left _ (by omega)
          _ ≤ m := h3
      exact (Nat.le_div_iff_mul_le (by decide : 0 < 16)).mpr (by rw [mul_comm]; exact h4)
    exact (Nat.le_div_iff_mul_le (by omega : 0 < 4 * ℓ)).mpr (h2.trans h1)
  have hm_lo_ge_L : 1600 * L ^ 2 ≤ m_lo := by
    have h1 : 80 * ℓ * (1600 * L ^ 2) ≤ m := by
      calc 80 * ℓ * (1600 * L ^ 2) = 128000 * ℓ * L ^ 2 := by ring
        _ ≤ 128000 * ℓ * L ^ 3 := by
            calc 128000 * ℓ * L ^ 2 = 128000 * ℓ * L ^ 2 * 1 := by ring
              _ ≤ 128000 * ℓ * L ^ 2 * L := Nat.mul_le_mul_left _ (by omega)
              _ = 128000 * ℓ * L ^ 3 := by ring
        _ = 128000 * (ℓ * L ^ 3) := by ring
        _ ≤ 1000000 * (ℓ * L ^ 3) := Nat.mul_le_mul_right _ (by decide)
        _ = 1000000 * ℓ * L ^ 3 := by ring
        _ ≤ m := hm_log
    have h2 : 1600 * L ^ 2 ≤ m / (80 * ℓ) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < 80 * ℓ)).mpr (by rw [mul_comm]; exact h1)
    exact h2.trans hm_lo_ge
  have hm_lo_pos : 0 < m_lo := by
    have : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
    omega
  set k' := 8192 * n' / m_lo + 4 * L + 2
  have hk'_ge : 4 * L ≤ k' := by dsimp [k']; exact (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
  -- Check 160 * ℓ * k' ≤ m (which gives BOTH 8 * ℓ * k' ≤ A_hi.card AND 40 * ℓ * k' ≤ m / 4!)
  have hk'_small : 160 * ℓ * k' ≤ m := by
    have hterm1 : 160 * ℓ * (8192 * n' / m_lo) ≤ m / 2 := by
      have h1 : m ≤ 96 * ℓ * m_lo := by
        have h1a : 4 * ℓ * m_lo + 4 * ℓ ≥ A_lo.card := by
          have hdm := Nat.div_add_mod A_lo.card (4 * ℓ)
          change 4 * ℓ * m_lo + A_lo.card % (4 * ℓ) = A_lo.card at hdm
          have hml := Nat.mod_lt A_lo.card (by omega : 0 < 4 * ℓ)
          omega
        have h1b : 16 * A_lo.card + 16 ≥ m := by omega
        have h1c : 4 * ℓ ≤ m / 1000 := by
          have : 65536 * ℓ * 100 ≤ m := by
            calc 65536 * ℓ * 100 ≤ 65536 * ℓ * L := Nat.mul_le_mul_left _ hL100
              _ ≤ m := hm_ge_65536
          omega
        have h1d : 64 * ℓ * m_lo + 64 * ℓ + 16 ≥ m := by linarith
        have h1e : 64 * ℓ + 16 ≤ 32 * ℓ * m_lo := by
          have hm100 : 100 ≤ m_lo := by
            have h1 : 100 ≤ 1600 * L ^ 2 := by
              have : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
              omega
            exact h1.trans hm_lo_ge_L
          calc 64 * ℓ + 16 ≤ 64 * ℓ + 16 * ℓ := by omega
            _ = 80 * ℓ := by ring
            _ ≤ 3200 * ℓ := by omega
            _ = 32 * ℓ * 100 := by ring
            _ ≤ 32 * ℓ * m_lo := Nat.mul_le_mul_left _ hm100
        linarith
      have h2 : (8192 * n' / m_lo) * m_lo ≤ 8192 * n' := Nat.div_mul_le_self _ _
      have h3 : (160 * ℓ * (8192 * n' / m_lo)) * m ≤ (m / 2) * m := by
        have ha : (160 * ℓ * (8192 * n' / m_lo)) * m ≤
            (160 * ℓ * (8192 * n' / m_lo)) * (96 * ℓ * m_lo) := Nat.mul_le_mul_left _ h1
        have hb : (160 * ℓ * (8192 * n' / m_lo)) * (96 * ℓ * m_lo) =
            15360 * ℓ ^ 2 * ((8192 * n' / m_lo) * m_lo) := by ring
        have hc : 15360 * ℓ ^ 2 * ((8192 * n' / m_lo) * m_lo) ≤ 15360 * ℓ ^ 2 * (8192 * n') :=
          Nat.mul_le_mul_left _ h2
        have hd : 15360 * ℓ ^ 2 * (8192 * n') ≤ 125829120 * (ℓ ^ 2 * n) := by
          have hn'le : n' ≤ n := Nat.div_le_self n d_tot
          calc 15360 * ℓ ^ 2 * (8192 * n') = 125829120 * (ℓ ^ 2 * n') := by ring
            _ ≤ 125829120 * (ℓ ^ 2 * n) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hn'le)
        have he : 4 * (125829120 * (ℓ ^ 2 * n)) ≤ m * m := by
          calc 4 * (125829120 * (ℓ ^ 2 * n)) = 503316480 * (ℓ ^ 2 * n) := by ring
            _ ≤ 4294967296 * (ℓ ^ 2 * n) := Nat.mul_le_mul_right _ (by decide)
            _ = (65536 * ℓ) ^ 2 * n := by ring
            _ ≤ m ^ 2 := hm_quad
            _ = m * m := sq m
        have hm2 : m ≤ 4 * (m / 2) := by omega
        have hf : 4 * (125829120 * (ℓ ^ 2 * n)) ≤ 4 * ((m / 2) * m) := by
          calc 4 * (125829120 * (ℓ ^ 2 * n)) ≤ m * m := he
            _ ≤ (4 * (m / 2)) * m := Nat.mul_le_mul_right m hm2
            _ = 4 * ((m / 2) * m) := by ring
        have hg : 125829120 * (ℓ ^ 2 * n) ≤ (m / 2) * m := Nat.le_of_mul_le_mul_left hf (by decide)
        linarith
      exact Nat.le_of_mul_le_mul_right h3 hm_pos
    have hterm2 : 160 * ℓ * (4 * L + 2) ≤ m / 2 := by
      have : 160 * ℓ * (4 * L + 2) ≤ 1000 * ℓ * L := by
        calc 160 * ℓ * (4 * L + 2) = 640 * ℓ * L + 320 * ℓ := by ring
          _ ≤ 640 * ℓ * L + 320 * ℓ * L := by
              have : 320 * ℓ ≤ 320 * ℓ * L := Nat.le_mul_of_pos_right _ (by omega)
              omega
          _ = 960 * (ℓ * L) := by ring
          _ ≤ 1000 * (ℓ * L) := Nat.mul_le_mul_right _ (by decide)
          _ = 1000 * ℓ * L := by ring
      have h2000 : 2 * (1000 * ℓ * L) ≤ m := by
        calc 2 * (1000 * ℓ * L) = 2000 * (ℓ * L) := by ring
          _ ≤ 65536 * (ℓ * L) := Nat.mul_le_mul_right _ (by decide)
          _ = 65536 * ℓ * L := by ring
          _ ≤ m := hm_ge_65536
      omega
    have hsplit : 160 * ℓ * k' = 160 * ℓ * (8192 * n' / m_lo) + 160 * ℓ * (4 * L + 2) := by
      dsimp [k']; ring
    omega
  have h8lk_le_hi : 8 * ℓ * k' ≤ A_hi.card := by
    have h16 : 16 * (8 * ℓ * k') ≤ m := by
      calc 16 * (8 * ℓ * k') = 128 * (ℓ * k') := by ring
        _ ≤ 160 * (ℓ * k') := Nat.mul_le_mul_right _ (by decide)
        _ = 160 * ℓ * k' := by ring
        _ ≤ m := hk'_small
    omega
  -- Split X = top 8 * ℓ * k' elements of A_hi
  obtain ⟨A_hi_rem, X, hdisj_rX, hunion_rX, hX_card, hrX_lt⟩ :=
    split_top_k A_hi (8 * ℓ * k') h8lk_le_hi
  have hX_sub_hi : X ⊆ A_hi := hunion_rX ▸ Finset.subset_union_right
  have hX_sub_core : X ⊆ A_core := hX_sub_hi.trans hhi_sub
  set M := X.sum id
  -- Every element of A_core \ X is strictly smaller than every element of X
  have hX_suffix : ∀ a ∈ A_core, ∀ x ∈ X, a ∉ X → a < x := by
    intro a ha x hx hanotX
    rw [← hunion_lh] at ha
    rcases Finset.mem_union.mp ha with halo | hahi
    · exact hlh_lt a halo x (hX_sub_hi hx)
    · rw [← hunion_rX] at hahi
      rcases Finset.mem_union.mp hahi with hrem | hx'
      · exact hrX_lt a hrem x hx
      · exact absurd hx' hanotX
  -- Minimum dyadic index j1 of X
  have hX_ne : X.Nonempty := Finset.card_pos.mp (by rw [hX_card]; exact Nat.mul_pos (Nat.mul_pos (by decide) hℓ) (by omega))
  set xmin := X.min' hX_ne
  have hxmin_X : xmin ∈ X := Finset.min'_mem X hX_ne
  set j1 := Nat.log 2 xmin
  have hj1_lt_L : j1 < L := by
    have h1 : xmin < 2 ^ L := hA'_lt_2L xmin (hcore_sub (hX_sub_core hxmin_X))
    have h2 : 2 ^ j1 ≤ xmin := Nat.pow_log_le_self 2 (by have := (hA'_le_n' xmin (hcore_sub (hX_sub_core hxmin_X))).1; omega)
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h2 h1)
  have hX_ge_j1 : ∀ x ∈ X, 2 ^ j1 ≤ x := by
    intro x hx
    have h1 : 2 ^ j1 ≤ xmin := Nat.pow_log_le_self 2 (by have := (hA'_le_n' xmin (hcore_sub (hX_sub_core hxmin_X))).1; omega)
    exact h1.trans (Finset.min'_le X x hx)
  have hxmin_lt : xmin < 2 ^ (j1 + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) xmin
  -- For any j > j1, A_core ∩ I_j = X ∩ I_j
  have hX_eq_core_gt : ∀ j > j1,
      A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) =
      X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) := by
    intro j hj
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨haC, ha1, ha2⟩
      refine ⟨?_, ha1, ha2⟩
      by_contra hanotX
      have halt : a < xmin := hX_suffix a haC xmin hxmin_X hanotX
      have hpow : 2 ^ (j1 + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) hj
      omega
    · rintro ⟨haX, ha1, ha2⟩
      exact ⟨hX_sub_core haX, ha1, ha2⟩
  -- Lower bound on M: M ≥ 8 * ℓ * k' * 2^j1 AND M ≥ 32 * ℓ * 2^j_max (so Q = 10*M/ℓ ≥ max(A')!)
  have hM_ge_j1 : 8 * ℓ * k' * 2 ^ j1 ≤ M := by
    calc 8 * ℓ * k' * 2 ^ j1 = X.card * 2 ^ j1 := by rw [hX_card]
      _ = ∑ _x ∈ X, 2 ^ j1 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ x ∈ X, x := Finset.sum_le_sum hX_ge_j1
      _ = M := rfl
  -- Also M ≥ 16 * ℓ * x_max for every x ∈ A'
  have hM_ge_all : ∀ x ∈ A', 16 * ℓ * x ≤ M := by
    intro x hx
    set jx := Nat.log 2 x
    have hjx_lt_L : jx < L := by
      have h1 := hA'_lt_2L x hx
      have h2 : 2 ^ jx ≤ x := Nat.pow_log_le_self 2 (by have := (hA'_le_n' x hx).1; omega)
      exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h2 h1)
    have hxj1 : 2 ^ jx ≤ x ∧ x < 2 ^ (jx + 1) :=
      ⟨Nat.pow_log_le_self 2 (by have := (hA'_le_n' x hx).1; omega),
       Nat.lt_pow_succ_log_self (by decide : 1 < 2) x⟩
    have hdy_core : 64 * ℓ * L ≤ (A_core.filter (fun a => 2 ^ jx ≤ a ∧ a < 2 ^ (jx + 1))).card :=
      hcore_dyad jx hjx_lt_L ⟨x, Finset.mem_filter.mpr ⟨hx, hxj1⟩⟩
    -- At least 32 * ℓ elements of X are ≥ 2^jx (since either all of X is ≥ 2^jx or A_core ∩ I_jx ⊆ X)
    have h32_ge : 32 * ℓ * 2 ^ jx ≤ M := by
      by_cases hle : jx ≤ j1
      · have hpow : 2 ^ jx ≤ 2 ^ j1 := Nat.pow_le_pow_right (by decide) hle
        have h1 : 32 * ℓ ≤ 8 * ℓ * k' := by
          have : 4 ≤ k' := by omega
          calc 32 * ℓ = 8 * ℓ * 4 := by ring
            _ ≤ 8 * ℓ * k' := Nat.mul_le_mul_left _ this
        exact (Nat.mul_le_mul h1 hpow).trans hM_ge_j1
      · have hgt : j1 < jx := by omega
        have heq := hX_eq_core_gt jx hgt
        set Xjx := X.filter (fun a => 2 ^ jx ≤ a ∧ a < 2 ^ (jx + 1))
        have hcard_ge : 32 * ℓ ≤ Xjx.card := by
          rw [← heq]
          have : 32 * ℓ ≤ 64 * ℓ * L := by
            have : 1 ≤ L := by omega
            calc 32 * ℓ ≤ 64 * ℓ := by omega
              _ ≤ 64 * ℓ * L := Nat.le_mul_of_pos_right _ this
          exact this.trans hdy_core
        calc 32 * ℓ * 2 ^ jx ≤ Xjx.card * 2 ^ jx := Nat.mul_le_mul_right _ hcard_ge
          _ = ∑ _a ∈ Xjx, 2 ^ jx := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ a ∈ Xjx, a := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.1
          _ ≤ ∑ a ∈ X, a := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    calc 16 * ℓ * x ≤ 16 * ℓ * (2 * 2 ^ jx) := Nat.mul_le_mul_left _ (by rw [← pow_succ']; omega)
      _ = 32 * ℓ * 2 ^ jx := by ring
      _ ≤ M := h32_ge
  -- Obtain good coloring f : A_core → Fin ℓ × Bool
  obtain ⟨f, hf⟩ := exists_good_coloring h_chernoff_lower h_chernoff_upper hℓ hn hL_big hm_ge_65536
    hk'_ge A_core A_lo A_hi X hlo_sub hhi_sub hX_sub_hi hlo_ge hhi_ge hX_card hcore_div
  -- Define parts P i, B1 i, B2 i, and S i = subsetSumLe (13 * k' + 1) (P i)
  let C_all (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, false), (i, true)}
  let C_f (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, false)}
  let C_t (i : Fin ℓ) : Finset (Fin ℓ × Bool) := {(i, true)}
  let img (S : Finset ℕ) (C : Finset (Fin ℓ × Bool)) : Finset ℕ :=
    (Finset.univ.filter (fun x : A_core => x.1 ∈ S ∧ f x ∈ C)).image Subtype.val
  let P (i : Fin ℓ) : Finset ℕ := img A_core (C_all i)
  let B1 (i : Fin ℓ) : Finset ℕ := img A_lo (C_all i) ∪ img A_hi (C_f i)
  let B2 (i : Fin ℓ) : Finset ℕ := img X (C_t i)
  let S (i : Fin ℓ) : Finset ℕ := subsetSumLe (13 * k' + 1) (P i)
  set Q := 10 * M / ℓ
  -- Verify P i pairwise disjoint and ⊆ A_core
  have hP_sub : ∀ i : Fin ℓ, P i ⊆ A_core := by
    intro i a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    exact x.2
  have hP_disj : ∀ i j : Fin ℓ, i ≠ j → Disjoint (P i) (P j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨x1, hx1, rfl⟩ := Finset.mem_image.mp ha1
    obtain ⟨x2, hx2, heq⟩ := Finset.mem_image.mp ha2
    have h1 := (Finset.mem_filter.mp hx1).2.2
    have h2 := (Finset.mem_filter.mp hx2).2.2
    rw [Subtype.ext heq.symm] at h1
    simp only [C_all, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      exact hij (congrArg Prod.fst (h1.symm.trans h2))
  -- Verify B1 i, B2 i disjoint and B1 i ∪ B2 i ⊆ P i
  have hB12_disj : ∀ i : Fin ℓ, Disjoint (B1 i) (B2 i) := by
    intro i
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    obtain ⟨x2, hx2, rfl⟩ := Finset.mem_image.mp ha2
    have hx2X := (Finset.mem_filter.mp hx2).2.1
    have hx2f := (Finset.mem_filter.mp hx2).2.2
    rcases Finset.mem_union.mp ha1 with halo | hahi
    · obtain ⟨x1, hx1, heq⟩ := Finset.mem_image.mp halo
      have hx1lo := (Finset.mem_filter.mp hx1).2.1
      rw [Subtype.ext heq] at hx1lo
      exact Finset.disjoint_left.mp hdisj_lh hx1lo (hX_sub_hi hx2X)
    · obtain ⟨x1, hx1, heq⟩ := Finset.mem_image.mp hahi
      have hx1f := (Finset.mem_filter.mp hx1).2.2
      rw [Subtype.ext heq] at hx1f
      simp only [C_f, C_t, Finset.mem_singleton] at hx1f hx2f
      have := hx1f.symm.trans hx2f
      cases this
  have hB12_sub_P : ∀ i : Fin ℓ, B1 i ∪ B2 i ⊆ P i := by
    intro i a ha
    rcases Finset.mem_union.mp ha with ha1 | ha2
    · rcases Finset.mem_union.mp ha1 with halo | hahi
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp halo
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, x.2, (Finset.mem_filter.mp hx).2.2⟩, rfl⟩
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hahi
        have hfx := (Finset.mem_filter.mp hx).2.2
        simp only [C_f, Finset.mem_singleton] at hfx
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, x.2, by simp [C_all, hfx]⟩, rfl⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha2
      have hfx := (Finset.mem_filter.mp hx).2.2
      simp only [C_t, Finset.mem_singleton] at hfx
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
        ⟨Finset.mem_univ x, x.2, by simp [C_all, hfx]⟩, rfl⟩
  -- Claim 2 (upper bound): every element of S i is ≤ Q = 10 * M / ℓ
  have hS_sub_Q : ∀ i : Fin ℓ, S i ⊆ Finset.Icc 0 Q := by
    intro i s hs
    obtain ⟨Y, hYf, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hYP, hYcard⟩ := Finset.mem_filter.mp hYf
    have hYP' : Y ⊆ P i := Finset.mem_powerset.mp hYP
    refine Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩
    set Ylo := Y.filter (fun a => a < 2 ^ (j1 + 1))
    set Yhi := Y.filter (fun a => ¬ a < 2 ^ (j1 + 1))
    have hYsum : Y.sum id = Ylo.sum id + Yhi.sum id := by
      have hdisjY : Disjoint Ylo Yhi := by
        rw [Finset.disjoint_left]; intro a ha1 ha2
        exact (Finset.mem_filter.mp ha2).2 (Finset.mem_filter.mp ha1).2
      rw [← Finset.sum_union hdisjY, Finset.filter_union_filter_not_eq]
    have hYlo_le : ℓ * Ylo.sum id ≤ 4 * M := by
      have h1 : Ylo.sum id ≤ Ylo.card * 2 ^ (j1 + 1) := by
        calc Ylo.sum id ≤ ∑ _a ∈ Ylo, 2 ^ (j1 + 1) :=
              Finset.sum_le_sum fun a ha => Nat.le_of_lt (Finset.mem_filter.mp ha).2
          _ = Ylo.card * 2 ^ (j1 + 1) := by rw [Finset.sum_const, smul_eq_mul]
      have h2 : Ylo.card ≤ 14 * k' := by
        have hsub_c : Ylo.card ≤ Y.card := Finset.card_le_card (Finset.filter_subset _ Y)
        omega
      calc ℓ * Ylo.sum id ≤ ℓ * ((14 * k') * (2 * 2 ^ j1)) := by
            rw [← pow_succ']; exact Nat.mul_le_mul_left ℓ (h1.trans (Nat.mul_le_mul_right _ h2))
        _ = 28 * ℓ * k' * 2 ^ j1 := by ring
        _ ≤ 32 * ℓ * k' * 2 ^ j1 := by
            have : 28 ≤ 32 := by decide
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this))
        _ = 4 * (8 * ℓ * k' * 2 ^ j1) := by ring
        _ ≤ 4 * M := Nat.mul_le_mul_left 4 hM_ge_j1
    have hYhi_le : ℓ * Yhi.sum id ≤ 6 * M := by
      set Jgt := (Finset.range L).filter (fun j => j1 < j)
      have hYhi_sub : Yhi ⊆ Jgt.biUnion (fun j => (P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
        intro a ha
        obtain ⟨haY, hage⟩ := Finset.mem_filter.mp ha
        have haP : a ∈ P i := hYP' haY
        have haA' : a ∈ A' := hcore_sub (hP_sub i haP)
        set ja := Nat.log 2 a
        have hja_lt : ja < L := by
          have h1 := hA'_lt_2L a haA'
          have h2 : 2 ^ ja ≤ a := Nat.pow_log_le_self 2 (by have := (hA'_le_n' a haA').1; omega)
          exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h2 h1)
        have hja_gt : j1 < ja := by
          by_contra hle; push Not at hle
          have h1 : a < 2 ^ (ja + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
          have h2 : 2 ^ (ja + 1) ≤ 2 ^ (j1 + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          have hage' : 2 ^ (j1 + 1) ≤ a := Nat.le_of_not_lt hage
          omega
        refine Finset.mem_biUnion.mpr ⟨ja, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hja_lt, hja_gt⟩,
          Finset.mem_filter.mpr ⟨haP, Nat.pow_log_le_self 2 (by have := (hA'_le_n' a haA').1; omega),
            Nat.lt_pow_succ_log_self (by decide : 1 < 2) a⟩⟩
      have hP_disj_Jgt : Set.PairwiseDisjoint (Jgt : Set ℕ)
          (fun j => (P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
        intro j1' _ j2' _ hne
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1' + 1 ≤ j2'); omega
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j2' + 1 ≤ j1'); omega
      have hYhi_sum : Yhi.sum id ≤ ∑ j ∈ Jgt,
          ((P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id := by
        rw [← Finset.sum_biUnion hP_disj_Jgt]
        exact Finset.sum_le_sum_of_subset hYhi_sub
      have hterm_j : ∀ j ∈ Jgt,
          ℓ * ((P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id ≤
            6 * (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id := by
        intro j hj
        obtain ⟨hjR, hjgt⟩ := Finset.mem_filter.mp hj
        have hjL := Finset.mem_range.mp hjR
        set Pj := (P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
        set Cj := A_core.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
        set Xj := X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
        have hCj_eq_Xj : Cj = Xj := hX_eq_core_gt j hjgt
        by_cases hne : (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).Nonempty
        · have hCj_ge : 64 * ℓ * L ≤ Cj.card := hcore_dyad j hjL hne
          have hE6 := (hf i).2.2.2.2.2 j hjL hCj_ge
          have hPj_eq : Pj = img Cj (C_all i) := by
            ext a
            simp only [Pj, P, Cj, img, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
              true_and, Subtype.exists]
            constructor
            · rintro ⟨⟨x, hxC, ⟨_, hfx⟩, rfl⟩, ha1, ha2⟩
              exact ⟨x, hxC, ⟨⟨hxC, ha1, ha2⟩, hfx⟩, rfl⟩
            · rintro ⟨x, hxC, ⟨⟨_, ha1, ha2⟩, hfx⟩, rfl⟩
              exact ⟨⟨x, hxC, ⟨hxC, hfx⟩, rfl⟩, ha1, ha2⟩
          change ℓ * (img Cj (C_all i)).card < 3 * Cj.card at hE6
          rw [← hPj_eq] at hE6
          have hPj_sum : Pj.sum id ≤ Pj.card * 2 ^ (j + 1) := by
            calc Pj.sum id ≤ ∑ _a ∈ Pj, 2 ^ (j + 1) :=
                  Finset.sum_le_sum fun a ha => Nat.le_of_lt (Finset.mem_filter.mp ha).2.2
              _ = Pj.card * 2 ^ (j + 1) := by rw [Finset.sum_const, smul_eq_mul]
          have hXj_sum : Xj.card * 2 ^ j ≤ Xj.sum id := by
            calc Xj.card * 2 ^ j = ∑ _a ∈ Xj, 2 ^ j := by rw [Finset.sum_const, smul_eq_mul]
              _ ≤ ∑ a ∈ Xj, a := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.1
          calc ℓ * Pj.sum id ≤ ℓ * (Pj.card * (2 * 2 ^ j)) := by
                rw [← pow_succ']; exact Nat.mul_le_mul_left ℓ hPj_sum
            _ = (ℓ * Pj.card) * (2 * 2 ^ j) := by ring
            _ ≤ (3 * Cj.card) * (2 * 2 ^ j) := Nat.mul_le_mul_right _ (Nat.le_of_lt hE6)
            _ = 6 * (Xj.card * 2 ^ j) := by rw [hCj_eq_Xj]; ring
            _ ≤ 6 * Xj.sum id := Nat.mul_le_mul_left 6 hXj_sum
        · have hPj_emp : Pj = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro a ha
            obtain ⟨haP, ha1, ha2⟩ := Finset.mem_filter.mp ha
            exact hne ⟨a, Finset.mem_filter.mpr ⟨hcore_sub (hP_sub i haP), ha1, ha2⟩⟩
          simp [hPj_emp]
      have hX_disj : Set.PairwiseDisjoint (Jgt : Set ℕ)
          (fun j => X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
        intro j1' _ j2' _ hne
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1' + 1 ≤ j2')
          omega
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j2' + 1 ≤ j1')
          omega
      have hX_sum_le : ∑ j ∈ Jgt, (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id ≤ M := by
        rw [← Finset.sum_biUnion hX_disj]
        exact Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr fun j _ => Finset.filter_subset _ _)
      calc ℓ * Yhi.sum id
          ≤ ℓ * ∑ j ∈ Jgt, ((P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id :=
            Nat.mul_le_mul_left ℓ hYhi_sum
        _ = ∑ j ∈ Jgt, (ℓ * ((P i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id) :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ Jgt, (6 * (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id) :=
            Finset.sum_le_sum hterm_j
        _ = 6 * ∑ j ∈ Jgt, (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id :=
            (Finset.mul_sum _ _ _).symm
        _ ≤ 6 * M := Nat.mul_le_mul_left 6 hX_sum_le
    have htot : ℓ * Y.sum id ≤ 10 * M := by
      rw [hYsum, mul_add]; omega
    exact (Nat.le_div_iff_mul_le hℓ).mpr (by rw [mul_comm]; exact htot)
  -- Claim 1 (lower bound): Q ≤ α_inv * (S i).card (with α_inv = 4096)
  have hS_dense : ∀ i : Fin ℓ, Q ≤ α_inv * (S i).card := by
    intro i
    obtain ⟨hE1, hE2, hE4, hE3, hE5, _⟩ := hf i
    set A_inj := img A_lo (C_all i)
    have hAinj_gt : m_lo < A_inj.card := by
      have h1 : 4 * ℓ * m_lo ≤ A_lo.card := Nat.mul_div_le A_lo.card (4 * ℓ)
      have h2 : 4 * ℓ * m_lo < 4 * ℓ * A_inj.card := lt_of_le_of_lt h1 hE1
      exact Nat.lt_of_mul_lt_mul_left h2
    have hB1_le_16 : (B1 i).card ≤ 16 * A_inj.card := by
      have h1 : (B1 i).card ≤ A_inj.card + (img A_hi (C_f i)).card := Finset.card_union_le _ _
      have h2 : (img A_hi (C_f i)).card ≤ 15 * A_inj.card := by
        have ha : 2 * ℓ * (img A_hi (C_f i)).card < 3 * A_hi.card := hE2
        have hb : 3 * A_hi.card ≤ 3 * (A_lo.card + 1) := by omega
        have hc : 3 * (A_lo.card + 1) ≤ 30 * ℓ * A_inj.card := by
          have : 4 * ℓ ≤ 4 * ℓ * A_inj.card := Nat.le_mul_of_pos_right _ (by omega)
          linarith
        have hd : 2 * ℓ * (img A_hi (C_f i)).card ≤ 2 * ℓ * (15 * A_inj.card) := by linarith
        exact Nat.le_of_mul_le_mul_left hd (by omega)
      omega
    have hB2_card_le : (B2 i).card ≤ 12 * k' := by
      have h1 : 2 * ℓ * (B2 i).card < 3 * (8 * ℓ * k') := hX_card ▸ hE4
      have h2 : 2 * ℓ * (B2 i).card ≤ 2 * ℓ * (12 * k') := by linarith
      exact Nat.le_of_mul_le_mul_left h2 (by omega)
    -- Apply Lemma 6.2 to B1 i for every b ∈ B2 i
    have hg : ∀ b ∈ B2 i, 0 < b ∧ b / 4 ≤ (subsetSumModLe b (k' + 1) (B1 i)).card := by
      intro b hb
      obtain ⟨xb, hxb, rfl⟩ := Finset.mem_image.mp hb
      have hbX : xb.1 ∈ X := (Finset.mem_filter.mp hxb).2.1
      have hbhi : xb.1 ∈ A_hi := hX_sub_hi hbX
      have hbA' : xb.1 ∈ A' := hcore_sub (hhi_sub hbhi)
      have hb_le_n' : xb.1 ≤ n' := (hA'_le_n' xb.1 hbA').2
      have hb_ge_8 : 8 ≤ xb.1 := by
        have hsub_lo : A_lo ⊆ Finset.Icc 1 xb.1 := fun x hx =>
          Finset.mem_Icc.mpr ⟨(hA'_le_n' x (hcore_sub (hlo_sub hx))).1, Nat.le_of_lt (hlh_lt x hx xb.1 hbhi)⟩
        have hle := Finset.card_le_card hsub_lo
        simp only [Nat.card_Icc, add_tsub_cancel_right] at hle
        omega
      have hLble : log2P xb.1 ≤ L := log2P_mono (hb_le_n'.trans (Nat.div_le_self n d_tot))
      have h62_m1 : 1600 * (log2P xb.1) ^ 2 ≤ A_inj.card := by
        have : (log2P xb.1) ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hLble 2
        calc 1600 * (log2P xb.1) ^ 2 ≤ 1600 * L ^ 2 := Nat.mul_le_mul_left 1600 this
          _ ≤ m_lo := hm_lo_ge_L
          _ ≤ A_inj.card := Nat.le_of_lt hAinj_gt
      have h62_div : ∀ d : ℕ, d ∣ xb.1 → 2 ≤ d → d ≤ 8 * xb.1 / A_inj.card →
          1200 * (log2P xb.1) ^ 2 + 8 * d ≤ ((B1 i).filter (fun a => ¬ d ∣ a)).card := by
        intro d _ hd2 hdub
        have hd_ub_nice : d ≤ 1024 * ℓ * n / m := by
          have h1 : 8 * xb.1 / A_inj.card ≤ 8 * n / (m / (80 * ℓ)) :=
            Nat.div_le_div (Nat.mul_le_mul_left 8 (hb_le_n'.trans (Nat.div_le_self n d_tot)))
              (hm_lo_ge.trans (Nat.le_of_lt hAinj_gt)) (by
                have h80 : 80 * ℓ ≤ m := by
                  have h1 : 80 * ℓ ≤ 65536 * ℓ * L := by
                    calc 80 * ℓ = 80 * ℓ * 1 := by ring
                      _ ≤ 65536 * ℓ * L := Nat.mul_le_mul (by omega) (by omega)
                  exact h1.trans hm_ge_65536
                exact Nat.ne_of_gt (Nat.div_pos h80 (by omega)))
          have h2 : 8 * n / (m / (80 * ℓ)) ≤ 1024 * ℓ * n / m := by
            have h80m : m ≤ 128 * ℓ * (m / (80 * ℓ)) := by
              have hdiv_ge : 80 * ℓ * (m / (80 * ℓ)) + 80 * ℓ ≥ m := by
                have := Nat.div_add_mod m (80 * ℓ)
                have := Nat.mod_lt m (by omega : 0 < 80 * ℓ)
                omega
              have hbig : 80 * ℓ ≤ 48 * ℓ * (m / (80 * ℓ)) := by
                have h10 : 10 ≤ m / (80 * ℓ) := by
                  have : 800 * ℓ ≤ m := by
                    have h1 : 800 * ℓ ≤ 65536 * ℓ * L := by
                      calc 800 * ℓ = 800 * ℓ * 1 := by ring
                        _ ≤ 65536 * ℓ * L := Nat.mul_le_mul (by omega) (by omega)
                    exact h1.trans hm_ge_65536
                  exact (Nat.le_div_iff_mul_le (by omega : 0 < 80 * ℓ)).mpr (by linarith)
                calc 80 * ℓ ≤ 480 * ℓ := by omega
                  _ = 48 * ℓ * 10 := by ring
                  _ ≤ 48 * ℓ * (m / (80 * ℓ)) := Nat.mul_le_mul_left _ h10
              linarith
            have h3 : (8 * n / (m / (80 * ℓ))) * m ≤ 1024 * ℓ * n := by
              calc (8 * n / (m / (80 * ℓ))) * m
                  ≤ (8 * n / (m / (80 * ℓ))) * (128 * ℓ * (m / (80 * ℓ))) := Nat.mul_le_mul_left _ h80m
                _ = 128 * ℓ * ((8 * n / (m / (80 * ℓ))) * (m / (80 * ℓ))) := by ring
                _ ≤ 128 * ℓ * (8 * n) := Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
                _ = 1024 * ℓ * n := by ring
            exact (Nat.le_div_iff_mul_le hm_pos).mpr h3
          exact hdub.trans (h1.trans h2)
        have hE3d := hE3 d hd2 hd_ub_nice
        have hcore_d := hcore_div d hd2 hd_ub_nice
        -- Show img (A_core.filter (¬ d ∣ ·)) (C_f i) ⊆ (B1 i).filter (¬ d ∣ ·)
        have hsub_d : img (A_core.filter (fun a => ¬ d ∣ a)) (C_f i) ⊆
            (B1 i).filter (fun a => ¬ d ∣ a) := by
          intro a ha
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨hxF, hfx⟩ := (Finset.mem_filter.mp hx).2
          have hnd := (Finset.mem_filter.mp hxF).2
          refine Finset.mem_filter.mpr ⟨?_, hnd⟩
          have hxC : x.1 ∈ A_lo ∪ A_hi := hunion_lh ▸ x.2
          rcases Finset.mem_union.mp hxC with hxlo | hxhi
          · apply Finset.mem_union_left
            simp only [C_f, Finset.mem_singleton] at hfx
            exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
              ⟨Finset.mem_univ x, hxlo, by simp [C_all, hfx]⟩, rfl⟩
          · apply Finset.mem_union_right
            exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxhi, hfx⟩, rfl⟩
        have hcard_le := Finset.card_le_card hsub_d
        have h1 : 8 * ℓ * (1200 * (log2P xb.1) ^ 2 + 8 * d) ≤ (A_core.filter (fun a => ¬ d ∣ a)).card := by
          have hL2 : (log2P xb.1) ^ 2 ≤ L ^ 2 := Nat.pow_le_pow_left hLble 2
          calc 8 * ℓ * (1200 * (log2P xb.1) ^ 2 + 8 * d)
              = 9600 * ℓ * (log2P xb.1) ^ 2 + 64 * ℓ * d := by ring
            _ ≤ 16000 * ℓ * L ^ 2 + 128 * ℓ * d := by
                have ha : 9600 * ℓ * (log2P xb.1) ^ 2 ≤ 16000 * ℓ * L ^ 2 := by
                  calc 9600 * ℓ * (log2P xb.1) ^ 2 ≤ 9600 * ℓ * L ^ 2 := Nat.mul_le_mul_left _ hL2
                    _ = 9600 * (ℓ * L ^ 2) := by ring
                    _ ≤ 16000 * (ℓ * L ^ 2) := Nat.mul_le_mul_right _ (by decide)
                    _ = 16000 * ℓ * L ^ 2 := by ring
                have hb : 64 * ℓ * d ≤ 128 * ℓ * d := by
                  calc 64 * ℓ * d = 64 * (ℓ * d) := by ring
                    _ ≤ 128 * (ℓ * d) := Nat.mul_le_mul_right _ (by decide)
                    _ = 128 * ℓ * d := by ring
                omega
            _ ≤ (A_core.filter (fun a => ¬ d ∣ a)).card := hcore_d
        have h2 : 8 * ℓ * (1200 * (log2P xb.1) ^ 2 + 8 * d) < 8 * ℓ * ((B1 i).filter (fun a => ¬ d ∣ a)).card :=
          lt_of_le_of_lt h1 (lt_of_lt_of_le hE3d (Nat.mul_le_mul_left _ hcard_le))
        exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_left h2)
      have h62 := h_lemma_6_2 (by omega : 2 ≤ xb.1) (B1 i) A_inj Finset.subset_union_left
        (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
          exact hlh_lt y.1 (Finset.mem_filter.mp hy).2.1 xb.1 hbhi)
        hB1_le_16 h62_m1 h62_div
      -- Verify min (A_inj.card^2 / 131072) (xb.1 / 4) = xb.1 / 4 and k_b ≤ k'
      have hmin_eq : xb.1 / 4 ≤ A_inj.card * A_inj.card / 131072 := by
        have hm1_big_sq : 131072 * xb.1 ≤ 4 * (A_inj.card * A_inj.card) := by
          have h1 : m ≤ 96 * ℓ * m_lo := by
            have h1a : 4 * ℓ * m_lo + 4 * ℓ ≥ A_lo.card := by
              have hdm := Nat.div_add_mod A_lo.card (4 * ℓ)
              change 4 * ℓ * m_lo + A_lo.card % (4 * ℓ) = A_lo.card at hdm
              have hml := Nat.mod_lt A_lo.card (by omega : 0 < 4 * ℓ)
              omega
            have h1b : 16 * A_lo.card + 16 ≥ m := by omega
            have h1e : 64 * ℓ + 16 ≤ 32 * ℓ * m_lo := by
              have hm100 : 100 ≤ m_lo := by
                have h1 : 100 ≤ 1600 * L ^ 2 := by
                  have : 1 ≤ L ^ 2 := Nat.one_le_pow 2 L (by omega)
                  omega
                exact h1.trans hm_lo_ge_L
              calc 64 * ℓ + 16 ≤ 64 * ℓ + 16 * ℓ := by omega
                _ = 80 * ℓ := by ring
                _ ≤ 3200 * ℓ := by omega
                _ = 32 * ℓ * 100 := by ring
                _ ≤ 32 * ℓ * m_lo := Nat.mul_le_mul_left _ hm100
            linarith
          have h2 : m * m ≤ (96 * ℓ * A_inj.card) * (96 * ℓ * A_inj.card) := by
            have : m ≤ 96 * ℓ * A_inj.card := h1.trans (Nat.mul_le_mul_left _ (Nat.le_of_lt hAinj_gt))
            exact Nat.mul_le_mul this this
          have h3 : 4294967296 * ℓ ^ 2 * xb.1 ≤ (96 * ℓ) ^ 2 * (A_inj.card * A_inj.card) := by
            calc 4294967296 * ℓ ^ 2 * xb.1 ≤ 4294967296 * ℓ ^ 2 * n :=
                  Nat.mul_le_mul_left _ (hb_le_n'.trans (Nat.div_le_self n d_tot))
              _ = (65536 * ℓ) ^ 2 * n := by ring
              _ ≤ m ^ 2 := hm_quad
              _ = m * m := sq m
              _ ≤ (96 * ℓ * A_inj.card) * (96 * ℓ * A_inj.card) := h2
              _ = (96 * ℓ) ^ 2 * (A_inj.card * A_inj.card) := by ring
          have h4 : (96 * ℓ) ^ 2 * (131072 * xb.1) ≤ (96 * ℓ) ^ 2 * (4 * (A_inj.card * A_inj.card)) := by
            calc (96 * ℓ) ^ 2 * (131072 * xb.1) = 1207959552 * (ℓ ^ 2 * xb.1) := by ring
              _ ≤ 17179869184 * (ℓ ^ 2 * xb.1) := Nat.mul_le_mul_right _ (by decide)
              _ = 4 * (4294967296 * ℓ ^ 2 * xb.1) := by ring
              _ ≤ 4 * ((96 * ℓ) ^ 2 * (A_inj.card * A_inj.card)) := Nat.mul_le_mul_left 4 h3
              _ = (96 * ℓ) ^ 2 * (4 * (A_inj.card * A_inj.card)) := by ring
          exact Nat.le_of_mul_le_mul_left h4 (by positivity)
        have hdiv : 131072 * (xb.1 / 4) ≤ A_inj.card * A_inj.card := by
          have : 4 * (131072 * (xb.1 / 4)) ≤ 131072 * xb.1 := by
            calc 4 * (131072 * (xb.1 / 4)) = 131072 * (4 * (xb.1 / 4)) := by ring
              _ ≤ 131072 * xb.1 := Nat.mul_le_mul_left _ (Nat.mul_div_le xb.1 4)
          omega
        exact (Nat.le_div_iff_mul_le (by decide : 0 < 131072)).mpr (by rw [mul_comm]; exact hdiv)
      have hkb_le : 8192 * xb.1 / A_inj.card + 2 ≤ k' := by
        have h1 : 8192 * xb.1 / A_inj.card ≤ 8192 * n' / m_lo :=
          Nat.div_le_div (Nat.mul_le_mul_left 8192 hb_le_n') (Nat.le_of_lt hAinj_gt) (Nat.ne_of_gt hm_lo_pos)
        omega
      have hmono_mod : subsetSumModLe xb.1 (8192 * xb.1 / A_inj.card + 2 + 1) (B1 i) ⊆
          subsetSumModLe xb.1 (k' + 1) (B1 i) := by
        apply Finset.image_subset_image
        intro x hx
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hTp, hTc⟩ := Finset.mem_filter.mp hT
        exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr ⟨hTp, by omega⟩, rfl⟩
      refine ⟨by omega, ?_⟩
      exact (le_min hmin_eq le_rfl).trans (h62.trans (Finset.card_le_card hmono_mod))
    -- Iterated Lemma 2.5 gives ∑_{b ∈ B2 i} (b / 4) ≤ (S i).card
    have hiter := card_subsetSumLe_iter_vadd h_card_union_vadd h_subsetSumLe_ins (B1 i) (B2 i) (hB12_disj i) (k' + 1) (fun b => b / 4) hg
    have hS_ge_sum : ∑ b ∈ B2 i, (b / 4) ≤ (S i).card := by
      have hsub_S : subsetSumLe (k' + 1 + (B2 i).card) (B1 i ∪ B2 i) ⊆ S i := by
        intro x hx
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨hTp, hTc⟩ := Finset.mem_filter.mp hT
        exact Finset.mem_image.mpr ⟨T, Finset.mem_filter.mpr
          ⟨Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hTp).trans (hB12_sub_P i)), by omega⟩, rfl⟩
      exact hiter.trans (Finset.card_le_card hsub_S)
    -- Bound (B2 i).sum id ≤ 8 * (S i).card (since every b ∈ B2 i has b ≥ 8, so b ≤ 8 * (b / 4))
    have hB2_sum_le : (B2 i).sum id ≤ 8 * (S i).card := by
      have h1 : ∀ b ∈ B2 i, b ≤ 8 * (b / 4) := by
        intro b hb
        obtain ⟨xb, hxb, rfl⟩ := Finset.mem_image.mp hb
        have hbhi : xb.1 ∈ A_hi := hX_sub_hi (Finset.mem_filter.mp hxb).2.1
        have hsub_lo : A_lo ⊆ Finset.Icc 1 xb.1 := fun x hx =>
          Finset.mem_Icc.mpr ⟨(hA'_le_n' x (hcore_sub (hlo_sub hx))).1, Nat.le_of_lt (hlh_lt x hx xb.1 hbhi)⟩
        have hle := Finset.card_le_card hsub_lo
        simp only [Nat.card_Icc, add_tsub_cancel_right] at hle
        have : 8 ≤ m / 16 := by omega
        omega
      calc (B2 i).sum id ≤ ∑ b ∈ B2 i, (8 * (b / 4)) := Finset.sum_le_sum h1
        _ = 8 * ∑ b ∈ B2 i, (b / 4) := (Finset.mul_sum _ _ _).symm
        _ ≤ 8 * (S i).card := Nat.mul_le_mul_left 8 hS_ge_sum
    -- Now prove M ≤ 32 * ℓ * (B2 i).sum id via dyadic decomposition of X + E5
    have hM_le_B2 : M ≤ 32 * ℓ * (B2 i).sum id := by
      set Xj1 := X.filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1))
      set Jgt := (Finset.range L).filter (fun j => j1 < j)
      have hpart_disj : Set.PairwiseDisjoint ((Finset.range L) : Set ℕ)
          (fun j => X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
        intro j1' _ j2' _ hne
        show Disjoint _ _
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        have h1 := (Finset.mem_filter.mp ha1).2
        have h2 := (Finset.mem_filter.mp ha2).2
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1' + 1 ≤ j2'); omega
        · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j2' + 1 ≤ j1'); omega
      -- Helper: for any j < L with |X ∩ I_j| ≥ 16 * ℓ * L, X_j.sum id ≤ 16 * ℓ * (B2 i ∩ I_j).sum id
      have hdyad_good : ∀ j < L, 16 * ℓ * L ≤ (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).card →
          (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id ≤
            16 * ℓ * ((B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id := by
        intro j hjL hge
        set Xj := X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
        set B2j := (B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))
        have hB2j_eq : B2j = img Xj (C_t i) := by
          ext a
          simp only [B2j, B2, Xj, img, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
            true_and, Subtype.exists]
          constructor
          · rintro ⟨⟨x, hxC, ⟨hxX, hfx⟩, rfl⟩, ha1, ha2⟩
            exact ⟨x, hxC, ⟨⟨hxX, ha1, ha2⟩, hfx⟩, rfl⟩
          · rintro ⟨x, hxC, ⟨⟨hxX, ha1, ha2⟩, hfx⟩, rfl⟩
            exact ⟨⟨x, hxC, ⟨hxX, hfx⟩, rfl⟩, ha1, ha2⟩
        have hE5j : Xj.card < 8 * ℓ * (img Xj (C_t i)).card := hE5 j hjL hge
        rw [← hB2j_eq] at hE5j
        have hX_ub : Xj.sum id ≤ Xj.card * (2 * 2 ^ j) := by
          calc Xj.sum id ≤ ∑ _a ∈ Xj, (2 * 2 ^ j) :=
                Finset.sum_le_sum fun a ha => by
                  have h := (Finset.mem_filter.mp ha).2.2
                  rw [pow_succ'] at h; exact Nat.le_of_lt h
            _ = Xj.card * (2 * 2 ^ j) := by rw [Finset.sum_const, smul_eq_mul]
        have hB2_lb : B2j.card * 2 ^ j ≤ B2j.sum id := by
          calc B2j.card * 2 ^ j = ∑ _a ∈ B2j, 2 ^ j := by rw [Finset.sum_const, smul_eq_mul]
            _ ≤ ∑ a ∈ B2j, a := Finset.sum_le_sum fun a ha => (Finset.mem_filter.mp ha).2.1
        calc Xj.sum id ≤ Xj.card * (2 * 2 ^ j) := hX_ub
          _ ≤ (8 * ℓ * B2j.card) * (2 * 2 ^ j) := Nat.mul_le_mul_right _ (Nat.le_of_lt hE5j)
          _ = 16 * ℓ * (B2j.card * 2 ^ j) := by ring
          _ ≤ 16 * ℓ * B2j.sum id := Nat.mul_le_mul_left _ hB2_lb
      -- Every j ∈ Jgt with nonempty X_j has |X_j| ≥ 64 * ℓ * L ≥ 16 * ℓ * L
      have hJgt_sum : (X \ Xj1).sum id ≤ 16 * ℓ * ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id := by
        have hXdiff_eq : X \ Xj1 = Jgt.biUnion (fun j => X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
          ext a
          simp only [Finset.mem_sdiff, Xj1, Finset.mem_filter, Finset.mem_biUnion, Jgt, Finset.mem_range]
          constructor
          · rintro ⟨haX, hnot⟩
            have haA' : a ∈ A' := hcore_sub (hX_sub_core haX)
            have ha1 := hX_ge_j1 a haX
            have hage : 2 ^ (j1 + 1) ≤ a := by
              by_contra hlt; push Not at hlt; exact hnot ⟨haX, ha1, hlt⟩
            set ja := Nat.log 2 a
            have hja_lt : ja < L := by
              have h1 := hA'_lt_2L a haA'
              have h2 : 2 ^ ja ≤ a := Nat.pow_log_le_self 2 (by have := (hA'_le_n' a haA').1; omega)
              exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (lt_of_le_of_lt h2 h1)
            have hja_gt : j1 < ja := by
              by_contra hle; push Not at hle
              have h1 : a < 2 ^ (ja + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) a
              have h2 := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : ja + 1 ≤ j1 + 1)
              omega
            exact ⟨ja, ⟨hja_lt, hja_gt⟩, haX, Nat.pow_log_le_self 2 (by have := (hA'_le_n' a haA').1; omega),
              Nat.lt_pow_succ_log_self (by decide : 1 < 2) a⟩
          · rintro ⟨j, ⟨_, hjgt⟩, haX, ha1, _⟩
            refine ⟨haX, fun h => ?_⟩
            have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1 + 1 ≤ j)
            omega
        have hB2_disj : Set.PairwiseDisjoint (Jgt : Set ℕ)
            (fun j => (B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) := by
          intro j1' _ j2' _ hne
          show Disjoint _ _
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          have h1 := (Finset.mem_filter.mp ha1).2
          have h2 := (Finset.mem_filter.mp ha2).2
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1' + 1 ≤ j2'); omega
          · have := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j2' + 1 ≤ j1'); omega
        have hB2_sub : Jgt.biUnion (fun j => (B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))) ⊆
            (B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a) := by
          intro a ha
          obtain ⟨j, hj, haB⟩ := Finset.mem_biUnion.mp ha
          have hjgt := (Finset.mem_filter.mp hj).2
          obtain ⟨haB2, ha1, _⟩ := Finset.mem_filter.mp haB
          have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : j1 + 1 ≤ j)
          exact Finset.mem_filter.mpr ⟨haB2, hpow.trans ha1⟩
        rw [hXdiff_eq, Finset.sum_biUnion (hpart_disj.subset (Finset.filter_subset _ _))]
        calc ∑ j ∈ Jgt, (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id
            ≤ ∑ j ∈ Jgt, (16 * ℓ * ((B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id) := by
              apply Finset.sum_le_sum
              intro j hj
              obtain ⟨hjR, hjgt⟩ := Finset.mem_filter.mp hj
              have hjL := Finset.mem_range.mp hjR
              by_cases hne : (X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).Nonempty
              · have hneA' : (A'.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).Nonempty := by
                  obtain ⟨a, ha⟩ := hne
                  obtain ⟨haX, ha1, ha2⟩ := Finset.mem_filter.mp ha
                  exact ⟨a, Finset.mem_filter.mpr ⟨hcore_sub (hX_sub_core haX), ha1, ha2⟩⟩
                have hge64 := hcore_dyad j hjL hneA'
                rw [hX_eq_core_gt j hjgt] at hge64
                have h16 : 16 * ℓ * L ≤ 64 * ℓ * L := by
                  calc 16 * ℓ * L = 16 * (ℓ * L) := by ring
                    _ ≤ 64 * (ℓ * L) := Nat.mul_le_mul_right _ (by decide)
                    _ = 64 * ℓ * L := by ring
                exact hdyad_good j hjL (h16.trans hge64)
              · have hemp : X.filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)) = ∅ :=
                  Finset.not_nonempty_iff_eq_empty.mp hne
                simp [hemp]
          _ = 16 * ℓ * ∑ j ∈ Jgt, ((B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1))).sum id :=
              (Finset.mul_sum _ _ _).symm
          _ = 16 * ℓ * (Jgt.biUnion (fun j => (B2 i).filter (fun a => 2 ^ j ≤ a ∧ a < 2 ^ (j + 1)))).sum id := by
              rw [Finset.sum_biUnion hB2_disj]
          _ ≤ 16 * ℓ * ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id :=
              Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset hB2_sub)
      have hM_split : M = Xj1.sum id + (X \ Xj1).sum id := by
        rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset (Finset.filter_subset _ _)]
      by_cases hbig1 : 16 * ℓ * L ≤ Xj1.card
      · have h1 := hdyad_good j1 hj1_lt_L hbig1
        have hB2_disj1 : Disjoint ((B2 i).filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1)))
            ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)) := by
          rw [Finset.disjoint_left]
          intro a ha1 ha2
          have hlt := (Finset.mem_filter.mp ha1).2.2
          have hge := (Finset.mem_filter.mp ha2).2
          omega
        have hB2_sub1 : ((B2 i).filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1))) ∪
            ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)) ⊆ B2 i :=
          Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hsum_le : ((B2 i).filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1))).sum id +
            ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id ≤ (B2 i).sum id := by
          rw [← Finset.sum_union hB2_disj1]
          exact Finset.sum_le_sum_of_subset hB2_sub1
        calc M = Xj1.sum id + (X \ Xj1).sum id := hM_split
          _ ≤ 16 * ℓ * ((B2 i).filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1))).sum id +
                16 * ℓ * ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id := Nat.add_le_add h1 hJgt_sum
          _ = 16 * ℓ * (((B2 i).filter (fun a => 2 ^ j1 ≤ a ∧ a < 2 ^ (j1 + 1))).sum id +
                ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id) := by ring
          _ ≤ 16 * ℓ * (B2 i).sum id := Nat.mul_le_mul_left _ hsum_le
          _ ≤ 32 * ℓ * (B2 i).sum id := by
              have : 16 * ℓ ≤ 32 * ℓ := by omega
              exact Nat.mul_le_mul_right _ this
      · -- Small Xj1: |X \ Xj1| ≥ |Xj1| and every element of X \ Xj1 ≥ 2^(j1+1) > every element of Xj1
        have hcard_diff : Xj1.card ≤ (X \ Xj1).card := by
          have h1 : (X \ Xj1).card + Xj1.card = X.card :=
            Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ X)
          have h2 : 32 * ℓ * L ≤ X.card := by
            rw [hX_card]
            calc 32 * ℓ * L = 8 * ℓ * (4 * L) := by ring
              _ ≤ 8 * ℓ * k' := Nat.mul_le_mul_left _ hk'_ge
          have h32 : 32 * ℓ * L = 2 * (16 * ℓ * L) := by ring
          omega
        have hXj1_le_diff : Xj1.sum id ≤ (X \ Xj1).sum id := by
          have h1 : Xj1.sum id ≤ Xj1.card * 2 ^ (j1 + 1) := by
            calc Xj1.sum id ≤ ∑ _a ∈ Xj1, 2 ^ (j1 + 1) :=
                  Finset.sum_le_sum fun a ha => Nat.le_of_lt (Finset.mem_filter.mp ha).2.2
              _ = Xj1.card * 2 ^ (j1 + 1) := by rw [Finset.sum_const, smul_eq_mul]
          have h2 : (X \ Xj1).card * 2 ^ (j1 + 1) ≤ (X \ Xj1).sum id := by
            calc (X \ Xj1).card * 2 ^ (j1 + 1) = ∑ _a ∈ X \ Xj1, 2 ^ (j1 + 1) := by
                  rw [Finset.sum_const, smul_eq_mul]
              _ ≤ ∑ a ∈ X \ Xj1, a := Finset.sum_le_sum fun a ha => by
                  obtain ⟨haX, hnot⟩ := Finset.mem_sdiff.mp ha
                  have ha1 := hX_ge_j1 a haX
                  by_contra hlt; push Not at hlt
                  exact hnot (Finset.mem_filter.mpr ⟨haX, ha1, hlt⟩)
          exact h1.trans ((Nat.mul_le_mul_right _ hcard_diff).trans h2)
        have hB2_le : ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id ≤ (B2 i).sum id :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        calc M = Xj1.sum id + (X \ Xj1).sum id := hM_split
          _ ≤ 2 * (X \ Xj1).sum id := by omega
          _ ≤ 2 * (16 * ℓ * ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id) :=
              Nat.mul_le_mul_left 2 hJgt_sum
          _ = 32 * ℓ * ((B2 i).filter (fun a => 2 ^ (j1 + 1) ≤ a)).sum id := by ring
          _ ≤ 32 * ℓ * (B2 i).sum id := Nat.mul_le_mul_left _ hB2_le
    -- Combine: ℓ * Q ≤ 10 * M ≤ 320 * ℓ * (B2 i).sum id ≤ 2560 * ℓ * (S i).card ≤ 4096 * ℓ * (S i).card
    have h1 : ℓ * Q ≤ 10 * M := Nat.mul_div_le (10 * M) ℓ
    have h2 : 10 * M ≤ 320 * ℓ * (B2 i).sum id := by
      calc 10 * M ≤ 10 * (32 * ℓ * (B2 i).sum id) := Nat.mul_le_mul_left 10 hM_le_B2
        _ = 320 * ℓ * (B2 i).sum id := by ring
    have h3 : 320 * ℓ * (B2 i).sum id ≤ 2560 * ℓ * (S i).card := by
      calc 320 * ℓ * (B2 i).sum id ≤ 320 * ℓ * (8 * (S i).card) := Nat.mul_le_mul_left _ hB2_sum_le
        _ = 2560 * ℓ * (S i).card := by ring
    have h4 : ℓ * Q ≤ ℓ * (α_inv * (S i).card) := by
      calc ℓ * Q ≤ 2560 * ℓ * (S i).card := h1.trans (h2.trans h3)
        _ = ℓ * (2560 * (S i).card) := by ring
        _ ≤ ℓ * (α_inv * (S i).card) := Nat.mul_le_mul_left ℓ (Nat.mul_le_mul_right _ (by omega))
    exact Nat.le_of_mul_le_mul_left h4 hℓ
  -- Verify coprimality condition for weak_lev_interval: ∀ i, ∀ d ≥ 2, ∃ x ∈ S i, ¬ d ∣ x
  have hS_cop : ∀ i : Fin ℓ, ∀ d ≥ 2, ∃ x ∈ S i, ¬ d ∣ x := by
    intro i d hd2
    -- Every element of P i is a singleton in S i (since 1 ≤ 13 * k' + 1)
    have hP_sub_S : P i ⊆ S i := by
      intro x hx
      refine Finset.mem_image.mpr ⟨{x}, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (Finset.singleton_subset_iff.mpr hx), by simp⟩, by simp⟩
    by_cases hd_le : d ≤ 1024 * ℓ * n / m
    · have hE3d := (hf i).2.2.2.1 d hd2 hd_le
      have hcore_d := hcore_div d hd2 hd_le
      have hpos : 0 < (img (A_core.filter (fun a => ¬ d ∣ a)) (C_f i)).card := by
        by_contra h0
        have heq0 : (img (A_core.filter (fun a => ¬ d ∣ a)) (C_f i)).card = 0 := by omega
        rw [heq0, mul_zero] at hE3d
        omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hyF, hfy⟩ := (Finset.mem_filter.mp hy).2
      have hnd := (Finset.mem_filter.mp hyF).2
      simp only [C_f, Finset.mem_singleton] at hfy
      have hyP : y.1 ∈ P i := Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨Finset.mem_univ y, y.2, by simp [C_all, hfy]⟩, rfl⟩
      exact ⟨y.1, hP_sub_S hyP, hnd⟩
    · -- d > 1024 * ℓ * n / m: P i has > m / (80 * ℓ) elements in [1, n], so cannot all be multiples of d
      by_contra hall
      push Not at hall
      have hAinj_sub_P : img A_lo (C_all i) ⊆ P i := by
        intro a ha
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr
          ⟨Finset.mem_univ x, x.2, (Finset.mem_filter.mp hx).2.2⟩, rfl⟩
      have hmul_sub : img A_lo (C_all i) ⊆ (Finset.Icc 1 (n / d)).image (fun q => d * q) := by
        intro a ha
        have haP : a ∈ P i := hAinj_sub_P ha
        have haA' : a ∈ A' := hcore_sub (hP_sub i haP)
        have hda : d ∣ a := hall a (hP_sub_S haP)
        have ha1 := (hA'_le_n' a haA').1
        have han : a ≤ n := (hA'_le_n' a haA').2.trans (Nat.div_le_self n d_tot)
        refine Finset.mem_image.mpr ⟨a / d, Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right han⟩,
          Nat.mul_div_cancel' hda⟩
        by_contra h0
        have hz : a / d = 0 := Nat.eq_zero_of_not_pos h0
        have heq := Nat.mul_div_cancel' hda
        rw [hz, mul_zero] at heq; omega
      have hcard_le : (img A_lo (C_all i)).card ≤ n / d := by
        calc (img A_lo (C_all i)).card
            ≤ ((Finset.Icc 1 (n / d)).image (fun q => d * q)).card := Finset.card_le_card hmul_sub
          _ ≤ (Finset.Icc 1 (n / d)).card := Finset.card_image_le
          _ = n / d := by simp
      have hcard_gt : m / (80 * ℓ) < (img A_lo (C_all i)).card := by
        have hE1 := (hf i).1
        have h1 : 4 * ℓ * m_lo ≤ A_lo.card := Nat.mul_div_le A_lo.card (4 * ℓ)
        have h2 : m_lo < (img A_lo (C_all i)).card := Nat.lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 hE1)
        exact lt_of_le_of_lt hm_lo_ge h2
      have hdn : d * (m / (80 * ℓ) + 1) ≤ n := by
        have h1 : m / (80 * ℓ) + 1 ≤ n / d := by omega
        calc d * (m / (80 * ℓ) + 1) ≤ d * (n / d) := Nat.mul_le_mul_left d h1
          _ ≤ n := Nat.mul_div_le n d
      have h80 : m ≤ 80 * ℓ * (m / (80 * ℓ) + 1) := by
        have := Nat.lt_mul_div_succ m (by omega : 0 < 80 * ℓ)
        omega
      have hdm_le : d * m ≤ 80 * ℓ * n := by
        calc d * m ≤ d * (80 * ℓ * (m / (80 * ℓ) + 1)) := Nat.mul_le_mul_left d h80
          _ = 80 * ℓ * (d * (m / (80 * ℓ) + 1)) := by ring
          _ ≤ 80 * ℓ * n := Nat.mul_le_mul_left _ hdn
      have hd_le_80 : d ≤ 1024 * ℓ * n / m := by
        have : d * m ≤ 1024 * ℓ * n := hdm_le.trans (by
          have : 80 ≤ 1024 := by decide
          calc 80 * ℓ * n = 80 * (ℓ * n) := by ring
            _ ≤ 1024 * (ℓ * n) := Nat.mul_le_mul_right _ this
            _ = 1024 * ℓ * n := by ring)
        exact (Nat.le_div_iff_mul_le hm_pos).mpr this
      exact hd_le hd_le_80
  -- Verify Q ≥ 4 * α_inv and Q ≥ every x ∈ A_ext
  have hQ_ge_all : ∀ x ∈ A', x ≤ Q := by
    intro x hx
    have h1 := hM_ge_all x hx
    have h2 : x * ℓ ≤ 10 * M := by
      calc x * ℓ ≤ 16 * ℓ * x := by
            have : 1 ≤ 16 := by decide
            calc x * ℓ = 1 * (ℓ * x) := by ring
              _ ≤ 16 * (ℓ * x) := Nat.mul_le_mul_right _ this
              _ = 16 * ℓ * x := by ring
        _ ≤ M := h1
        _ ≤ 10 * M := by omega
    exact (Nat.le_div_iff_mul_le hℓ).mpr h2
  have hQ_ge_4α : 4 * α_inv ≤ Q := by
    -- A' has size ≥ m / 2 ≥ 32768 * ℓ ≥ 16384 = 4 * α_inv, so max(A') ≥ 4 * α_inv!
    have hA'_ne : A'.Nonempty := Finset.card_pos.mp (by omega)
    set amax := A'.max' hA'_ne
    have hsub : A' ⊆ Finset.Icc 1 amax := fun x hx =>
      Finset.mem_Icc.mpr ⟨(hA'_le_n' x hx).1, Finset.le_max' A' x hx⟩
    have hcard_le : A'.card ≤ amax := by simpa using Finset.card_le_card hsub
    have h4α_le : 4 * α_inv ≤ A'.card := by
      have h4α_le_ℓ : 4 * α_inv ≤ ℓ := by
        have h16 : 1 ≤ 16 * α_inv := by omega
        calc 4 * α_inv ≤ (16 * α_inv) * (4 * α_inv) := Nat.le_mul_of_pos_left _ h16
          _ ≤ 2 * ((16 * α_inv) * (4 * α_inv)) := by omega
      have h1 : 2 * (4 * α_inv) ≤ 65536 * ℓ * L := by
        have h2 : ℓ ≤ ℓ * L := Nat.le_mul_of_pos_right ℓ (by omega)
        calc 2 * (4 * α_inv) ≤ 2 * ℓ := Nat.mul_le_mul_left 2 h4α_le_ℓ
          _ ≤ 2 * (ℓ * L) := Nat.mul_le_mul_left 2 h2
          _ ≤ 65536 * (ℓ * L) := Nat.mul_le_mul_right _ (by decide)
          _ = 65536 * ℓ * L := by ring
      omega
    exact (h4α_le.trans hcard_le).trans (hQ_ge_all amax (Finset.max'_mem A' hA'_ne))
  have hS_0 : ∀ i : Fin ℓ, 0 ∈ S i := fun i =>
    Finset.mem_image.mpr ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), Nat.zero_le _⟩, by simp⟩
  -- Apply Weak Lev to S : Fin ℓ → Finset ℕ
  obtain ⟨a, ha_pos, ha_le, hIcc_core⟩ := h_weak_lev hα hQ_ge_4α S hS_sub_Q hS_0 hS_dense hS_cop
  -- Lift finsetListSum (List.ofFn S) ⊆ A_core.powerset.image (·.sum id)
  have hlist_sub_core : finsetListSum (List.ofFn S) ⊆ A_core.powerset.image (fun T => T.sum id) := by
    have h1 := finsetListSum_ofFn_subset_powerset P S hP_disj (fun i x hx => by
      obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨T, (Finset.mem_filter.mp hT).1, rfl⟩)
    have hbiU_sub : Finset.univ.biUnion P ⊆ A_core := Finset.biUnion_subset.mpr fun i _ => hP_sub i
    exact h1.trans (Finset.image_subset_image (Finset.powerset_mono.mpr hbiU_sub))
  -- Extend interval Icc a (a + Q) by A_ext!
  have hIcc_A' : Finset.Icc a (a + Q + A_ext.sum id) ⊆ A'.powerset.image (fun T => T.sum id) := by
    rw [← hunion_ce]
    exact extend_interval_subsetSum A_core A_ext hdisj_ce a Q
      (hIcc_core.trans hlist_sub_core) (fun x hx => hQ_ge_all x (hext_sub hx))
  -- Bound len := Q + A_ext.sum id ≥ m^2 / 256
  have hlen_ge : m * m / 256 ≤ Q + A_ext.sum id := by
    have hsum_ext := sum_distinct_pos_ge A_ext (fun x hx => (hA'_le_n' x (hext_sub hx)).1)
    have h1 : m * m ≤ 256 * A_ext.sum id := by
      have hm8 : m ≤ 9 * (m / 8) := by omega
      have hsq : m * m ≤ 81 * (A_ext.card * (A_ext.card + 1)) := by
        calc m * m ≤ (9 * (m / 8)) * (9 * (m / 8)) := Nat.mul_le_mul hm8 hm8
          _ = 81 * ((m / 8) * (m / 8)) := by ring
          _ ≤ 81 * (A_ext.card * (A_ext.card + 1)) :=
              Nat.mul_le_mul_left 81 (Nat.mul_le_mul hext_card (by omega))
      calc m * m ≤ 81 * (2 * A_ext.sum id) := hsq.trans (Nat.mul_le_mul_left 81 hsum_ext)
        _ = 162 * A_ext.sum id := by ring
        _ ≤ 256 * A_ext.sum id := Nat.mul_le_mul_right _ (by decide)
    have h2 : m * m / 256 ≤ A_ext.sum id :=
      (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 256)).mpr (by rw [mul_comm]; omega)
    omega
  -- Bound d_tot * a ≤ (m / 4) * n
  have hda_le : d_tot * a ≤ (m / 4) * n := by
    have ha_5M : a ≤ 5 * M := by
      have h1 : r * Q = r * (10 * M / (2 * r)) := rfl
      have h2 : 2 * r * (10 * M / (2 * r)) ≤ 10 * M := Nat.mul_div_le (10 * M) (2 * r)
      have h3 : 2 * (r * Q) ≤ 10 * M := by linarith
      have ha_le' : a ≤ r * Q := ha_le
      omega
    have hM_ub : d_tot * M ≤ 8 * ℓ * k' * n := by
      have h1 : M ≤ X.card * n' := by
        calc M = ∑ x ∈ X, x := rfl
          _ ≤ ∑ _x ∈ X, n' := Finset.sum_le_sum fun x hx => (hA'_le_n' x (hcore_sub (hX_sub_core hx))).2
          _ = X.card * n' := by rw [Finset.sum_const, smul_eq_mul]
      calc d_tot * M ≤ d_tot * (X.card * n') := Nat.mul_le_mul_left d_tot h1
        _ = X.card * (d_tot * n') := by ring
        _ ≤ X.card * n := Nat.mul_le_mul_left _ (Nat.mul_div_le n d_tot)
        _ = 8 * ℓ * k' * n := by rw [hX_card]
    have h40_le : 40 * ℓ * k' ≤ m / 4 := by
      have h4 : 4 * (40 * ℓ * k') = 160 * ℓ * k' := by ring
      omega
    calc d_tot * a ≤ d_tot * (5 * M) := Nat.mul_le_mul_left d_tot ha_5M
      _ = 5 * (d_tot * M) := by ring
      _ ≤ 5 * (8 * ℓ * k' * n) := Nat.mul_le_mul_left 5 hM_ub
      _ = (40 * ℓ * k') * n := by ring
      _ ≤ (m / 4) * n := Nat.mul_le_mul_right n h40_le
  -- Map subset sums of A' back to A via x ↦ d_tot * x
  refine ⟨d_tot, a, Q + A_ext.sum id, hd_pos, hd_le_3, ha_pos, hlen_ge, hda_le, ?_⟩
  intro x hx
  have hxA' := hIcc_A' (by simpa [add_assoc] using hx)
  obtain ⟨T, hTA', hTsum⟩ := Finset.mem_image.mp hxA'
  have hTA'' : T ⊆ A' := Finset.mem_powerset.mp hTA'
  refine Finset.mem_image.mpr ⟨T.image (fun y => d_tot * y), Finset.mem_powerset.mpr ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    exact (hA'_prop y (hTA'' hy)).2
  · have hinj : Set.InjOn (fun y => d_tot * y) (T : Set ℕ) := fun y1 _ y2 _ heq =>
      Nat.eq_of_mul_eq_mul_left hd_pos heq
    rw [Finset.sum_image (fun y1 hy1 y2 hy2 heq => hinj hy1 hy2 heq)]
    simp only [id_eq] at hTsum ⊢
    rw [← Finset.mul_sum, hTsum]

end Theorem61

-- Pigeonhole: any d elements of ℕ contain a nonempty subset of size ≤ d with sum divisible by d
lemma pigeonhole_dvd_subset {d : ℕ} (hd : 0 < d) {R : Finset ℕ} (hcard : d ≤ R.card) :
    ∃ T ⊆ R, T.Nonempty ∧ T.card ≤ d ∧ d ∣ T.sum id := by
  have : NeZero d := ⟨Nat.ne_of_gt hd⟩
  set L : List ℕ := R.toList.take d
  have hLlen : L.length = d := by
    simp [L, hcard]
  have hLnd : L.Nodup := (Finset.nodup_toList R).take
  have hLmem : ∀ x ∈ L, x ∈ R := fun x hx =>
    Finset.mem_toList.mp (List.mem_of_mem_take hx)
  let p : Fin (d + 1) → ZMod d := fun j => ((L.take j.1).sum : ZMod d)
  have hlt : Fintype.card (ZMod d) < Fintype.card (Fin (d + 1)) := by
    rw [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨j1, j2, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt p hlt
  -- Ensure i < j
  obtain ⟨i, j, hij, hij_eq⟩ : ∃ i j : Fin (d + 1), i.1 < j.1 ∧ p i = p j := by
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact ⟨j1, j2, h, heq⟩
    · exact ⟨j2, j1, h, heq.symm⟩
  set subL : List ℕ := (L.drop i.1).take (j.1 - i.1)
  have htake_split : L.take j.1 = L.take i.1 ++ subL := by
    have h1 : j.1 = i.1 + (j.1 - i.1) := by omega
    conv_lhs => rw [h1]
    rw [List.take_add]
  have hsubL_nd : subL.Nodup := hLnd.drop.take
  have hsubL_len : subL.length = j.1 - i.1 := by
    simp only [subL, List.length_take, List.length_drop, hLlen]
    omega
  set T : Finset ℕ := subL.toFinset
  have hT_sub : T ⊆ R := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact hLmem x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hT_card : T.card = j.1 - i.1 := by
    rw [List.toFinset_card_of_nodup hsubL_nd, hsubL_len]
  have hT_ne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hT_le : T.card ≤ d := by omega
  have hT_sum : T.sum id = subL.sum := by
    simpa [T] using List.sum_toFinset id hsubL_nd
  have hsum_add : (L.take i.1).sum + T.sum id = (L.take j.1).sum := by
    rw [hT_sum, htake_split, List.sum_append]
  have hdvd : d ∣ T.sum id := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hcast : (((L.take i.1).sum + T.sum id : ℕ) : ZMod d) = ((L.take j.1).sum : ZMod d) :=
      congrArg (Nat.cast : ℕ → ZMod d) hsum_add
    rw [Nat.cast_add] at hcast
    have hp : ((L.take i.1).sum : ZMod d) = ((L.take j.1).sum : ZMod d) := hij_eq
    linear_combination hcast - hp
  exact ⟨T, hT_sub, hT_ne, hT_le, hdvd⟩

-- Greedily partition R into disjoint nonempty subsets of size ≤ d with sums divisible by d
lemma greedy_dvd_partition {d : ℕ} (hd : 0 < d) (R : Finset ℕ) :
    ∃ L : List (Finset ℕ),
      (∀ T ∈ L, T ⊆ R ∧ T.Nonempty ∧ T.card ≤ d ∧ d ∣ T.sum id) ∧
      L.Pairwise Disjoint ∧
      R.card < (L.map Finset.card).sum + d := by
  induction hn : R.card using Nat.strongRecOn generalizing R with
  | ind n ih =>
    by_cases hlt : R.card < d
    · exact ⟨[], by simp, List.Pairwise.nil, by omega⟩
    · have hge : d ≤ R.card := by omega
      obtain ⟨T, hTR, hTne, hTle, hTdvd⟩ := pigeonhole_dvd_subset hd hge
      have hcard_lt : (R \ T).card < n := by
        have hsd := Finset.card_sdiff_add_card_eq_card hTR
        have hpos := hTne.card_pos
        omega
      obtain ⟨L, hLprop, hLdisj, hLrem⟩ := ih (R \ T).card hcard_lt (R \ T) rfl
      refine ⟨T :: L, ?_, ?_, ?_⟩
      · intro U hU
        rcases List.mem_cons.mp hU with rfl | hUL
        · exact ⟨hTR, hTne, hTle, hTdvd⟩
        · obtain ⟨h1, h2, h3, h4⟩ := hLprop U hUL
          exact ⟨h1.trans Finset.sdiff_subset, h2, h3, h4⟩
      · refine List.pairwise_cons.mpr ⟨?_, hLdisj⟩
        intro U hUL
        exact Finset.disjoint_sdiff.mono_right (hLprop U hUL).1
      · simp only [List.map_cons, List.sum_cons]
        have hsd := Finset.card_sdiff_add_card_eq_card hTR
        omega

-- From a greedy partition of R ⊆ [M, N], hit any homogeneous AP d * [a, a + len]
lemma exists_subset_sum_in_homAP {d a len M N : ℕ} (hd : 0 < d) (ha : 0 < a)
    (hlen : N ≤ len) (R : Finset ℕ)
    (hR : ∀ x ∈ R, M ≤ x ∧ x ≤ N)
    (hreach : d * (a + len) ≤ (R.card - d) * M) :
    ∃ U ⊆ R, U.Nonempty ∧ ∃ x ∈ Finset.Icc a (a + len), U.sum id = d * x := by
  obtain ⟨L, hLprop, hLdisj, hLrem⟩ := greedy_dvd_partition hd R
  let prefUnion : ℕ → Finset ℕ := fun k => (L.take k).foldr (· ∪ ·) ∅
  have hpref_sub : ∀ k, prefUnion k ⊆ R := by
    intro k
    induction k with
    | zero => simp [prefUnion]
    | succ k ih =>
      simp only [prefUnion]
      by_cases hk : k < L.length
      · rw [List.take_succ_eq_append_getElem hk, List.foldr_append]
        have haux : ∀ (A : List (Finset ℕ)) (init : Finset ℕ),
            (∀ X ∈ A, X ⊆ R) → init ⊆ R → A.foldr (· ∪ ·) init ⊆ R := by
          intro A init hA hinit
          induction A with
          | nil => exact hinit
          | cons X A ihA =>
            exact Finset.union_subset (hA X (by simp)) (ihA (fun Y hY => hA Y (by simp [hY])))
        refine haux (L.take k) (L[k] ∪ ∅)
          (fun X hX => (hLprop X (List.mem_of_mem_take hX)).1)
          (Finset.union_subset (hLprop L[k] (List.getElem_mem hk)).1 (Finset.empty_subset _))
      · rw [List.take_of_length_le (by omega)]
        have haux : ∀ (A : List (Finset ℕ)), (∀ X ∈ A, X ⊆ R) → A.foldr (· ∪ ·) ∅ ⊆ R := by
          intro A hA
          induction A with
          | nil => exact Finset.empty_subset _
          | cons X A ihA =>
            exact Finset.union_subset (hA X (by simp)) (ihA (fun Y hY => hA Y (by simp [hY])))
        exact haux L (fun X hX => (hLprop X hX).1)
  have hfold_sum_card : ∀ (A : List (Finset ℕ)), A.Pairwise Disjoint →
      (A.foldr (· ∪ ·) ∅).sum id = (A.map (fun T => T.sum id)).sum ∧
      (A.foldr (· ∪ ·) ∅).card = (A.map Finset.card).sum := by
    intro A hA
    induction A with
    | nil => simp
    | cons X A ih =>
      rw [List.pairwise_cons] at hA
      obtain ⟨hsum, hcard⟩ := ih hA.2
      have hdisj : Disjoint X (A.foldr (· ∪ ·) ∅) := by
        rw [Finset.disjoint_left]
        intro x hxX hxA
        have hmem : ∀ (B : List (Finset ℕ)), x ∈ B.foldr (· ∪ ·) ∅ → ∃ Y ∈ B, x ∈ Y := by
          intro B
          induction B with
          | nil => intro h; simp at h
          | cons Y B ihB =>
            intro h
            rcases Finset.mem_union.mp h with h1 | h2
            · exact ⟨Y, by simp, h1⟩
            · obtain ⟨Z, hZ, hxZ⟩ := ihB h2
              exact ⟨Z, by simp [hZ], hxZ⟩
        obtain ⟨Y, hYA, hxY⟩ := hmem A hxA
        exact Finset.disjoint_left.mp (hA.1 Y hYA) hxX hxY
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact ⟨by rw [Finset.sum_union hdisj, hsum], by rw [Finset.card_union_of_disjoint hdisj, hcard]⟩
  let W : ℕ → ℕ := fun k => (prefUnion k).sum id
  have hW_eq : ∀ k, W k = ((L.take k).map (fun T => T.sum id)).sum := fun k =>
    (hfold_sum_card (L.take k) hLdisj.take).1
  have hW_dvd : ∀ k, d ∣ W k := by
    intro k
    rw [hW_eq k]
    have haux : ∀ (A : List (Finset ℕ)), (∀ T ∈ A, d ∣ T.sum id) → d ∣ (A.map (fun T => T.sum id)).sum := by
      intro A hA
      induction A with
      | nil => simp
      | cons T A ih =>
        simp only [List.map_cons, List.sum_cons]
        exact dvd_add (hA T (by simp)) (ih (fun U hU => hA U (by simp [hU])))
    exact haux (L.take k) (fun T hT => (hLprop T (List.mem_of_mem_take hT)).2.2.2)
  have hW_top : d * (a + len) ≤ W L.length := by
    have h1 : (R.card - d) * M ≤ (prefUnion L.length).card * M := by
      apply Nat.mul_le_mul_right
      have hc := (hfold_sum_card L hLdisj).2
      have htake : L.take L.length = L := List.take_length
      simp only [prefUnion, htake, hc]
      omega
    have h2 : (prefUnion L.length).card * M ≤ W L.length := by
      dsimp [W]
      calc (prefUnion L.length).card * M
          = ∑ _x ∈ prefUnion L.length, M := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ x ∈ prefUnion L.length, id x :=
            Finset.sum_le_sum fun x hx => (hR x (hpref_sub L.length hx)).1
    exact hreach.trans (h1.trans h2)
  have hex : ∃ k, d * a ≤ W k := ⟨L.length, (Nat.mul_le_mul_left d (by omega)).trans hW_top⟩
  let k0 := Nat.find hex
  have hk0_ge : d * a ≤ W k0 := Nat.find_spec hex
  have hk0_pos : 0 < k0 := by
    by_contra h0
    have hk00 : k0 = 0 := by omega
    have hW0 : W 0 = 0 := by simp [W, prefUnion]
    rw [hk00, hW0] at hk0_ge
    nlinarith
  have hk0_le_len : k0 ≤ L.length := Nat.find_min' hex ((Nat.mul_le_mul_left d (by omega)).trans hW_top)
  have hk0_prev : W (k0 - 1) < d * a := lt_of_not_ge (Nat.find_min hex (by omega : k0 - 1 < k0))
  have hstep : W k0 ≤ W (k0 - 1) + d * N := by
    have hlt : k0 - 1 < L.length := by omega
    have htake : L.take k0 = L.take (k0 - 1) ++ [L[k0 - 1]] := by
      have : k0 = (k0 - 1) + 1 := by omega
      conv_lhs => rw [this]
      exact List.take_succ_eq_append_getElem hlt
    rw [hW_eq k0, hW_eq (k0 - 1), htake, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
    have hTprop := hLprop L[k0 - 1] (List.getElem_mem hlt)
    have hTsum_le : L[k0 - 1].sum id ≤ d * N := by
      calc L[k0 - 1].sum id
          ≤ ∑ _x ∈ L[k0 - 1], N := Finset.sum_le_sum fun x hx => (hR x (hTprop.1 hx)).2
        _ = L[k0 - 1].card * N := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ d * N := Nat.mul_le_mul_right N hTprop.2.2.1
    omega
  have hW_le : W k0 ≤ d * (a + len) := by
    have : d * N ≤ d * len := Nat.mul_le_mul_left d hlen
    nlinarith
  obtain ⟨x, hx⟩ := hW_dvd k0
  have hx_mem : x ∈ Finset.Icc a (a + len) := by
    rw [Finset.mem_Icc]
    constructor <;> nlinarith
  have hU_ne : (prefUnion k0).Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    have : W k0 = 0 := by simp [W, he]
    nlinarith
  exact ⟨prefUnion k0, hpref_sub k0, hU_ne, x, hx_mem, hx⟩

-- Split two sets S1, S2 of size ≥ m into halves R1 ≤ M ≤ R2 (up to swapping S1, S2)
lemma median_split_two_sets {m : ℕ} (hm : 2 ≤ m) (S1 S2 : Finset ℕ)
    (h1 : m ≤ S1.card) (h2 : m ≤ S2.card) :
    ∃ M : ℕ, ∃ R1 R2 : Finset ℕ,
      ((R1 ⊆ S1 ∧ R2 ⊆ S2) ∨ (R1 ⊆ S2 ∧ R2 ⊆ S1)) ∧
      m / 2 ≤ R1.card ∧ m / 2 ≤ R2.card ∧
      (∀ x ∈ R1, x ≤ M) ∧ (∀ y ∈ R2, M ≤ y) := by
  have hmed : ∀ (S : Finset ℕ), m ≤ S.card →
      ∃ med : ℕ, m / 2 ≤ (S.filter (· ≤ med)).card ∧ m / 2 ≤ (S.filter (med ≤ ·)).card := by
    intro S hS
    set L := S.sort (· ≤ ·)
    have hLlen : L.length = S.card := Finset.length_sort _
    have hidx : m / 2 < L.length := by omega
    set med := L[m / 2]
    refine ⟨med, ?_, ?_⟩
    · have hsub : (L.take (m / 2)).toFinset ⊆ S.filter (· ≤ med) := by
        intro x hx
        rw [List.mem_toFinset] at hx
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        have hklen : k < m / 2 := by simp only [List.length_take] at hk; omega
        have hkL : k < L.length := by omega
        rw [List.getElem_take]
        refine Finset.mem_filter.mpr ⟨(Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hkL), ?_⟩
        exact List.pairwise_iff_getElem.mp (Finset.pairwise_sort S (· ≤ ·)) k (m / 2) hkL hidx hklen
      have hnd : (L.take (m / 2)).Nodup := (Finset.sort_nodup S (· ≤ ·)).take
      have hc : (L.take (m / 2)).toFinset.card = m / 2 := by
        rw [List.toFinset_card_of_nodup hnd, List.length_take]
        omega
      rw [← hc]
      exact Finset.card_le_card hsub
    · have hsub : (L.drop (m / 2)).toFinset ⊆ S.filter (med ≤ ·) := by
        intro x hx
        rw [List.mem_toFinset] at hx
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        have hkL : m / 2 + k < L.length := by simp only [List.length_drop] at hk; omega
        rw [List.getElem_drop]
        refine Finset.mem_filter.mpr ⟨(Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hkL), ?_⟩
        by_cases hk0 : k = 0
        · simp [hk0, med]
        · exact List.pairwise_iff_getElem.mp (Finset.pairwise_sort S (· ≤ ·)) (m / 2) (m / 2 + k) hidx hkL (by omega)
      have hnd : (L.drop (m / 2)).Nodup := (Finset.sort_nodup S (· ≤ ·)).drop
      have hc : m / 2 ≤ (L.drop (m / 2)).toFinset.card := by
        rw [List.toFinset_card_of_nodup hnd, List.length_drop, hLlen]
        omega
      exact hc.trans (Finset.card_le_card hsub)
  obtain ⟨m1, h1lo, h1hi⟩ := hmed S1 h1
  obtain ⟨m2, h2lo, h2hi⟩ := hmed S2 h2
  rcases le_total m1 m2 with h12 | h21
  · refine ⟨m1, S1.filter (· ≤ m1), S2.filter (m2 ≤ ·), Or.inl ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩,
      h1lo, h2hi, ?_, ?_⟩
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro y hy; exact h12.trans (Finset.mem_filter.mp hy).2
  · refine ⟨m2, S2.filter (· ≤ m2), S1.filter (m1 ≤ ·), Or.inr ⟨Finset.filter_subset _ _, Finset.filter_subset _ _⟩,
      h2lo, h1hi, ?_, ?_⟩
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro y hy; exact h21.trans (Finset.mem_filter.mp hy).2

-- Straus median split: non-averaging A ⊆ [1, N] of size ≥ 2*m + 3 yields S1, S2 ⊆ [1, N] of size ≥ m
-- with no equal nonempty subset sums
lemma straus_median_split {N m : ℕ} {A : Finset ℕ}
    (hAsub : A ⊆ Finset.Icc 1 N) (hna : Erdos186.NonAveraging A) (hcard : 2 * m + 3 ≤ A.card) :
    ∃ S1 S2 : Finset ℕ,
      S1 ⊆ Finset.Icc 1 N ∧ S2 ⊆ Finset.Icc 1 N ∧
      m ≤ S1.card ∧ m ≤ S2.card ∧
      ∀ T1 ⊆ S1, ∀ T2 ⊆ S2, T1.Nonempty → T2.Nonempty → T1.sum id ≠ T2.sum id := by
  set L := A.sort (· ≤ ·)
  have hLlen : L.length = A.card := Finset.length_sort _
  have hLnd : L.Nodup := Finset.sort_nodup _ _
  have hLpw : L.Pairwise (· ≤ ·) := Finset.pairwise_sort A (· ≤ ·)
  set k := A.card / 2
  have hk_lt : k < L.length := by omega
  set a_mid := L[k]
  have hamid_A : a_mid ∈ A := (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hk_lt)
  have hamid_leN : a_mid ≤ N := (Finset.mem_Icc.mp (hAsub hamid_A)).2
  set A_lt := A.filter (· < a_mid)
  set A_gt := A.filter (a_mid < ·)
  have hAlt_card : m ≤ A_lt.card := by
    have hsub : (L.take k).toFinset ⊆ A_lt := by
      intro x hx
      rw [List.mem_toFinset] at hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hi_lt_k : i < k := by simp only [List.length_take] at hi; omega
      have hiL : i < L.length := by omega
      rw [List.getElem_take]
      refine Finset.mem_filter.mpr ⟨(Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hiL), ?_⟩
      have hle := List.pairwise_iff_getElem.mp hLpw i k hiL hk_lt hi_lt_k
      have hne : L[i] ≠ L[k] := fun h => by
        have := (List.Nodup.getElem_inj_iff hLnd).mp h; omega
      exact lt_of_le_of_ne hle hne
    have hc : (L.take k).toFinset.card = k := by
      rw [List.toFinset_card_of_nodup hLnd.take, List.length_take]; omega
    have hle := Finset.card_le_card hsub
    omega
  have hAgt_card : m ≤ A_gt.card := by
    have hsub : (L.drop (k + 1)).toFinset ⊆ A_gt := by
      intro x hx
      rw [List.mem_toFinset] at hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hiL : k + 1 + i < L.length := by simp only [List.length_drop] at hi; omega
      rw [List.getElem_drop]
      refine Finset.mem_filter.mpr ⟨(Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hiL), ?_⟩
      have hle := List.pairwise_iff_getElem.mp hLpw k (k + 1 + i) hk_lt hiL (by omega)
      have hne : L[k] ≠ L[k + 1 + i] := fun h => by
        have := (List.Nodup.getElem_inj_iff hLnd).mp h; omega
      exact lt_of_le_of_ne hle hne
    have hc : (L.drop (k + 1)).toFinset.card = L.length - (k + 1) := by
      rw [List.toFinset_card_of_nodup hLnd.drop, List.length_drop]
    have hle := Finset.card_le_card hsub
    omega
  set S1 := A_lt.image (fun x => a_mid - x)
  set S2 := A_gt.image (fun x => x - a_mid)
  refine ⟨S1, S2, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hxA, hxlt⟩ := Finset.mem_filter.mp hx
    have hx1 := (Finset.mem_Icc.mp (hAsub hxA)).1
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro d hd
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨hxA, hxgt⟩ := Finset.mem_filter.mp hx
    have hxN := (Finset.mem_Icc.mp (hAsub hxA)).2
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · have hinj : Set.InjOn (fun x => a_mid - x) (A_lt : Set ℕ) := by
      intro x1 hx1 x2 hx2 heq
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      dsimp at heq; omega
    rw [Finset.card_image_of_injOn hinj]
    exact hAlt_card
  · have hinj : Set.InjOn (fun x => x - a_mid) (A_gt : Set ℕ) := by
      intro x1 hx1 x2 hx2 heq
      have h1 := (Finset.mem_filter.mp hx1).2
      have h2 := (Finset.mem_filter.mp hx2).2
      dsimp at heq; omega
    rw [Finset.card_image_of_injOn hinj]
    exact hAgt_card
  · intro T1 hT1 T2 hT2 hT1ne hT2ne heqsum
    set U1 := T1.image (fun d => a_mid - d)
    set U2 := T2.image (fun d => a_mid + d)
    have hT1_lt : ∀ d ∈ T1, d < a_mid := by
      intro d hd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hT1 hd)
      have hx1 := (Finset.mem_Icc.mp (hAsub (Finset.mem_filter.mp hx).1)).1
      have hxlt := (Finset.mem_filter.mp hx).2
      omega
    have hU1_sub : U1 ⊆ A_lt := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hT1 hd)
      have hxlt := (Finset.mem_filter.mp hx).2
      have : a_mid - (a_mid - x) = x := by omega
      rwa [this]
    have hU2_sub : U2 ⊆ A_gt := by
      intro y hy
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hT2 hd)
      have hxgt := (Finset.mem_filter.mp hx).2
      have : a_mid + (x - a_mid) = x := by omega
      rwa [this]
    have hinj1 : Set.InjOn (fun d => a_mid - d) (T1 : Set ℕ) := by
      intro d1 hd1 d2 hd2 heq
      have h1 := hT1_lt d1 hd1
      have h2 := hT1_lt d2 hd2
      dsimp at heq; omega
    have hinj2 : Set.InjOn (fun d => a_mid + d) (T2 : Set ℕ) := fun _ _ _ _ heq => by
      dsimp at heq; omega
    have hU1_card : U1.card = T1.card := Finset.card_image_of_injOn hinj1
    have hU2_card : U2.card = T2.card := Finset.card_image_of_injOn hinj2
    have hU1_sum : U1.sum id + T1.sum id = U1.card * a_mid := by
      rw [hU1_card]
      have h1 : U1.sum id = ∑ d ∈ T1, (a_mid - d) := by
        rw [Finset.sum_image (fun d1 hd1 d2 hd2 h => hinj1 hd1 hd2 h)]
        rfl
      rw [h1]
      calc (∑ d ∈ T1, (a_mid - d)) + T1.sum id
          = ∑ d ∈ T1, ((a_mid - d) + d) := (Finset.sum_add_distrib).symm
        _ = ∑ _d ∈ T1, a_mid := Finset.sum_congr rfl fun d hd => by
            have := hT1_lt d hd; omega
        _ = T1.card * a_mid := by rw [Finset.sum_const, smul_eq_mul]
    have hU2_sum : U2.sum id = U2.card * a_mid + T2.sum id := by
      rw [hU2_card]
      have h1 : U2.sum id = ∑ d ∈ T2, (a_mid + d) := by
        rw [Finset.sum_image (fun d1 hd1 d2 hd2 h => hinj2 hd1 hd2 h)]
        rfl
      rw [h1, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
      rfl
    have hUdisj : Disjoint U1 U2 := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      have hlt := (Finset.mem_filter.mp (hU1_sub hy1)).2
      have hgt := (Finset.mem_filter.mp (hU2_sub hy2)).2
      omega
    have hU_sub : U1 ∪ U2 ⊆ A.erase a_mid := by
      intro y hy
      rcases Finset.mem_union.mp hy with h1 | h2
      · obtain ⟨hyA, hylt⟩ := Finset.mem_filter.mp (hU1_sub h1)
        exact Finset.mem_erase.mpr ⟨by omega, hyA⟩
      · obtain ⟨hyA, hygt⟩ := Finset.mem_filter.mp (hU2_sub h2)
        exact Finset.mem_erase.mpr ⟨by omega, hyA⟩
    have hU_card : 2 ≤ (U1 ∪ U2).card := by
      rw [Finset.card_union_of_disjoint hUdisj, hU1_card, hU2_card]
      have h1 := hT1ne.card_pos
      have h2 := hT2ne.card_pos
      omega
    have hU_sum : (∑ x ∈ U1 ∪ U2, x) = (U1 ∪ U2).card * a_mid := by
      have hs : (∑ x ∈ U1 ∪ U2, x) = U1.sum id + U2.sum id := Finset.sum_union hUdisj
      rw [hs, Finset.card_union_of_disjoint hUdisj, add_mul]
      omega
    exact hna a_mid hamid_A (U1 ∪ U2) hU_sub hU_card hU_sum

-- Pure ℕ bound: for k ≥ 50, 16 * (k + 1)^3 ≤ 2 ^ (k / 2)
lemma cube_le_two_pow_half : ∀ k : ℕ, 50 ≤ k → 16 * (k + 1) ^ 3 ≤ 2 ^ (k / 2) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk50
    by_cases hk52 : k < 52
    · have : k = 50 ∨ k = 51 := by omega
      rcases this with rfl | rfl <;> norm_num
    · have hk2 : 50 ≤ k - 2 := by omega
      have hih := ih (k - 2) (by omega) hk2
      have hdiv : k / 2 = (k - 2) / 2 + 1 := by omega
      have hpow : 2 ^ (k / 2) = 2 * 2 ^ ((k - 2) / 2) := by rw [hdiv, pow_succ']
      have hkm1 : k - 2 + 1 = k - 1 := by omega
      rw [hkm1] at hih
      have hcube : (k + 1) ^ 3 ≤ 2 * (k - 1) ^ 3 := by
        set u := k - 1
        have hku : k + 1 = u + 2 := by omega
        rw [hku]
        have hu10 : 10 ≤ u := by omega
        have hexp : (u + 2) ^ 3 = u ^ 3 + 6 * u ^ 2 + 12 * u + 8 := by ring
        have h6 : 6 * u ^ 2 + 12 * u + 8 ≤ u ^ 3 := by
          have h1 : 10 * u ^ 2 ≤ u ^ 3 := by
            calc 10 * u ^ 2 ≤ u * u ^ 2 := Nat.mul_le_mul_right _ hu10
              _ = u ^ 3 := by ring
          have h2 : 12 * u + 8 ≤ 4 * u ^ 2 := by nlinarith
          linarith
        linarith
      rw [hpow]
      calc 16 * (k + 1) ^ 3 ≤ 16 * (2 * (k - 1) ^ 3) := Nat.mul_le_mul_left 16 hcube
        _ = 2 * (16 * (k - 1) ^ 3) := by ring
        _ ≤ 2 * 2 ^ ((k - 2) / 2) := Nat.mul_le_mul_left 2 hih

section FinalGlue

variable
  (h_theorem_6_1 : ∀ {α_inv n : ℕ}, 4096 ≤ α_inv → 2 ≤ n →
    ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 n →
    100 * (log2P (2 * (16 * α_inv * (4 * α_inv))) + 1) ≤ log2P n →
    (65536 * (2 * (16 * α_inv * (4 * α_inv)))) ^ 2 * n ≤ A.card ^ 2 →
    1000000 * (2 * (16 * α_inv * (4 * α_inv))) * (log2P n) ^ 3 ≤ A.card →
    ∃ d_tot a len : ℕ,
      1 ≤ d_tot ∧ d_tot ≤ 3 * n / A.card ∧
      0 < a ∧ A.card * A.card / 256 ≤ len ∧
      d_tot * a ≤ (A.card / 4) * n ∧
      ∀ x ∈ Finset.Icc a (a + len), d_tot * x ∈ A.powerset.image (fun S => S.sum id))
  (h_homAP : ∀ {d a len M N : ℕ}, 0 < d → 0 < a → N ≤ len → ∀ (R : Finset ℕ),
    (∀ x ∈ R, M ≤ x ∧ x ≤ N) → d * (a + len) ≤ (R.card - d) * M →
    ∃ U ⊆ R, U.Nonempty ∧ ∃ x ∈ Finset.Icc a (a + len), U.sum id = d * x)
  (h_med_split : ∀ {m : ℕ}, 2 ≤ m → ∀ (S1 S2 : Finset ℕ),
    m ≤ S1.card → m ≤ S2.card →
    ∃ M : ℕ, ∃ R1 R2 : Finset ℕ,
      ((R1 ⊆ S1 ∧ R2 ⊆ S2) ∨ (R1 ⊆ S2 ∧ R2 ⊆ S1)) ∧
      m / 2 ≤ R1.card ∧ m / 2 ≤ R2.card ∧
      (∀ x ∈ R1, x ≤ M) ∧ (∀ y ∈ R2, M ≤ y))

-- Corollary 1.10: no disjoint-subset-sum pair S1, S2 ⊆ [1, N] can both have size ≥ 2 * 65536 * ℓ * (√N + 1)
include h_theorem_6_1 h_homAP h_med_split in
lemma disjoint_subsetSum_bound {α_inv : ℕ} (hα : 4096 ≤ α_inv) :
    let ℓ : ℕ := 2 * (16 * α_inv * (4 * α_inv))
    let N0 : ℕ := max (2 ^ 50) (2 ^ (200 * (log2P ℓ + 1)))
    ∀ N ≥ N0, ∀ S1 S2 : Finset ℕ,
      S1 ⊆ Finset.Icc 1 N → S2 ⊆ Finset.Icc 1 N →
      (∀ T1 ⊆ S1, ∀ T2 ⊆ S2, T1.Nonempty → T2.Nonempty → T1.sum id ≠ T2.sum id) →
      ¬ (2 * (65536 * ℓ * (Nat.sqrt N + 1)) ≤ S1.card ∧
         2 * (65536 * ℓ * (Nat.sqrt N + 1)) ≤ S2.card) := by
  intro ℓ N0 N hN S1 S2 hS1 hS2 hnoeq ⟨hcard1, hcard2⟩
  have hℓpos : 1 ≤ ℓ := Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (Nat.mul_pos (by decide) (by omega)))
  set m := 65536 * ℓ * (Nat.sqrt N + 1)
  have hm_ge2 : 2 ≤ 2 * m := by
    have : 1 ≤ m := Nat.mul_pos (Nat.mul_pos (by decide) hℓpos) (Nat.succ_pos _)
    omega
  obtain ⟨M, R1, R2, hcases, hR1_card, hR2_card, hR1_le, hR2_ge⟩ :=
    h_med_split hm_ge2 S1 S2 hcard1 hcard2
  have hm_le_R1 : m ≤ R1.card := by simpa using hR1_card
  have hm_le_R2 : m ≤ R2.card := by simpa using hR2_card
  obtain ⟨R1', hR1'_sub, hR1'_card⟩ := Finset.exists_subset_card_eq hm_le_R1
  have hR1_sub_Icc : R1 ⊆ Finset.Icc 1 N := by
    rcases hcases with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact h1.trans (by assumption)
  have hR2_sub_Icc : R2 ⊆ Finset.Icc 1 N := by
    rcases hcases with ⟨_, h2⟩ | ⟨_, h2⟩ <;> exact h2.trans (by assumption)
  have hR1'_IccM : R1' ⊆ Finset.Icc 1 M := fun x hx =>
    Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hR1_sub_Icc (hR1'_sub hx))).1, hR1_le x (hR1'_sub hx)⟩
  have hm_le_M : m ≤ M := by
    have h := Finset.card_le_card hR1'_IccM
    simp only [Nat.card_Icc, add_tsub_cancel_right] at h
    omega
  have hM_le_N : M ≤ N := by
    have hR2ne : R2.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy⟩ := hR2ne
    exact (hR2_ge y hy).trans (Finset.mem_Icc.mp (hR2_sub_Icc hy)).2
  have hN_ge_50 : 2 ^ 50 ≤ N := (le_max_left _ _).trans hN
  have hN_ge_ell : 2 ^ (200 * (log2P ℓ + 1)) ≤ N := (le_max_right _ _).trans hN
  -- Check hypotheses of theorem_6_1 on R1' ⊆ Icc 1 M
  have hM_ge2 : 2 ≤ M := by
    have h2m : 2 ≤ m := by
      have : 2 ≤ 65536 * ℓ := by omega
      exact this.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
    omega
  have hsqrt_ge_ell : 2 ^ (100 * (log2P ℓ + 1)) ≤ Nat.sqrt N := by
    apply Nat.le_sqrt.mpr
    have heq : 100 * (log2P ℓ + 1) + 100 * (log2P ℓ + 1) = 200 * (log2P ℓ + 1) := by ring
    rw [← pow_add, heq]
    exact hN_ge_ell
  have hL_M : 100 * (log2P ℓ + 1) ≤ log2P M := by
    have h1 : 2 ^ (100 * (log2P ℓ + 1)) ≤ M := by
      have h2 : Nat.sqrt N ≤ m := by
        have : 1 ≤ 65536 * ℓ := Nat.mul_pos (by decide) hℓpos
        calc Nat.sqrt N ≤ Nat.sqrt N + 1 := Nat.le_succ _
          _ = 1 * (Nat.sqrt N + 1) := (one_mul _).symm
          _ ≤ (65536 * ℓ) * (Nat.sqrt N + 1) := Nat.mul_le_mul_right _ this
      exact hsqrt_ge_ell.trans (h2.trans hm_le_M)
    have h2 : 100 * (log2P ℓ + 1) ≤ Nat.log 2 M := Nat.le_log_of_pow_le (by decide) h1
    exact h2.trans (Nat.le_succ _)
  have hm_quad_N : (65536 * ℓ) ^ 2 * N ≤ m ^ 2 := by
    have hNlt : N ≤ (Nat.sqrt N + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt N
      rw [sq]; exact Nat.le_of_lt this
    calc (65536 * ℓ) ^ 2 * N ≤ (65536 * ℓ) ^ 2 * (Nat.sqrt N + 1) ^ 2 := Nat.mul_le_mul_left _ hNlt
      _ = m ^ 2 := by dsimp [m]; ring
  have hm_quad_M : (65536 * ℓ) ^ 2 * M ≤ R1'.card ^ 2 := by
    rw [hR1'_card]
    exact (Nat.mul_le_mul_left _ hM_le_N).trans hm_quad_N
  have hm_log_M : 1000000 * ℓ * (log2P M) ^ 3 ≤ R1'.card := by
    rw [hR1'_card]
    have hlog_le : log2P M ≤ log2P N := log2P_mono hM_le_N
    have hk50 : 50 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) hN_ge_50
    have hcube : 16 * (log2P N) ^ 3 ≤ 2 ^ (Nat.log 2 N / 2) := cube_le_two_pow_half _ hk50
    have hpow_sqrt : 2 ^ (Nat.log 2 N / 2) ≤ Nat.sqrt N := by
      apply Nat.le_sqrt.mpr
      have h2k : 2 ^ (Nat.log 2 N) ≤ N := Nat.pow_log_le_self 2 (by omega)
      calc 2 ^ (Nat.log 2 N / 2) * 2 ^ (Nat.log 2 N / 2)
          = 2 ^ (Nat.log 2 N / 2 + Nat.log 2 N / 2) := (pow_add 2 _ _).symm
        _ ≤ 2 ^ (Nat.log 2 N) := Nat.pow_le_pow_right (by decide) (by omega)
        _ ≤ N := h2k
    have h16 : 16 * (log2P M) ^ 3 ≤ Nat.sqrt N + 1 := by
      have : (log2P M) ^ 3 ≤ (log2P N) ^ 3 := Nat.pow_le_pow_left hlog_le 3
      calc 16 * (log2P M) ^ 3 ≤ 16 * (log2P N) ^ 3 := Nat.mul_le_mul_left 16 this
        _ ≤ 2 ^ (Nat.log 2 N / 2) := hcube
        _ ≤ Nat.sqrt N := hpow_sqrt
        _ ≤ Nat.sqrt N + 1 := Nat.le_succ _
    calc 1000000 * ℓ * (log2P M) ^ 3 ≤ 1048576 * ℓ * (log2P M) ^ 3 := by
          have : 1000000 ≤ 1048576 := by decide
          calc 1000000 * ℓ * (log2P M) ^ 3 = 1000000 * (ℓ * (log2P M) ^ 3) := by ring
            _ ≤ 1048576 * (ℓ * (log2P M) ^ 3) := Nat.mul_le_mul_right _ this
            _ = 1048576 * ℓ * (log2P M) ^ 3 := by ring
      _ = 65536 * ℓ * (16 * (log2P M) ^ 3) := by ring
      _ ≤ 65536 * ℓ * (Nat.sqrt N + 1) := Nat.mul_le_mul_left _ h16
  obtain ⟨d_tot, a, len, hd_pos, hd_le_3, ha_pos, hlen_ge, hda_le, hAP⟩ :=
    h_theorem_6_1 hα hM_ge2 R1' hR1'_IccM hL_M hm_quad_M hm_log_M
  rw [hR1'_card] at hd_le_3 hlen_ge hda_le
  -- Check N ≤ len
  have hN_le_len : N ≤ len := by
    have h1 : 256 * N ≤ m * m := by
      have h2 : 256 ≤ (65536 * ℓ) ^ 2 := by
        have : 65536 ≤ 65536 * ℓ := Nat.le_mul_of_pos_right _ hℓpos
        nlinarith
      calc 256 * N ≤ (65536 * ℓ) ^ 2 * N := Nat.mul_le_mul_right N h2
        _ ≤ m ^ 2 := hm_quad_N
        _ = m * m := sq m
    have h2 : N ≤ m * m / 256 := (Nat.le_div_iff_mul_le (by decide : 0 < 256)).mpr (by rw [mul_comm]; exact h1)
    exact h2.trans hlen_ge
  -- Check d_tot * (a + N) ≤ (R2.card - d_tot) * M
  have hreach : d_tot * (a + N) ≤ (R2.card - d_tot) * M := by
    have hm_pos : 0 < m := by
      have : 1 ≤ 65536 * ℓ := Nat.mul_pos (by decide) hℓpos
      exact Nat.mul_pos this (Nat.succ_pos _)
    have hdm_le : d_tot * m ≤ 3 * M := by
      calc d_tot * m ≤ (3 * M / m) * m := Nat.mul_le_mul_right m hd_le_3
        _ ≤ 3 * M := Nat.div_mul_le_self _ _
    have h12N : 12 * N ≤ m * m := by
      have h2 : 12 ≤ (65536 * ℓ) ^ 2 := by
        have : 65536 ≤ 65536 * ℓ := Nat.le_mul_of_pos_right _ hℓpos
        nlinarith
      calc 12 * N ≤ (65536 * ℓ) ^ 2 * N := Nat.mul_le_mul_right N h2
        _ ≤ m ^ 2 := hm_quad_N
        _ = m * m := sq m
    have hdN_le : d_tot * N ≤ (m / 4) * M := by
      have h1 : (4 * (d_tot * N)) * m ≤ (m * M) * m := by
        calc (4 * (d_tot * N)) * m = 4 * N * (d_tot * m) := by ring
          _ ≤ 4 * N * (3 * M) := Nat.mul_le_mul_left _ hdm_le
          _ = (12 * N) * M := by ring
          _ ≤ (m * m) * M := Nat.mul_le_mul_right M h12N
          _ = (m * M) * m := by ring
      have h2 : 4 * (d_tot * N) ≤ m * M := Nat.le_of_mul_le_mul_right h1 hm_pos
      have hm4 : 4 * (m / 4) = m := by
        have : 4 ∣ m := ⟨16384 * ℓ * (Nat.sqrt N + 1), by dsimp [m]; ring⟩
        exact Nat.mul_div_cancel' this
      have h3 : 4 * (d_tot * N) ≤ 4 * ((m / 4) * M) := by
        calc 4 * (d_tot * N) ≤ m * M := h2
          _ = (4 * (m / 4)) * M := by rw [hm4]
          _ = 4 * ((m / 4) * M) := by ring
      exact Nat.le_of_mul_le_mul_left h3 (by decide)
    have hd_le_m4 : d_tot ≤ m / 4 := by
      have h1 : 4 * d_tot * m ≤ m * m := by
        calc 4 * d_tot * m = 4 * (d_tot * m) := by ring
          _ ≤ 4 * (3 * M) := Nat.mul_le_mul_left 4 hdm_le
          _ ≤ 12 * N := by omega
          _ ≤ m * m := h12N
      have h2 : 4 * d_tot ≤ m := Nat.le_of_mul_le_mul_right h1 hm_pos
      omega
    have hhalf : m / 4 + m / 4 ≤ R2.card - d_tot := by omega
    calc d_tot * (a + N) = d_tot * a + d_tot * N := mul_add _ _ _
      _ ≤ (m / 4) * M + (m / 4) * M := Nat.add_le_add hda_le hdN_le
      _ = (m / 4 + m / 4) * M := (add_mul _ _ _).symm
      _ ≤ (R2.card - d_tot) * M := Nat.mul_le_mul_right M hhalf
  -- Apply exists_subset_sum_in_homAP to R2 with len := N
  obtain ⟨U2, hU2R2, hU2ne, x, hxIcc, hU2sum⟩ :=
    h_homAP hd_pos ha_pos le_rfl R2 (fun y hy => ⟨hR2_ge y hy, (Finset.mem_Icc.mp (hR2_sub_Icc hy)).2⟩) hreach
  have hxIcc' : x ∈ Finset.Icc a (a + len) := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hxIcc
    exact Finset.mem_Icc.mpr ⟨h1, by omega⟩
  obtain ⟨U1, hU1p, hU1sum⟩ := Finset.mem_image.mp (hAP x hxIcc')
  have hU1R1 : U1 ⊆ R1 := (Finset.mem_powerset.mp hU1p).trans hR1'_sub
  have hU1ne : U1.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    have : U1.sum id = 0 := by simp [he]
    have hxa : 0 < x := by have := (Finset.mem_Icc.mp hxIcc).1; omega
    have hpos : 0 < d_tot * x := Nat.mul_pos hd_pos hxa
    omega
  have heqsum : U1.sum id = U2.sum id := hU1sum.trans hU2sum.symm
  rcases hcases with ⟨hR1S1, hR2S2⟩ | ⟨hR1S2, hR2S1⟩
  · exact hnoeq U1 (hU1R1.trans hR1S1) U2 (hU2R2.trans hR2S2) hU1ne hU2ne heqsum
  · exact hnoeq U2 (hU2R2.trans hR2S1) U1 (hU1R1.trans hR1S2) hU2ne hU1ne heqsum.symm

-- Main Erdos-Sarkozy theorem
include h_theorem_6_1 h_homAP h_med_split in
lemma erdos_sarkozy_from_alpha {α_inv : ℕ} (hα : 4096 ≤ α_inv) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (Erdos186.F N : ℝ) ≤ C * Real.sqrt ((N : ℝ) * Real.log N) := by
  let ℓ : ℕ := 2 * (16 * α_inv * (4 * α_inv))
  let N0 : ℕ := max (2 ^ 50) (2 ^ (200 * (log2P ℓ + 1)))
  have hℓpos : 1 ≤ ℓ := Nat.mul_pos (by decide) (Nat.mul_pos (Nat.mul_pos (by decide) (by omega)) (Nat.mul_pos (by decide) (by omega)))
  refine ⟨(8 * 65536 * ℓ : ℝ), by positivity, Filter.eventually_atTop.mpr ⟨N0, fun N hN => ?_⟩⟩
  have hN_ge_50 : 2 ^ 50 ≤ N := (le_max_left _ _).trans hN
  have hF_le : Erdos186.F N ≤ 8 * 65536 * ℓ * Nat.sqrt N := by
    unfold Erdos186.F
    apply Finset.sup_le
    intro A hA
    obtain ⟨hAp, hna⟩ := Finset.mem_filter.mp hA
    have hAsub : A ⊆ Finset.Icc 1 N := Finset.mem_powerset.mp hAp
    by_contra hgt
    push Not at hgt
    set m := 2 * (65536 * ℓ * (Nat.sqrt N + 1))
    have hsqrt_ge : 4 ≤ Nat.sqrt N := by
      apply Nat.le_sqrt.mpr
      have : 16 ≤ 2 ^ 50 := by norm_num
      omega
    have h2m3 : 2 * m + 3 ≤ A.card := by
      have h1 : 2 * m + 3 = 4 * 65536 * ℓ * Nat.sqrt N + 4 * 65536 * ℓ + 3 := by dsimp [m]; ring
      have h2 : 4 * 65536 * ℓ + 3 ≤ 4 * 65536 * ℓ * Nat.sqrt N := by
        have hpos : 1 ≤ 65536 * ℓ := Nat.mul_pos (by decide) hℓpos
        calc 4 * 65536 * ℓ + 3 ≤ 4 * 65536 * ℓ * 4 := by omega
          _ ≤ 4 * 65536 * ℓ * Nat.sqrt N := Nat.mul_le_mul_left _ hsqrt_ge
      have h8 : 8 * 65536 * ℓ * Nat.sqrt N = 4 * 65536 * ℓ * Nat.sqrt N + 4 * 65536 * ℓ * Nat.sqrt N := by ring
      omega
    obtain ⟨S1, S2, hS1, hS2, hS1c, hS2c, hnoeq⟩ := straus_median_split hAsub hna h2m3
    exact disjoint_subsetSum_bound h_theorem_6_1 h_homAP h_med_split hα N hN S1 S2 hS1 hS2 hnoeq ⟨hS1c, hS2c⟩
  have hF_R : (Erdos186.F N : ℝ) ≤ (8 * 65536 * ℓ : ℝ) * (Nat.sqrt N : ℝ) := by exact_mod_cast hF_le
  have hsqrt_le : (Nat.sqrt N : ℝ) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have h1 : Nat.sqrt N * Nat.sqrt N ≤ N := Nat.sqrt_le N
    have h2 : (Nat.sqrt N : ℝ) ^ 2 = ((Nat.sqrt N * Nat.sqrt N : ℕ) : ℝ) := by push_cast; ring
    rw [h2]; exact_mod_cast h1
  have hlog_ge1 : (1 : ℝ) ≤ Real.log (N : ℝ) := by
    have h3 : (3 : ℝ) ≤ (N : ℝ) := by
      have : 3 ≤ N := le_trans (by norm_num : 3 ≤ 2 ^ 50) hN_ge_50
      exact_mod_cast this
    have hexp : Real.exp 1 ≤ (N : ℝ) := by linarith [Real.exp_one_lt_d9]
    have h := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at h
  have hsqrt_log : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) := by
    apply Real.sqrt_le_sqrt
    calc (N : ℝ) = (N : ℝ) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) * Real.log (N : ℝ) := mul_le_mul_of_nonneg_left hlog_ge1 (by positivity)
  calc (Erdos186.F N : ℝ) ≤ (8 * 65536 * ℓ : ℝ) * (Nat.sqrt N : ℝ) := hF_R
    _ ≤ (8 * 65536 * ℓ : ℝ) * Real.sqrt ((N : ℝ) * Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hsqrt_le.trans hsqrt_log) (by positivity)

include h_theorem_6_1 h_homAP h_med_split in
theorem erdos_sarkozy_final :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, (Erdos186.F N : ℝ) ≤ C * Real.sqrt ((N : ℝ) * Real.log N) :=
  erdos_sarkozy_from_alpha h_theorem_6_1 h_homAP h_med_split (le_refl 4096)

end FinalGlue


private theorem lemma_6_2_proved {b : ℕ} (hb : 2 ≤ b) (A A_inj : Finset ℕ)
    (hAinj_sub : A_inj ⊆ A)
    (hAinj_lt : ∀ x ∈ A_inj, x < b)
    (hA_le : A.card ≤ 16 * A_inj.card)
    (hm1_big : 1600 * (log2P b) ^ 2 ≤ A_inj.card)
    (hdiv : ∀ d : ℕ, d ∣ b → 2 ≤ d → d ≤ 8 * b / A_inj.card →
      1200 * (log2P b) ^ 2 + 8 * d ≤ (A.filter (fun a => ¬ d ∣ a)).card) :
    let k := 8192 * b / A_inj.card + 2
    min (A_inj.card * A_inj.card / 131072) (b / 4) ≤ (subsetSumModLe b (k + 1) A).card :=
  lemma_6_2
    (fun b _ H => zmod_subgroup_char b H)
    (fun {G} _ _ _ K P h0 hPK hgen k hk => cos_sumset_bound_subgroup K P h0 hPK hgen k hk)
    (fun {d} _ A hdiv => subsetSumMod_eq_univ A hdiv)
    (fun {α} _ _ E c => chernoff_half_lower E c)
    (fun {G} _ _ _ A d hd => card_small_growth_le A d hd)
    (fun {G} _ _ A L => card_sdiff_vadd_list_sum_le A L)
    hb A A_inj hAinj_sub hAinj_lt hA_le hm1_big hdiv

private theorem theorem_6_1_proved {α_inv n : ℕ} (hα4096 : 4096 ≤ α_inv) (hn : 2 ≤ n)
    (A : Finset ℕ) (hAsub : A ⊆ Finset.Icc 1 n)
    (hL_big : 100 * (log2P (2 * (16 * α_inv * (4 * α_inv))) + 1) ≤ log2P n)
    (hm_quad : (65536 * (2 * (16 * α_inv * (4 * α_inv)))) ^ 2 * n ≤ A.card ^ 2)
    (hm_log : 1000000 * (2 * (16 * α_inv * (4 * α_inv))) * (log2P n) ^ 3 ≤ A.card) :
    ∃ d_tot a len : ℕ,
      1 ≤ d_tot ∧ d_tot ≤ 3 * n / A.card ∧
      0 < a ∧ A.card * A.card / 256 ≤ len ∧
      d_tot * a ≤ (A.card / 4) * n ∧
      ∀ x ∈ Finset.Icc a (a + len), d_tot * x ∈ A.powerset.image (fun S => S.sum id) :=
  theorem_6_1
    (fun {α β} _ _ _ _ E C hβ => chernoff_lower E C hβ)
    (fun {α β} _ _ _ _ E C hβ => chernoff_upper E C hβ)
    (fun {α} _ _ E c => chernoff_half_lower E c)
    card_union_vadd_ge
    subsetSumLe_insert_superset
    (fun {b} hb A A_inj h1 h2 h3 h4 h5 => lemma_6_2_proved hb A A_inj h1 h2 h3 h4 h5)
    (fun {ℓ n} hℓ hn A hA hm => lemma_6_3 hℓ hn A hA hm)
    (fun {α_inv Q} hα hQ S hsub h0 hdense hcop => weak_lev_interval hα hQ S hsub h0 hdense hcop)
    hα4096 hn A hAsub hL_big hm_quad hm_log

private theorem erdos_sarkozy_proved :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (Erdos186.F N : ℝ) ≤ C * Real.sqrt ((N : ℝ) * Real.log N) :=
  erdos_sarkozy_final
    (fun {α_inv n} hα hn A hA hL hq hl => theorem_6_1_proved hα hn A hA hL hq hl)
    (fun {d a len M N} hd ha hlen R hR hreach => exists_subset_sum_in_homAP hd ha hlen R hR hreach)
    (fun {m} hm S1 S2 h1 h2 => median_split_two_sets hm S1 S2 h1 h2)

end Erdos186Proof

theorem OMA.solution : type_of% @Erdos186.erdos_186.variants.erdos_sarkozy :=
  Erdos186Proof.erdos_sarkozy_proved

