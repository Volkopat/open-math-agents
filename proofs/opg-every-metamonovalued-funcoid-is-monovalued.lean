import OMAStatements.S_opg_every_metamonovalued_funcoid_is_monovalued
import Mathlib

/-!
Two funcoids into a singleton, obtained from contact with disjoint subsets,
have empty meet. If the original funcoid fails monovaluedness on these sets,
the two composites have a nonempty common lower bound. The lower bound is
constructed by testing every partition of the source set.
-/

namespace OMA.Porton

open Set
open OMA.S_opg_every_metamonovalued_funcoid_is_monovalued
  (IsFuncoid comp rev meet Metamonovalued Monovalued)

private theorem union_mono {A : Type} {p : Set A → Prop}
    (hp : ∀ X Y, p (X ∪ Y) ↔ p X ∨ p Y) : Monotone p := by
  intro X Y hXY hX
  have h := (hp X Y).mpr (Or.inl hX)
  rwa [Set.union_eq_right.mpr hXY] at h

private theorem right_mono {A B : Type} {f : Set A → Set B → Prop}
    (hf : IsFuncoid f) (X : Set A) : Monotone (f X) :=
  union_mono (hf.2.2.2 X)

private def cut {A : Type} (p q : Set A → Prop) (X : Set A) : Prop :=
  ∀ U : Set A, p (X ∩ Uᶜ) ∨ q (X ∩ U)

private theorem cut_imp_left {A : Type} {p q : Set A → Prop} {X : Set A}
    (hq : ¬q ∅) (h : cut p q X) : p X := by
  simpa [hq] using h ∅

private theorem cut_imp_right {A : Type} {p q : Set A → Prop} {X : Set A}
    (hp : ¬p ∅) (h : cut p q X) : q X := by
  simpa [hp] using h Set.univ

private theorem cut_union {A : Type} {p q : Set A → Prop}
    (hp : ∀ X Y, p (X ∪ Y) ↔ p X ∨ p Y)
    (hq : ∀ X Y, q (X ∪ Y) ↔ q X ∨ q Y) (X Y : Set A) :
    cut p q (X ∪ Y) ↔ cut p q X ∨ cut p q Y := by
  classical
  have hpmono := union_mono hp
  have hqmono := union_mono hq
  have lift {S T : Set A} (hST : S ⊆ T) (h : cut p q S) : cut p q T := by
    intro U
    exact (h U).imp
      (hpmono (Set.inter_subset_inter_left _ hST))
      (hqmono (Set.inter_subset_inter_left _ hST))
  refine ⟨?_, fun h => h.elim (lift Set.subset_union_left) (lift Set.subset_union_right)⟩
  intro h
  by_contra! hfail
  obtain ⟨U, hpU, hqU⟩ : ∃ U, ¬p (X ∩ Uᶜ) ∧ ¬q (X ∩ U) := by
    simpa only [cut, not_forall, not_or] using hfail.1
  obtain ⟨V, hpV, hqV⟩ : ∃ V, ¬p (Y ∩ Vᶜ) ∧ ¬q (Y ∩ V) := by
    simpa only [cut, not_forall, not_or] using hfail.2
  let W := (X ∩ U) ∪ ((Y \ X) ∩ V)
  have hleft : (X ∪ Y) ∩ Wᶜ ⊆ (X ∩ Uᶜ) ∪ (Y ∩ Vᶜ) := by
    intro a ha
    simp only [W, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff, Set.mem_compl_iff] at ha ⊢
    tauto
  have hright : (X ∪ Y) ∩ W ⊆ (X ∩ U) ∪ (Y ∩ V) := by
    intro a ha
    simp only [W, Set.mem_inter_iff, Set.mem_union, Set.mem_sdiff] at ha ⊢
    tauto
  rcases h W with h | h
  · exact ((hp _ _).mp (hpmono hleft h)).elim hpU hpV
  · exact ((hq _ _).mp (hqmono hright h)).elim hqU hqV

private def toUnit {A : Type} (p : Set A → Prop) : Set A → Set Unit → Prop :=
  fun X Z => p X ∧ Z.Nonempty

private theorem toUnit_funcoid {A : Type} {p : Set A → Prop}
    (h0 : ¬ p ∅) (hp : ∀ X Y, p (X ∪ Y) ↔ p X ∨ p Y) :
    IsFuncoid (toUnit p) := by
  refine ⟨fun Z h => h0 h.1, fun X h => Set.not_nonempty_empty h.2, ?_, ?_⟩
  · intro X Y Z
    unfold toUnit
    rw [hp]
    tauto
  · intro X Y Z
    unfold toUnit
    rw [Set.union_nonempty]
    tauto

private def contact {B : Type} (Y : Set B) : Set B → Set Unit → Prop :=
  toUnit fun U => (U ∩ Y).Nonempty

private theorem contact_funcoid {B : Type} (Y : Set B) : IsFuncoid (contact Y) := by
  apply toUnit_funcoid
  · simp
  · intro U V
    rw [Set.union_inter_distrib_right, Set.union_nonempty]

private theorem comp_contact {A B : Type} {f : Set A → Set B → Prop}
    (hf : IsFuncoid f) {X : Set A} {Y : Set B} {Z : Set Unit}
    (hXY : f X Y) (hZ : Z.Nonempty) : comp (contact Y) f X Z := by
  intro U
  by_cases h : (U ∩ Y).Nonempty
  · exact Or.inr ⟨h,hZ⟩
  · apply Or.inl
    apply right_mono hf X _ hXY
    intro y hy hyU
    exact h ⟨y,hyU,hy⟩

private theorem no_contact_meet {B : Type} {Y Y' : Set B}
    (hsep : ¬ (Y ∩ Y').Nonempty) (U : Set B) (Z : Set Unit) :
    ¬ meet ({contact Y, contact Y'} : Set (Set B → Set Unit → Prop)) U Z := by
  rintro ⟨r, hr, hbelow, hUZ⟩
  have hsplit : (U ∩ Y) ∪ (U ∩ Yᶜ) = U := by
    rw [← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
  have hh := (hr.2.2.1 (U ∩ Y) (U ∩ Yᶜ) Z).mp (hsplit.symm ▸ hUZ)
  rcases hh with hl | hr'
  · have h : contact Y' (U ∩ Y) Z :=
      hbelow (contact Y') (by simp) _ _ hl
    obtain ⟨b, hb, hb'⟩ := h.1
    exact hsep ⟨b,hb.2,hb'⟩
  · have h : contact Y (U ∩ Yᶜ) Z :=
      hbelow (contact Y) (by simp) _ _ hr'
    obtain ⟨b,hb,hb'⟩ := h.1
    exact hb.2 hb'

theorem monovalued {A B : Type} {f : Set A → Set B → Prop}
    (hf : IsFuncoid f) (hmeta : Metamonovalued f) : Monovalued f := by
  classical
  intro Y Y' hcomp
  by_contra hsep
  let G : Set (Set B → Set Unit → Prop) := {contact Y, contact Y'}
  have hG (g : Set B → Set Unit → Prop) (hg : g ∈ G) : IsFuncoid g := by
    change g ∈ ({contact Y, contact Y'} : Set _) at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl <;> exact contact_funcoid _
  let p : Set A → Prop := fun X => f X Y
  let q : Set A → Prop := fun X => f X Y'
  have hp0 : ¬ p ∅ := hf.1 Y
  have hq0 : ¬ q ∅ := hf.1 Y'
  let r := toUnit (cut p q)
  have hr : IsFuncoid r := by
    apply toUnit_funcoid
    · intro h
      exact hp0 (cut_imp_left hq0 h)
    · exact cut_union (fun X X' => hf.2.2.1 X X' Y) (fun X X' => hf.2.2.1 X X' Y')
  have hr_lower : ∀ s ∈ {s | ∃ g ∈ G, s = comp g f}, ∀ X Z, r X Z → s X Z := by
    rintro s ⟨g,hg,rfl⟩ X Z ⟨hXZ,hZ⟩
    change g ∈ ({contact Y, contact Y'} : Set _) at hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact comp_contact hf (show f X Y from cut_imp_left (p := p) (q := q) hq0 hXZ) hZ
    · exact comp_contact hf (show f X Y' from cut_imp_right (p := p) (q := q) hp0 hXZ) hZ
  have hr_univ : r Set.univ Set.univ := by
    refine ⟨?_, ⟨(), Set.mem_univ _⟩⟩
    intro U
    simpa only [Set.univ_inter, p, q, rev] using hcomp U
  have himpossible : comp (meet G) f Set.univ Set.univ := by
    rw [hmeta Unit G hG]
    exact ⟨r,hr,hr_lower,hr_univ⟩
  exact (himpossible Set.univ).elim (by simpa using hf.2.1 Set.univ)
    (no_contact_meet hsep Set.univ Set.univ)

end OMA.Porton

theorem OMA.solution :
    type_of% @OMA.S_opg_every_metamonovalued_funcoid_is_monovalued.main := by
  intro A B f hf hmeta
  exact OMA.Porton.monovalued hf hmeta
