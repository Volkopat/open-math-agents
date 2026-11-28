import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1

/-!
# Cyclic exact cover on the distinguished-point slice
-/

open Finset SimpleGraph

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1_H1_R1

/-- One Steiner system through the fixed point, with one block in each
orbit of the rotations of the first seventeen points. -/
def H1 : Prop :=
  let rot := fun (i : Fin 17) (a : Fin 32) =>
    if a.val < 17 then Fin.ofNat 32 ((a.val + i.val) % 17) else a
  ∃ D : Finset (Finset (Fin 32)),
    (∀ S : Finset (Fin 32), S.card = 15 → (31 : Fin 32) ∈ S →
      ∃! a : Fin 32, a ∉ S ∧ insert a S ∈ D) ∧
    (∀ A : Finset (Fin 32), A.card = 16 → (31 : Fin 32) ∈ A →
      ∃! i : Fin 17, A.image (rot i) ∈ D)

/-- Transport an exact cover along injective relabelings. A covering by
the inverse images of a single class supplies a proper coloring. -/
def H2 : Prop :=
  ∀ (x : Fin 32) (r : Fin 17 → Fin 32 → Fin 32) (D : Finset (Finset (Fin 32))),
    (∀ i, Function.Injective (r i)) →
    (∀ i, r i x = x) →
    (∀ S : Finset (Fin 32), S.card = 15 → x ∈ S →
      ∃! a : Fin 32, a ∉ S ∧ insert a S ∈ D) →
    (∀ A : Finset (Fin 32), A.card = 16 → x ∈ A →
      ∃ i : Fin 17, A.image (r i) ∈ D) →
    ((J(32, 16)).induce {v | x ∈ v.val}).Colorable 17

lemma rot_injective (i : Fin 17) :
    Function.Injective (fun a : Fin 32 =>
      if a.val < 17 then Fin.ofNat 32 ((a.val + i.val) % 17) else a) := by
  intro a b h
  have he := congrArg Fin.val h
  have ha := Nat.mod_lt (a.val + i.val) (by decide : 0 < 17)
  have hb := Nat.mod_lt (b.val + i.val) (by decide : 0 < 17)
  by_cases ha' : a.val < 17 <;> by_cases hb' : b.val < 17
  all_goals
    apply Fin.ext
    simp only [ha', hb', if_true, if_false, Fin.val_ofNat] at he
    omega

lemma translate_cover : H2 := by
  classical
  intro x r D hr hfix hd hcover
  let pick (v : {v : {s : Finset (Fin 32) // s.card = 16} // x ∈ v.val}) :=
    (hcover v.val.val v.val.property v.property).choose
  have hpick (v : {v : {s : Finset (Fin 32) // s.card = 16} // x ∈ v.val}) :
      v.val.val.image (r (pick v)) ∈ D :=
    (hcover v.val.val v.val.property v.property).choose_spec
  refine ⟨SimpleGraph.Coloring.mk pick ?_⟩
  intro v w hvw he
  let f := r (pick v)
  have hfi : Function.Injective f := hr _
  let s := v.val.val ∩ w.val.val
  have hs : s.card + 1 = 16 := hvw
  have hxs : x ∈ s := mem_inter.mpr ⟨v.property, w.property⟩
  have hs' : (s.image f).card = 15 := by
    rw [card_image_of_injective _ hfi]
    omega
  have hxs' : x ∈ s.image f := mem_image.mpr ⟨x, hxs, hfix _⟩
  obtain ⟨a, ha, hA⟩ := OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.insert_repr
    (s := s) inter_subset_left (hs.trans v.val.property.symm)
  obtain ⟨b, hb, hB⟩ := OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.insert_repr
    (s := s) inter_subset_right (hs.trans w.val.property.symm)
  have missing (u : Fin 32) (hu : u ∉ s) : f u ∉ s.image f := by
    intro hm
    obtain ⟨t, ht, heq⟩ := mem_image.mp hm
    exact hu (hfi heq ▸ ht)
  have haD : insert (f a) (s.image f) ∈ D := by
    have h := hpick v
    change v.val.val.image f ∈ D at h
    rwa [hA, image_insert] at h
  have hbD : insert (f b) (s.image f) ∈ D := by
    have h := hpick w
    rw [← he] at h
    change w.val.val.image f ∈ D at h
    rwa [hB, image_insert] at h
  have hab := (hd (s.image f) hs' hxs').unique ⟨missing a ha, haD⟩ ⟨missing b hb, hbD⟩
  apply ha
  have heq := hfi hab
  exact mem_inter.mpr ⟨by rw [hA]; exact mem_insert_self _ _,
    by rw [hB, heq]; exact mem_insert_self _ _⟩

theorem main : H1 → H2 → OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1.H1 := by
  rintro ⟨D, hd, htrans⟩ h
  let rot := fun (i : Fin 17) (a : Fin 32) =>
    if a.val < 17 then Fin.ofNat 32 ((a.val + i.val) % 17) else a
  have color := h 31 rot D rot_injective (by intro i; rfl) hd
    (fun A hA hx => (htrans A hA hx).exists)
  have first : OMA.R_Erdos835_erdos_835_variants_johnson_R1.H1 :=
    ⟨16, 31, by decide, by decide, color⟩
  exact OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1.restrict_coloring
    (OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.restrict_coloring first)

end OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1_H1_R1_H1_R1
