import OMAStatements.S_oeis_a264515
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Set

/-!
We reuse the disjoint-union argument from our A264273 proof (signed revision
4e2f136543f3d67c8099c46d9cfdb3b2856a4ff6). Each of the two column parities
becomes the directed board defining A264507 after exchanging the axes and
reflecting the long coordinate.
-/

namespace OMA.PermBlocks

variable {V W α β : Type*}

def Legal (R : V → V → Prop) := {σ : Equiv.Perm V // ∀ x, R x (σ x)}

def sumRel (R : α → α → Prop) (S : β → β → Prop) : α ⊕ β → α ⊕ β → Prop
  | .inl a, .inl b => R a b
  | .inr a, .inr b => S a b
  | _, _ => False

def transport (e : V ≃ W) (R : V → V → Prop) (S : W → W → Prop)
    (h : ∀ x y, R x y ↔ S (e x) (e y)) : Legal R ≃ Legal S :=
  e.permCongr.subtypeEquiv (fun σ => by
    constructor
    · intro hσ w
      simpa using (h (e.symm w) (σ (e.symm w))).mp (hσ (e.symm w))
    · intro hσ x
      apply (h x (σ x)).mpr
      simpa using hσ (e x))

theorem card_transport (e : V ≃ W) (R : V → V → Prop) (S : W → W → Prop)
    (h : ∀ x y, R x y ↔ S (e x) (e y)) : Nat.card (Legal R) = Nat.card (Legal S) :=
  Nat.card_congr (transport e R S h)

noncomputable def split (R : α → α → Prop) (S : β → β → Prop) :
    Legal (sumRel R S) ≃ (Legal R × Legal S) := by
  let join : Legal R × Legal S → Legal (sumRel R S) := fun p =>
    ⟨Equiv.sumCongr p.1.val p.2.val, fun x => by cases x with
      | inl x => exact p.1.property x
      | inr x => exact p.2.property x⟩
  have hinj : Function.Injective join := by
    intro p q h
    have hval := congrArg Subtype.val h
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro a
      exact Sum.inl_injective (β := β) (congrArg (fun σ : Equiv.Perm (α ⊕ β) => σ (.inl a)) hval)
    · apply Subtype.ext
      apply Equiv.ext
      intro b
      exact Sum.inr_injective (α := α) (congrArg (fun σ : Equiv.Perm (α ⊕ β) => σ (.inr b)) hval)
  have hsurj : Function.Surjective join := by
    intro p
    have hl (x : α) : ∃ y : α, p.val (.inl x) = .inl y ∧ R x y := by
      have hr := p.property (.inl x)
      cases hh : p.val (.inl x) with
      | inl y => exact ⟨y, rfl, by simpa [hh, sumRel] using hr⟩
      | inr y => simp [hh, sumRel] at hr
    have hr (x : β) : ∃ y : β, p.val (.inr x) = .inr y ∧ S x y := by
      have ht := p.property (.inr x)
      cases hh : p.val (.inr x) with
      | inr y => exact ⟨y, rfl, by simpa [hh, sumRel] using ht⟩
      | inl y => simp [hh, sumRel] at ht
    let f := fun a => (hl a).choose
    let g := fun b => (hr b).choose
    have hm : Sum.map f g = (p.val : α ⊕ β → α ⊕ β) := by
      funext x
      cases x with
      | inl a => exact (hl a).choose_spec.1.symm
      | inr b => exact (hr b).choose_spec.1.symm
    have hfg := Sum.map_bijective.mp (hm.symm ▸ p.val.bijective)
    refine ⟨(⟨Equiv.ofBijective f hfg.1, fun a => (hl a).choose_spec.2⟩,
      ⟨Equiv.ofBijective g hfg.2, fun b => (hr b).choose_spec.2⟩), ?_⟩
    apply Subtype.ext
    apply Equiv.ext
    exact congrFun hm
  exact (Equiv.ofBijective join ⟨hinj, hsurj⟩).symm

theorem card_split (R : α → α → Prop) (S : β → β → Prop) :
    Nat.card (Legal (sumRel R S)) = Nat.card (Legal R) * Nat.card (Legal S) :=
  (Nat.card_congr (split R S)).trans (Nat.card_prod _ _)

theorem card_transport_split (e : V ≃ α ⊕ β) (T : V → V → Prop)
    (R : α → α → Prop) (S : β → β → Prop)
    (h : ∀ x y, T x y ↔ sumRel R S (e x) (e y)) :
    Nat.card (Legal T) = Nat.card (Legal R) * Nat.card (Legal S) :=
  (card_transport e T (sumRel R S) h).trans (card_split R S)

end OMA.PermBlocks

namespace OMA.S_oeis_a264515

private def classify {n : ℕ} (u : Wide n) : Narrow n ⊕ Narrow n :=
  let v : Narrow n := (⟨u.2.val / 2, by have := u.2.isLt; omega⟩, u.1.rev)
  if u.2.val % 2 = 0 then .inl v else .inr v

private def restore {n : ℕ} : Narrow n ⊕ Narrow n → Wide n
  | .inl (j, k) => (k.rev, ⟨2 * j.val, by have := j.isLt; omega⟩)
  | .inr (j, k) => (k.rev, ⟨2 * j.val + 1, by have := j.isLt; omega⟩)

/-- The column parity picks a component. Its coordinates are the half-column
and the reflected original row. -/
private def boards (n : ℕ) : Wide n ≃ Narrow n ⊕ Narrow n where
  toFun := classify
  invFun := restore
  left_inv := by
    rintro ⟨i, c⟩
    by_cases hc : c.val % 2 = 0 <;> simp [classify, restore, hc, Fin.ext_iff] <;> omega
  right_inv := by
    rintro (⟨j, k⟩ | ⟨j, k⟩)
    · have h : (2 * j.val) % 2 = 0 := by omega
      simp [classify, restore, h]
    · simp [classify, restore, Fin.ext_iff]
      omega

private theorem boards_move (n : ℕ) (u v : Wide n) :
    wideMove u v ↔ OMA.PermBlocks.sumRel narrowMove narrowMove (boards n u) (boards n v) := by
  rcases u with ⟨i, c⟩
  rcases v with ⟨j, d⟩
  have hi := i.isLt
  have hj := j.isLt
  by_cases hc : c.val % 2 = 0 <;> by_cases hd : d.val % 2 = 0 <;>
    simp [boards, classify, hc, hd, OMA.PermBlocks.sumRel, wideMove, narrowMove] <;> omega

end OMA.S_oeis_a264515

open OMA.S_oeis_a264515 in
theorem OMA.solution : type_of% @OMA.S_oeis_a264515.main := by
  intro n _
  simpa only [a515, a507, pow_two, OMA.PermBlocks.Legal] using
    OMA.PermBlocks.card_transport_split (boards n) wideMove narrowMove narrowMove (boards_move n)
