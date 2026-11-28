import OMAStatements.S_oeis_a071536

/-!
There are two objects, with an involution at each. There are four arrows
from source to target. The source involution interchanges the first pair
and fixes the second. The target involution fixes the first pair and
interchanges the second.

In an associative extension, multiply an arrow fixed on the left by an
arrow fixed on the right. The product would be fixed on both sides.
No arrow in this category has both properties.
-/

namespace EightArrowCategory

open CategoryTheory OMA.S_oeis_a071536

private inductive Point | source | target
open Point

private def Hom : Point → Point → Type
  | source, source => Bool
  | target, target => Bool
  | source, target => Sum Bool Bool
  | target, source => Empty

private def identity : (X : Point) → Hom X X
  | source | target => false

private def compose : {X Y Z : Point} → Hom X Y → Hom Y Z → Hom X Z
  | source, source, source, a, b => xor a b
  | target, target, target, a, b => xor a b
  | source, source, target, a, .inl i => .inl (xor a i)
  | source, source, target, _, .inr i => .inr i
  | source, target, target, .inl i, _ => .inl i
  | source, target, target, .inr i, b => .inr (xor i b)
  | source, target, source, _, h => nomatch h
  | target, source, _, h, _ => nomatch h
  | target, target, source, _, h => nomatch h

private instance : SmallCategory Point where
  Hom := Hom
  id := identity
  comp := @compose
  id_comp := by
    intro X Y f
    cases X <;> cases Y <;> cases f <;> first | rfl | rename_i i; cases i <;> rfl
  comp_id := by
    intro X Y f
    cases X <;> cases Y <;> cases f <;> first | rfl | rename_i i; cases i <;> rfl
  assoc := by
    intro X Y Z W f g h
    cases X <;> cases Y <;> cases Z <;> cases W <;> cases f <;> cases g <;> cases h <;>
      first | rfl | rename_i i; cases i <;> rfl

private abbrev atSource (i : Bool) : Arr Point := ⟨source, source, i⟩
private abbrev atTarget (i : Bool) : Arr Point := ⟨target, target, i⟩
private abbrev across (i : Sum Bool Bool) : Arr Point := ⟨source, target, i⟩

theorem impossible : ¬ (type_of% @OMA.S_oeis_a071536.main) := by
  intro extension
  obtain ⟨mul, assoc, agrees⟩ := extension Point
  let u := across (.inl false)
  let v := across (.inr false)
  have hu : mul (atTarget true) u = u := agrees source target target (.inl false) true
  have hv : mul v (atSource true) = v := agrees source source target true (.inr false)
  have hl : mul (atTarget true) (mul u v) = mul u v := by rw [← assoc, hu]
  have hr : mul (mul u v) (atSource true) = mul u v := by rw [assoc, hv]
  have no_fixed (z : Arr Point) (left : mul (atTarget true) z = z)
      (right : mul z (atSource true) = z) : False := by
    obtain ⟨X, Y, f⟩ := z
    cases X <;> cases Y
    · rw [agrees source source source true f] at right
      change Bool at f
      cases f <;> cases right
    · change Sum Bool Bool at f
      cases f with
      | inl i =>
        rw [agrees source source target true (.inl i)] at right
        cases i <;> cases right
      | inr i =>
        rw [agrees source target target (.inr i) true] at left
        cases i <;> cases left
    · exact nomatch f
    · rw [agrees target target target f true] at left
      change Bool at f
      cases f <;> cases left
  exact no_fixed (mul u v) hl hr

end EightArrowCategory

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a071536.main) :=
  EightArrowCategory.impossible
