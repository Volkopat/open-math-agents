import Mathlib

/-!
# Does a signed pentagon commutator identity characterize 3-Engel groups?

This is the concrete identity question in https://mathoverflow.net/questions/266492.
The signs may be chosen independently, once for all groups. The other questions
in the post concern nilpotence of the variety defined by a pentagon identity.
Credit: @witeg4
-/

namespace OMA.S_mo_266492

def bracket {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

def engelThree (G : Type*) [Group G] : Prop :=
  ∀ x y : G, bracket (bracket (bracket x y) y) y = 1

def signed {G : Type*} [Group G] (negate : Bool) (g : G) : G :=
  if negate then g⁻¹ else g

def pentagon {G : Type*} [Group G] (s : Fin 5 → Bool) (x y z w : G) : G :=
  signed (s 0) (bracket (bracket (bracket x y) z) w) *
  signed (s 1) (bracket (bracket x (bracket y z)) w) *
  signed (s 2) (bracket x (bracket (bracket y z) w)) *
  signed (s 3) (bracket x (bracket y (bracket z w))) *
  signed (s 4) (bracket (bracket x y) (bracket z w))

theorem main : ∃ s : Fin 5 → Bool, ∀ (G : Type) [Group G],
    engelThree G ↔ ∀ x y z w : G, pentagon s x y z w = 1 := by
  sorry

end OMA.S_mo_266492
