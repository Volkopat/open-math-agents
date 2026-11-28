import FormalConjectures.Wikipedia.Jacobson
import Mathlib

-- Reduction Jacobson.jacobson_conjecture.R1 of Jacobson's conjecture for Noetherian rings.
-- Credit: @marcusbuffett

/-!
# Jacobson's conjecture: the classical cases, and the open rest

The conjecture: in a left and right Noetherian ring `R`, `⋂ₙ J(R)ⁿ = 0`.

* `H1` (classical): the conjecture holds when `R` is commutative (Krull's intersection
  theorem, 1938) or semiprimary (its Jacobson radical is nilpotent and `R / J(R)` is
  semisimple; this includes every left Artinian ring, by Hopkins–Levitzki).
* `H2` (open): the conjecture for left and right Noetherian rings that are neither
  commutative nor semiprimary.

`main` is a case split. This isolates the textbook cases; it is not progress on the
noncommutative conjecture, which `H2` keeps in full.
-/

namespace OMA.R_Jacobson_jacobson_conjecture_R1

/-- Krull and semiprimary cases: commutative or semiprimary Noetherian rings satisfy
Jacobson's conjecture. -/
def H1 : Prop :=
  ∀ (R : Type) [Ring R] [IsNoetherianRing R] [IsRightNoetherianRing R],
    ((∀ x y : R, x * y = y * x) ∨ IsSemiprimaryRing R) → Jacobson.JacobsonConjectureFor R

/-- The open part: noncommutative, non-semiprimary left and right Noetherian rings. -/
def H2 : Prop :=
  ∀ (R : Type) [Ring R] [IsNoetherianRing R] [IsRightNoetherianRing R],
    ¬ (∀ x y : R, x * y = y * x) → ¬ IsSemiprimaryRing R → Jacobson.JacobsonConjectureFor R

theorem main : H1 → H2 → type_of% @Jacobson.jacobson_conjecture := by
  intro h1 h2 R _ _ _
  by_cases hc : ∀ x y : R, x * y = y * x
  · exact h1 R (Or.inl hc)
  by_cases hs : IsSemiprimaryRing R
  · exact h1 R (Or.inr hs)
  exact h2 R hc hs

end OMA.R_Jacobson_jacobson_conjecture_R1
