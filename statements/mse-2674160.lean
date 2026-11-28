import Mathlib

/-!
# Is there an endofunctor of the category of sets that maps $\kappa$ to $\kappa^+$?

Source: https://math.stackexchange.com/questions/2674160/is-there-an-endofunctor-of-the-category-of-sets-that-maps-kappa-to-kappa
Credit: @mgv27

Is there an endofunctor of the category of sets which maps each infinite cardinal $\kappa$
to a set of size $\kappa^+$ (i.e., the first larger cardinality)? Under GCH the power set
functor works, since $2^\kappa = \kappa^+$. Is it always true under ZFC that there exists an
endofunctor of the category of sets that maps $\kappa$ to a set of size $\kappa^+$?

Formalization notes:
* The category of sets is modelled by `Type u` (with all functions as morphisms), and an
  endofunctor is a `CategoryTheory.Functor (Type u) (Type u)`.
* "Maps $\kappa$ to a set of size $\kappa^+$" is stated for every type `X` of infinite
  cardinality: `#(F.obj X) = Order.succ #X`. Since functors preserve isomorphisms
  (bijections), this only depends on `#X`, so it is the same as asking it for one
  representative of each infinite cardinal.
* Nothing is required on finite sets (the asker only asks about infinite cardinals).
* `main` is the natural "yes" reading (existence of such a functor), stated in Lean's
  foundations rather than literally "provable in ZFC". A ZFC proof would give a proof of
  `main`; the asker and commenters expect the answer may be independent (it holds under
  GCH), in which case `main` might also be unprovable here.
-/

namespace OMA.S_mse_2674160

open CategoryTheory

/-- `F` sends every infinite set `X` to a set of cardinality `|X|^+`. -/
def SendsToSucc (F : Functor (Type u) (Type u)) : Prop :=
  ∀ X : Type u, Cardinal.aleph0 ≤ Cardinal.mk X →
    Cardinal.mk (F.obj X) = Order.succ (Cardinal.mk X)

/-- Is there an endofunctor of the category of sets mapping each infinite `κ` to a set of
size `κ⁺`? -/
theorem main : ∃ F : Functor (Type u) (Type u), SendsToSucc F := by
  sorry

end OMA.S_mse_2674160
