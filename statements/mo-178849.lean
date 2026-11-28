import Mathlib

/-!
# Kaplansky idempotents in an extension of torsion-free groups

Source: https://mathoverflow.net/questions/178849 (Ali Taghavi, CC BY-SA)
Credit: @my-other-github-account

The question concerns the idempotent conjecture for complex group algebras.
A short exact sequence `1 → N → G → Q → 1` is an injective homomorphism `i`,
a surjective homomorphism `p` and the exactness condition `range i = ker p`.
Given torsion-free `N` and `Q` whose complex group algebras have only the
trivial idempotents, it asks whether the same holds for `G`; the second
conjunct is the semidirect-product case. The optional C*-algebraic Kadison
question mentioned in parentheses is not stated here.
-/

namespace OMA.S_mo_178849

/-- The only element of finite order is the identity. -/
def TorsionFree (G : Type*) [Group G] : Prop :=
  ∀ g : G, IsOfFinOrder g → g = 1

/-- `ℂ[G]` has no idempotents other than `0` and `1`. -/
def HasOnlyTrivialIdempotents (G : Type*) [Group G] : Prop :=
  ∀ e : MonoidAlgebra ℂ G, IsIdempotentElem e → e = 0 ∨ e = 1

theorem main :
    (∀ (N G Q : Type) [Group N] [Group G] [Group Q] (i : N →* G) (p : G →* Q),
      Function.Injective i → Function.Surjective p → i.range = p.ker →
      TorsionFree N → TorsionFree Q →
      HasOnlyTrivialIdempotents N → HasOnlyTrivialIdempotents Q →
      HasOnlyTrivialIdempotents G) ∧
    (∀ (N H : Type) [Group N] [Group H] (φ : H →* MulAut N),
      TorsionFree N → TorsionFree H →
      HasOnlyTrivialIdempotents N → HasOnlyTrivialIdempotents H →
      HasOnlyTrivialIdempotents (N ⋊[φ] H)) := by
  sorry

end OMA.S_mo_178849
