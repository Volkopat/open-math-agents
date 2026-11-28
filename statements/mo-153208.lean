import Mathlib

/-!
# MathOverflow 153208: is the poset of graphs automorphism-free?

Source: https://mathoverflow.net/questions/153208 (CC BY-SA 3.0).

For `n ≥ 5` let `𝒫ₙ` be the set of isomorphism classes of (simple) graphs with `n` vertices,
ordered by `G ≤ H` iff `G` is a subgraph of `H`. Question: is it true that `𝒫ₙ` has no
nontrivial automorphisms? `main` states the affirmative.

Conventions: graphs on `n` vertices are `SimpleGraph (Fin n)`. Since both graphs have `n`
vertices, "`G` is (isomorphic to) a subgraph of `H`" means there is an injective graph
homomorphism `G →g H` (`Sub G H`). `Sub` is a preorder whose induced equivalence is graph
isomorphism (on finitely many vertices, injective homomorphisms both ways force equal edge
counts), so its quotient is `𝒫ₙ` with the subgraph order. We avoid the quotient: an
automorphism of `𝒫ₙ` is the same as a map `φ` on graphs that preserves and reflects `Sub` and
hits every isomorphism class (any automorphism lifts to such a `φ` by choosing representatives,
and any such `φ` descends to an automorphism), and it is trivial iff `φ G ≃g G` for all `G`.
-/

namespace OMA.S_mo_153208

/-- `G` is isomorphic to a subgraph of `H` (both on `Fin n`). -/
def Sub {n : ℕ} (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ f : G →g H, Function.Injective f

theorem main : ∀ n : ℕ, 5 ≤ n → ∀ φ : SimpleGraph (Fin n) → SimpleGraph (Fin n),
    (∀ G H : SimpleGraph (Fin n), Sub G H ↔ Sub (φ G) (φ H)) →
    (∀ H : SimpleGraph (Fin n), ∃ G, Nonempty (φ G ≃g H)) →
    ∀ G : SimpleGraph (Fin n), Nonempty (φ G ≃g G) := by
  sorry

end OMA.S_mo_153208
