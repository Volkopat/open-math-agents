import Mathlib

/-!
# Automorphisms of order 2 in finite groups with no elements of order $p^2$

Source: https://mathoverflow.net/questions/266649
Credit: @ivillar

Status: false as stated. The cyclic group of order 6 is a counterexample (pointed out in the
comments to the question): it has no element of order `p ^ 2`, its order is not a prime, and
every automorphism of a cyclic group maps every subgroup onto itself. The statement is kept as
the target of a disproof.

Let $G$ be a finite group with no element of order $p^2$ for each prime $p$. Also, suppose that
$\vert G\vert\neq p$, for each prime $p$. Does there always exist an automorphism $\phi$ of
order 2 such that for at least one subgroup of $G$, say $H$, we have $\phi(H)\neq H$?

Formalization notes:
* `φ` is an element of order `2` of the automorphism group `MulAut G`, and `φ(H)` is the image
  subgroup `H.map φ`.
* The follow-up in the question ("what if we add the supposition that `G` is not cyclic?") is
  not part of this statement.
-/

namespace OMA.S_mo_266649

theorem main : ∀ (G : Type) [Group G] [Finite G],
    (∀ p : ℕ, p.Prime → ∀ g : G, orderOf g ≠ p ^ 2) →
    (∀ p : ℕ, p.Prime → Nat.card G ≠ p) →
    ∃ φ : MulAut G, orderOf φ = 2 ∧ ∃ H : Subgroup G, H.map φ.toMonoidHom ≠ H := by
  sorry

end OMA.S_mo_266649
