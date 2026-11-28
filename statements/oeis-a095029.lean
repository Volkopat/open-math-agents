import Mathlib

/-!
# A095029: Prime Power Conjecture for Abelian planar difference sets.

Source: https://oeis.org/A095029
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A (v,k,lambda) cyclic difference set is a subset D={d1,d2,...,dk} of the integers
modulo v such that {1,2,...,v-1} can each be represented as a difference (di-d_j)
modulo v in exactly lambda different ways. Difference sets with lambda=1 (planar
difference sets) have order n=k-1. The Prime Power Conjecture states that all
Abelian planar difference sets have order n a prime power.
-/

namespace OMA.S_oeis_a095029

/-- `D` is a nontrivial planar difference set of order `n` in the finite abelian group `G`. -/
def IsPlanarDifferenceSet {G : Type} [AddCommGroup G] [Fintype G] (D : Finset G) (n : ℕ) : Prop :=
  2 ≤ n ∧ D.card = n + 1 ∧
    ∀ g : G, g ≠ 0 → ∃! p : G × G, p ∈ D ×ˢ D ∧ p.1 - p.2 = g

theorem main :
    ∀ (G : Type) [AddCommGroup G] [Fintype G] (D : Finset G) (n : ℕ),
      IsPlanarDifferenceSet D n → IsPrimePow n := by
  sorry

end OMA.S_oeis_a095029
