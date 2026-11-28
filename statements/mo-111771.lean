import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# A universal bound for automorphisms stabilizing a subgroup

Source: https://mathoverflow.net/questions/111771
Question by Igor Rivin, 2012-11-08 (CC BY-SA 3.0).
The binomial bound was already noted in Will Sawin's source comment.
This formalizes that elementary bound, with no claim of optimality.
Credit: @etaubman

The question asks for an explicit universal upper bound, in terms of k and l,
for the index in Aut(G) of the automorphisms preserving a subgroup H, where
|H| = k and |G| = k*l. The stabilizer acts on H as a set, exactly encoding
phi(H) = H. We read H < G as a proper subgroup. The proof also covers H = G.
-/

open scoped Pointwise

universe u

namespace OMA.S_mo_111771

theorem main : ∃ B : ℕ → ℕ → ℕ,
    ∀ (G : Type u) [Group G] [Finite G] (H : Subgroup G) (k l : ℕ),
      H < ⊤ → Nat.card H = k → Nat.card G = k * l →
        (MulAction.stabilizer (MulAut G) (H : Set G)).index ≤ B k l := by
  sorry

end OMA.S_mo_111771
