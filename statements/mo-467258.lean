import Mathlib

/-!
# The Non-Cancelling Intersections Conjecture

Source: Mikaël Monet, https://mathoverflow.net/questions/467258
Original formulation: Amarilli, Monet and Suciu, https://arxiv.org/abs/2401.16210
Credit: @wtho704

The family is nonempty, and any two distinct members are incomparable by
inclusion. Non-cancellation means that the sum of the signed coefficients
of all index sets yielding the same intersection is nonzero.

Wilhelm reports counterexamples in https://arxiv.org/abs/2608.27416.
-/

namespace OMA.S_mo_467258

universe u

/-- The intersection of a nonempty subfamily, taken inside the full union. -/
def intersection {α : Type u} [DecidableEq α] {n : ℕ}
    (S : Fin n → Finset α) (indices : Finset (Fin n)) : Finset α :=
  (Finset.univ.biUnion S).filter (fun x => ∀ i ∈ indices, x ∈ S i)

/-- The coefficient of a set after collecting equal intersections. -/
def coefficient {α : Type u} [DecidableEq α] {n : ℕ}
    (S : Fin n → Finset α) (A : Finset α) : ℤ :=
  ∑ indices ∈ (Finset.univ : Finset (Fin n)).powerset,
    if indices.Nonempty ∧ intersection S indices = A then (-1 : ℤ) ^ (indices.card + 1)
    else 0

/-- A finite expression using the available sets and the two partial operations. -/
inductive Buildable {α : Type u} [DecidableEq α] (available : Finset α → Prop) :
    Finset α → Prop where
  | base {A : Finset α} : available A → Buildable available A
  | disjointUnion {A B : Finset α} :
      Buildable available A → Buildable available B → Disjoint A B →
      Buildable available (A ∪ B)
  | subsetComplement {A B : Finset α} :
      Buildable available A → Buildable available B → B ⊆ A →
      Buildable available (A \ B)

theorem main :
    ∀ (α : Type u) [DecidableEq α] (n : ℕ), 0 < n → ∀ S : Fin n → Finset α,
      (∀ i j, i ≠ j → ¬ S i ⊆ S j) →
      Buildable (fun A => coefficient S A ≠ 0) (Finset.univ.biUnion S) := by
  sorry

end OMA.S_mo_467258
