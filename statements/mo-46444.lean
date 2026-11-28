import Mathlib

/-!
# No `n > 1` has exactly `n` groups of order `n`

Source: https://mathoverflow.net/questions/46444/natural-numbers-n-which-satisfy-gnun-n
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`gnu(n)` is the number of isomorphism classes of groups of order `n`. Question: is there
`n > 1` with `gnu(n) = n`? Conjecture 10.1 of Conway–Dietrich–O'Brien implies there is none;
`main` states that no such `n` exists.

Convention: `gnu(n) = k` is spelled out as: there are groups `G 0, …, G (k-1)` of order `n`,
pairwise non-isomorphic, such that every group of order `n` is isomorphic to one of them.
-/

namespace OMA.S_mo_46444

/-- There are exactly `k` isomorphism classes of groups of order `n`. -/
def HasGnu (n k : ℕ) : Prop :=
  ∃ (G : Fin k → Type) (_ : ∀ i, Group (G i)),
    (∀ i, Nat.card (G i) = n) ∧
    (∀ i j, Nonempty (G i ≃* G j) → i = j) ∧
    ∀ (H : Type) [Group H], Nat.card H = n → ∃ i, Nonempty (H ≃* G i)

theorem main : ∀ n : ℕ, 1 < n → ¬ HasGnu n n := by
  sorry

end OMA.S_mo_46444
