import Mathlib

/-!
# The large sets conjecture

Source: https://www.openproblemgarden.org/op/the_large_sets_conjecture
Credit: @ishaanzee

For `r ∈ ℕ`, a set of positive integers `L` is said to be `r`-large if for any `r`-coloring `f`
of the positive integers there are arbitrarily long `f`-monochromatic arithmetic progressions
whose common differences belong to `L`. Then `L` is large if and only if it is `r`-large for all
`r`.

**Conjecture** (T. C. Brown, R. L. Graham, B. M. Landman). If `A` is 2-large, then `A` is large.

Formalization: `L : Set ℕ` with all elements positive; an `r`-coloring of the positive integers is
`f : ℕ → Fin r` (its value at `0` is irrelevant). Arbitrarily long monochromatic progressions:
for every `m` there are `a ≥ 1` and `d ∈ L` with `f (a + i d) = f a` for all `i < m`. "Large" is
`r`-large for every `r ≥ 1` (for `r = 0` there is no coloring).
-/

namespace OMA.S_opg_the_large_sets_conjecture

/-- `L` is `r`-large: every `r`-coloring of the positive integers has arbitrarily long
monochromatic arithmetic progressions with common difference in `L`. -/
def IsLarge (L : Set ℕ) (r : ℕ) : Prop :=
  ∀ (f : ℕ → Fin r) (m : ℕ), ∃ a d : ℕ, 0 < a ∧ d ∈ L ∧ ∀ i < m, f (a + i * d) = f a

/-- **Large sets conjecture**: a 2-large set of positive integers is `r`-large for every `r`. -/
theorem main : ∀ L : Set ℕ, (∀ d ∈ L, 0 < d) → IsLarge L 2 → ∀ r : ℕ, 0 < r → IsLarge L r := by
  sorry

end OMA.S_opg_the_large_sets_conjecture
