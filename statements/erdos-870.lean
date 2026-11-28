import Mathlib

/-!
# Erdős Problem 870

Source: https://www.erdosproblems.com/870
Credit: @shc261392

The source: let `k ≥ 3` and `A` be an additive basis of order `k`. Does there exist a constant
`c = c(k) > 0` such that if `r(n) ≥ c log n` for all large `n` then `A` must contain a minimal
basis of order `k`? (Here `r(n)` counts the number of representations of `n` as the sum of at
most `k` elements from `A`.)

The source records that Erdős and Nathanson proved this for `k = 2` (with the constant
`(log (4/3))⁻¹`). This file states the question in its affirmative form: a proof of `main`
answers it yes, a proof of `¬ main` answers it no.

Reading used here:
* `A ⊆ ℕ`. An additive basis of order `k` is a set such that every sufficiently large integer is
  the sum of at most `k` elements of `A` (repetitions allowed), as in the source's `r(n)`.
* A minimal basis of order `k` is a basis `B` of order `k` such that `B \ {b}` is not a basis of
  order `k` for any `b ∈ B`.
* `r(n)` counts representations as multisets of at most `k` elements of `A` summing to `n`
  (summands in any order counted once). Counting ordered tuples instead changes `r(n)` by at most a
  factor `k!`, which the existential constant `c` absorbs, so the statement does not depend on
  this choice.
-/

namespace OMA.S_erdos_870

open Filter

/-- Every sufficiently large integer is the sum of at most `k` elements of `A`. -/
def IsBasisOfOrder (A : Set ℕ) (k : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∃ s : Multiset ℕ, Multiset.card s ≤ k ∧ (∀ a ∈ s, a ∈ A) ∧ s.sum = n

/-- `B` is a basis of order `k` and no set `B \ {b}` with `b ∈ B` is one. -/
def IsMinimalBasisOfOrder (B : Set ℕ) (k : ℕ) : Prop :=
  IsBasisOfOrder B k ∧ ∀ b ∈ B, ¬ IsBasisOfOrder (B \ {b}) k

/-- The number of representations of `n` as a sum of at most `k` elements of `A`. -/
noncomputable def r (A : Set ℕ) (k n : ℕ) : ℕ :=
  Set.ncard {s : Multiset ℕ | Multiset.card s ≤ k ∧ (∀ a ∈ s, a ∈ A) ∧ s.sum = n}

theorem main :
    ∀ k : ℕ, 3 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ A : Set ℕ, IsBasisOfOrder A k →
      (∀ᶠ n : ℕ in atTop, c * Real.log n ≤ r A k n) →
        ∃ B ⊆ A, IsMinimalBasisOfOrder B k := by
  sorry

end OMA.S_erdos_870
