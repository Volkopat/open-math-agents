import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a245024

/-- Membership predicate for OEIS A245024: even `n ≥ 4` with `lpf(n - 1) < lpf(n - 3)`. -/
def isTerm (n : ℕ) : Prop :=
  4 ≤ n ∧ Even n ∧ (n - 1).minFac < (n - 3).minFac

/-- The `i`-th term (0-indexed: `a 0 = 10, a 1 = 16, a 2 = 22, ...`) of OEIS A245024. -/
noncomputable def a (i : ℕ) : ℕ :=
  Nat.nth isTerm i

/-- The `i`-th first difference `a (i + 1) - a i`. -/
noncomputable def d (i : ℕ) : ℕ :=
  a (i + 1) - a i

/-- OEIS A245024 conjecture (Vladimir Shevelev & Peter J. C. Moses, Jul 2014):
All first differences of A245024 are `2`, `4`, or `6`; no two consecutive differences are `2`;
no two consecutive differences are `4`; consecutive differences `6` occur in maximal runs of
length `1`, `2`, `3`, or `4` (never `≥ 5`, and all four lengths `1, 2, 3, 4` occur); and
consecutive pairs `(4, 2)` occur in maximal runs of length `1`, `2`, `3`, or `4` (never `≥ 5`,
and all four lengths `1, 2, 3, 4` occur). -/
theorem main :
    (∀ i, d i = 2 ∨ d i = 4 ∨ d i = 6) ∧
    (∀ i, ¬ (d i = 2 ∧ d (i + 1) = 2)) ∧
    (∀ i, ¬ (d i = 4 ∧ d (i + 1) = 4)) ∧
    (∀ i, ¬ (∀ j < 5, d (i + j) = 6)) ∧
    (∀ k ∈ ({1, 2, 3, 4} : Set ℕ),
      ∃ i, (i = 0 ∨ d (i - 1) ≠ 6) ∧ (∀ j < k, d (i + j) = 6) ∧ d (i + k) ≠ 6) ∧
    (∀ i, ¬ (∀ j < 5, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2)) ∧
    (∀ k ∈ ({1, 2, 3, 4} : Set ℕ),
      ∃ i, (i < 2 ∨ ¬ (d (i - 2) = 4 ∧ d (i - 1) = 2)) ∧
        (∀ j < k, d (i + 2 * j) = 4 ∧ d (i + 2 * j + 1) = 2) ∧
        ¬ (d (i + 2 * k) = 4 ∧ d (i + 2 * k + 1) = 2)) := by
  sorry

end OMA.S_oeis_a245024
