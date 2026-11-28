import Mathlib

/-!
# A282504: Expansion of 1/(1 - Sum_{k>=0} x^(2*k*(k+1)+1)).

Source: https://oeis.org/A282504
Credit: @luciusacarr

a(n) is the number of compositions (ordered partitions) of n into centered square numbers
(A001844: 1, 5, 13, 25, 41, ...).

The entry's comments record two conjectures. `main` states both, as a conjunction, in the order
the source gives them.

Conjecture: every number > 1 is the sum of at most 6 centered square numbers.
Extended conjecture: every number > 1 is the sum of at most k+2 centered k-gonal numbers.

Reading of the source:
* The centered k-gonal numbers are `k * m(m+1)/2 + 1` for `m ≥ 0`; for k = 4 these are the
  centered square numbers `2m(m+1) + 1`. Polygons have `k ≥ 3` sides, so the extended conjecture
  is stated for every `k ≥ 3`.
* "Sum of at most j" means a sum of `i ≤ j` such numbers, repetitions allowed (the summands are
  indexed by `Fin i`).
* The first conjecture was checked numerically for every n from 2 to 20000.

Note: a sum of `i` centered k-gonal numbers is `i + k * (sum of i triangular numbers)`, so both
claims appear to follow from Gauss's Eureka theorem (every natural number is a sum of three
triangular numbers) by choosing `i` in `{3, ..., k + 2}` according to `n mod k` (or `i = n` when
`n ≤ k + 2`). They are stated here as the entry states them.
-/

namespace OMA.S_oeis_a282504

/-- `m` is a centered square number (A001844). -/
def IsCenteredSquare (m : ℕ) : Prop := ∃ t : ℕ, m = 2 * t * (t + 1) + 1

/-- `m` is a centered `k`-gonal number. -/
def IsCenteredPolygonal (k m : ℕ) : Prop := ∃ t : ℕ, m = k * (t * (t + 1) / 2) + 1

theorem main :
    -- Every number > 1 is the sum of at most 6 centered square numbers.
    (∀ n : ℕ, 1 < n → ∃ (i : ℕ) (b : Fin i → ℕ), i ≤ 6 ∧
      (∀ r, IsCenteredSquare (b r)) ∧ ∑ r, b r = n) ∧
    -- Extended: for k ≥ 3, every number > 1 is the sum of at most k + 2 centered k-gonal numbers.
    (∀ k : ℕ, 3 ≤ k → ∀ n : ℕ, 1 < n → ∃ (i : ℕ) (b : Fin i → ℕ), i ≤ k + 2 ∧
      (∀ r, IsCenteredPolygonal k (b r)) ∧ ∑ r, b r = n) := by
  sorry

end OMA.S_oeis_a282504
