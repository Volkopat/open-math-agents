import Mathlib

/-!
# A183978: 1/4 the number of (n+1) X 2 binary arrays with all 2 X 2 subblock sums the same.

Source: https://oeis.org/A183978
Credit: @ceejcake

Entry (R. H. Hardin), offset 1, data 4, 6, 9, 15, 25, 45, 81, 153, 289, 561, ...
Formula section: Based on the conjectured recursion formula, we may prove (by a tedious
induction) that a(n) = (2^ceiling(n/2) + 1) * (2^floor(n/2) + 1) = A051032(n) * A051032(n-1)
for n >= 1. - Philippe Gibone, Jul 06 2016, corrected by Robert Israel, May 21 2019.

Formalization notes:
* An (n+1) X 2 binary array is a function `Fin (n + 1) → Fin 2 → Bool` (row, column). Its
  2 X 2 subblocks are the ones with top-left corner `(i, 0)` for `i : Fin n`. The sequence is
  defined from this count (divided by 4), not from any formula.
* `main` states the listed formula a(n) = (2^ceiling(n/2) + 1) * (2^floor(n/2) + 1) for every
  n >= 1, exactly in the listed form, with ceiling and floor taken of the rational number n/2.
  The second equality of the entry (a cross reference to A051032) is not part of the claim.
* As written, this formula is false: at n = 1 every 2 X 2 binary array qualifies (there is a
  single subblock), so a(1) = 16/4 = 4, while the formula gives (2^1 + 1) * (2^0 + 1) = 6.
  The right-hand side matches the data shifted by one index, that is, it equals a(n + 1)
  (6, 9, 15, 25, ...). The statement keeps the listed form and range anyway.
-/

namespace OMA.S_oeis_a183978

/-- The sum of the `2 × 2` subblock of a binary array `A : Fin (n + 1) → Fin 2 → Bool`
with top-left corner `(i, j)`. -/
def subblockSum {n : ℕ} (A : Fin (n + 1) → Fin 2 → Bool) (i : Fin n) (j : Fin 1) : ℕ :=
  (A i.castSucc j.castSucc).toNat + (A i.castSucc j.succ).toNat +
  (A i.succ j.castSucc).toNat + (A i.succ j.succ).toNat

/-- A binary array `A : Fin (n + 1) → Fin 2 → Bool` is valid if all of its `2 × 2`
subblocks have the same sum. -/
def isValid (n : ℕ) (A : Fin (n + 1) → Fin 2 → Bool) : Prop :=
  ∃ s : ℕ, ∀ (i : Fin n) (j : Fin 1), subblockSum A i j = s

/-- `a n` is `1/4` the number of `(n + 1) × 2` binary arrays with all `2 × 2`
subblock sums equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 2 → Bool // isValid n A} / 4

/-- Gibone's formula for OEIS A183978, as listed, for all `n ≥ 1`
(false as written: it fails at `n = 1`, see the notes above). -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = (2 ^ ⌈(n : ℚ) / 2⌉₊ + 1) * (2 ^ ⌊(n : ℚ) / 2⌋₊ + 1) := by
  sorry

end OMA.S_oeis_a183978
