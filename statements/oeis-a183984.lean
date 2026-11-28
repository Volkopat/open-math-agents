import Mathlib

/-!
# OEIS A183984

A183984: `1/4` the number of `(n + 1) × 8` binary arrays with all `2 × 2` subblock
sums the same.

Conjectures from Colin Barker (Apr 09 2018):
- `a(n) = 3 * 2^(n/2 - 1) + 2^(n - 1) + 78` for `n` even (`n ≥ 2`),
- `a(n) = 2^(n - 1) + 2^((n + 1)/2) + 78` for `n` odd (`n ≥ 1`).

Note: OEIS A183984 has offset 1 and data
`81, 83, 86, 92, 102, 122, 158, 230, 366, 638, ...`.

Reference: https://oeis.org/A183984
-/

namespace OMA.S_oeis_a183984

/-- The sum of the `2 × 2` subblock of a binary array `A : Fin (n + 1) → Fin 8 → Bool`
with top-left corner `(i, j)`. -/
def subblockSum {n : ℕ} (A : Fin (n + 1) → Fin 8 → Bool) (i : Fin n) (j : Fin 7) : ℕ :=
  (A i.castSucc j.castSucc).toNat + (A i.castSucc j.succ).toNat +
  (A i.succ j.castSucc).toNat + (A i.succ j.succ).toNat

/-- A binary array `A : Fin (n + 1) → Fin 8 → Bool` is valid if all of its `2 × 2`
subblocks have the same sum. -/
def isValid (n : ℕ) (A : Fin (n + 1) → Fin 8 → Bool) : Prop :=
  ∃ s : ℕ, ∀ (i : Fin n) (j : Fin 7), subblockSum A i j = s

/-- `a n` is `1/4` the number of `(n + 1) × 8` binary arrays with all `2 × 2`
subblock sums equal. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 8 → Bool // isValid n A} / 4

/-- Colin Barker's closed-form conjectures for OEIS A183984 (for even and odd `n ≥ 1`). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → a n = 3 * 2 ^ (n / 2 - 1) + 2 ^ (n - 1) + 78) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → a n = 2 ^ (n - 1) + 2 ^ ((n + 1) / 2) + 78) := by
  sorry

end OMA.S_oeis_a183984
