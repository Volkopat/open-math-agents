import Mathlib

/-!
# OEIS A209725

`1/4` the number of `(n + 1) × 7` `0..2` arrays with every `2 × 2` subblock having distinct
clockwise edge differences.

Conjectured by Colin Barker (Jul 12 2018):
* for even `n ≥ 1`, `a(n) = 3 * 2 ^ (n / 2 - 1) + 10`,
* for odd `n ≥ 1`, `a(n) = 2 ^ ((n + 1) / 2) + 10`.
-/

namespace OMA.S_oeis_a209725

/-- A `2 × 2` block with top row `(a, b)` and bottom row `(d, c)` has distinct clockwise
edge differences `b - a`, `c - b`, `d - c`, `a - d` (in `ℤ`). -/
def distinctClockwise (a b d c : Fin 3) : Prop :=
  let d1 : ℤ := (b.1 : ℤ) - (a.1 : ℤ)
  let d2 : ℤ := (c.1 : ℤ) - (b.1 : ℤ)
  let d3 : ℤ := (d.1 : ℤ) - (c.1 : ℤ)
  let d4 : ℤ := (a.1 : ℤ) - (d.1 : ℤ)
  d1 ≠ d2 ∧ d1 ≠ d3 ∧ d1 ≠ d4 ∧ d2 ≠ d3 ∧ d2 ≠ d4 ∧ d3 ≠ d4

/-- An `(n + 1) × 7` array over `Fin 3` is valid if every `2 × 2` subblock has distinct
clockwise edge differences. -/
def isValid (n : ℕ) (A : Fin (n + 1) → Fin 7 → Fin 3) : Prop :=
  ∀ (i : Fin n) (j : Fin 6),
    distinctClockwise (A i.castSucc j.castSucc) (A i.castSucc j.succ)
      (A i.succ j.castSucc) (A i.succ j.succ)

/-- `a(n)` is `1/4` of the number of valid `(n + 1) × 7` arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {A : Fin (n + 1) → Fin 7 → Fin 3 // isValid n A} / 4

theorem main :
    (∀ n : ℕ, 1 ≤ n → Even n → a n = 3 * 2 ^ (n / 2 - 1) + 10) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → a n = 2 ^ ((n + 1) / 2) + 10) := by
  sorry

end OMA.S_oeis_a209725
