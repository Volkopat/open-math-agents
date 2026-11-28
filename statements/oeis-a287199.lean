import Mathlib

/-!
# OEIS A287199: Decimal representation of the diagonal from the origin to the corner of Rule 259

Source: https://oeis.org/A287199
Conjectures: Colin Barker, May 25 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A287199 (Robert Price, May 21 2017), offset 0: Decimal representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 259, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 259 on `ℤ × ℤ`.
* `%N` and all OEIS terms `1, 3, 4, 3, 16, 15, 64, 63, ...` read the diagonal cells
  `(0, 0)..(n, n)` in base 2 with the origin most significant (the last line of `%t` is a
  copy-paste x-axis typo).
-/

namespace OMA.S_oeis_a287199

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 259
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 259 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- `A287199(n)`: diagonal cells `(0, 0)..(n, n)` at stage `n` interpreted in base 2. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 2 ^ (n - i)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 + 2 * X)) =
      1 + 3 * X - X ^ 2 - 12 * X ^ 3 + 12 * X ^ 5 ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = 2 ^ n) ∧
    (∀ n : ℕ, n % 2 = 1 → a n = 2 ^ (n - 1) - 1) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 5 * a (n - 2) - 4 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a287199
