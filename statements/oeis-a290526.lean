import Mathlib

/-!
# OEIS A290526: Binary representation of the diagonal from the origin to the corner of Rule 833

Source: https://oeis.org/A290526
Conjectures: Colin Barker, Aug 05 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A290526 (Robert Price, Aug 04 2017), offset 0: Binary representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 833, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 833 on `ℤ × ℤ`.
* `%N` and all OEIS terms `1, 1, 101, 1111, 11, 111111, 111, ...` read the diagonal cells
  `(0, 0)..(n, n)` in base 10 with the origin most significant (the last line of `%t` is a
  copy-paste x-axis typo).
-/

namespace OMA.S_oeis_a290526

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 833
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 833 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- `A290526(n)`: diagonal cells `(0, 0)..(n, n)` at stage `n` read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2)) =
      1 - 10 * X ^ 2 + 1010 * X ^ 3 - 11100 * X ^ 4 + 110000 * X ^ 6 - 100000 * X ^ 7 ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = a (n - 1) + 110 * a (n - 2) - 110 * a (n - 3) - 1000 * a (n - 4) +
        1000 * a (n - 5)) := by
  sorry

end OMA.S_oeis_a290526
