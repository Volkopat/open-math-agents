import Mathlib

/-!
# OEIS A286771: Binary representation of the diagonal from the origin to the corner of Rule 221

Source: https://oeis.org/A286771
Conjectures: Colin Barker, May 14 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A286771 (Robert Price, May 14 2017), offset 0: Binary representation of the diagonal from
the origin to the corner of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 221, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 221 on `ℤ × ℤ`.
* `%N` and all OEIS terms `1, 1, 0, 111, 10000, 11111, ...` read the diagonal cells
  `(0, 0), (1, 1), ..., (n, n)` in base 10 with the origin most significant (the last line of `%t`
  is a copy-paste x-axis typo).
* `10^n - 1` is divisible by `9` for every `n`, so `/ 9` is exact.
-/

namespace OMA.S_oeis_a286771

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 221
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 221 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- `A286771(n)`: diagonal cells `(0, 0)..(n, n)` at stage `n` read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n (i : ℤ) (i : ℤ)).toNat * 10 ^ (n - i)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + X - 101 * X ^ 2 + 10 * X ^ 3 + 10100 * X ^ 4 - 10000 * X ^ 6 ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 → a n = 10 ^ n) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 → a n = (10 ^ n - 1) / 9) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a286771
