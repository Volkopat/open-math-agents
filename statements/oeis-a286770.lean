import Mathlib

/-!
# OEIS A286770: Binary representation of the diagonal from the corner to the origin of Rule 221

Source: https://oeis.org/A286770
Conjectures: Colin Barker, May 14 2017.
Formalization: @longling12 (drafted with AI assistance)

Entry A286770 (Robert Price, May 14 2017), offset 0: Binary representation of the diagonal from
the corner to the origin of the n-th stage of growth of the two-dimensional cellular automaton
defined by Rule 221, based on the 5-celled von Neumann neighborhood, initialized with a single
black (ON) cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 221 on `ℤ × ℤ`.
* As in other diagonal entries by Price, the last line of `%t` contains a copy-paste x-axis line,
  whereas `%N` and all OEIS terms `1, 10, 0, 1110, 1, 111110, ...` read the diagonal cells
  `(-n, -n), (-n + 1, -n + 1), ..., (0, 0)` in base 10 with the corner most significant.
* `10^n - 1` is divisible by `9` for every `n`, so integer division `/ 9` is exact.
-/

namespace OMA.S_oeis_a286770

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

/-- `A286770(n)`: diagonal cells `(-n, -n)..(0, 0)` at stage `n` read as base-10 digits. -/
def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1), (state n ((i : ℤ) - n) ((i : ℤ) - n)).toNat * 10 ^ (n - i)

theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X)) =
      1 + 10 * X - 101 * X ^ 2 + 100 * X ^ 3 + 101 * X ^ 4 - 100 * X ^ 6 ∧
    (∀ n : ℕ, 2 < n → n % 2 = 0 → a n = 1) ∧
    (∀ n : ℕ, 2 < n → n % 2 = 1 → a n = 10 * (10 ^ n - 1) / 9) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 101 * a (n - 2) - 100 * a (n - 4)) := by
  sorry

end OMA.S_oeis_a286770
