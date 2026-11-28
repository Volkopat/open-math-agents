import Mathlib

/-!
# OEIS A270684: First differences of number of active (ON, black) cells in Rule 190

Source: https://oeis.org/A270684
Conjectures: Colin Barker, Mar 21 2016.
Formalization: @longling12 (drafted with AI assistance)

Entry A270684 (Robert Price, Mar 21 2016), offset 0: First differences of number of active
(ON, black) cells in n-th stage of growth of two-dimensional cellular automaton defined by
Rule 190, based on the 5-celled von Neumann neighborhood, initialized with a single black (ON)
cell at stage zero.

Formalization notes:
* Outer-totalistic 5-cell von Neumann rule 190 on `ℤ × ℤ`.
* Following `%t` (`Table[on[[i+1]] - on[[i]], ...]`), `onCount n` counts ON cells in `[-n, n]^2`
  at stage `n`, and `a n = onCount (n + 1) - onCount n : ℤ`, reproducing `4, 7, 12, 8, 20, 8, ...`.
-/

namespace OMA.S_oeis_a270684

open PowerSeries

/-- One step of the 2D outer-totalistic cellular automaton with code 190
on the 5-cell von Neumann neighborhood. -/
def step (g : ℤ → ℤ → Bool) (x y : ℤ) : Bool :=
  Nat.testBit 190 ((g x y).toNat + 2 *
    ((g (x - 1) y).toNat + (g (x + 1) y).toNat + (g x (y - 1)).toNat + (g x (y + 1)).toNat))

/-- Stage `n` of the automaton on `ℤ × ℤ` started from a single ON cell at `(0, 0)`. -/
def state : ℕ → ℤ → ℤ → Bool
  | 0 => fun x y => decide (x = 0 ∧ y = 0)
  | n + 1 => step (state n)

/-- Number of ON cells in `[-n, n]^2` at stage `n` of Rule 190. -/
def onCount (n : ℕ) : ℤ :=
  (((Finset.range (2 * n + 1) ×ˢ Finset.range (2 * n + 1)).filter fun p : ℕ × ℕ =>
    state n ((p.1 : ℤ) - n) ((p.2 : ℤ) - n)).card : ℤ)

/-- `A270684(n)`: first difference `onCount (n + 1) - onCount n`. -/
def a (n : ℕ) : ℤ := onCount (n + 1) - onCount n

theorem main :
    (∀ n : ℕ, 1 < n → a n = 2 * (3 - (-1) ^ n + (n : ℤ) + (-1) ^ n * (n : ℤ))) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 0 → a n = 4 * (n : ℤ) + 4) ∧
    (∀ n : ℕ, 1 < n → n % 2 = 1 → a n = 8) ∧
    (∀ n : ℕ, 3 < n → a n = 2 * a (n - 2) - a (n - 4)) ∧
    PowerSeries.mk a * ((1 - X) ^ 2 * (1 + X) ^ 2) =
      4 + 7 * X + 4 * X ^ 2 - 6 * X ^ 3 - X ^ 5 := by
  sorry

end OMA.S_oeis_a270684
