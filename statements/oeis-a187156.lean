import Mathlib

/-!
# A187156: 3-step one-space bishop tours on an n×n board

Source: https://oeis.org/A187156
Credit: @mbilenko03

A one-space bishop moves by a single diagonal step: both coordinates change by
exactly `1`. The OEIS examples for a `4×4` board label the visited squares
`1, 2, 3` and print `0` for every empty square, so a 3-step tour is a directed
path of three distinct squares. Counting those paths gives the recorded terms
`0, 0, 20, 64, 132, 224` for `n = 1, 2, 3, 4, 5, 6`. Paths of four squares are
the next row of A187155.

`a n` is that number of tours on an `n×n` board, with `a 0 = 0` on the empty
board. The entry records the empirical formula `12*n^2 - 40*n + 32` for `n > 1`
and Colin Barker's conjectures (28 Feb 2018): the generating function
`4*x^3*(5 + x)/(1 - x)^3`, and `a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3)` for `n > 4`.
-/

namespace OMA.S_oeis_a187156

/-- Both coordinates of a one-space diagonal step change by exactly one. -/
def IsDiag (d : ℤ × ℤ) : Prop :=
  (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1)

/-- Squares of an `n×n` board. -/
abbrev Square (n : ℕ) := Fin n × Fin n

/-- Integer displacement from `p` to `q`. -/
def delta {n : ℕ} (p q : Square n) : ℤ × ℤ :=
  ((q.1.val : ℤ) - (p.1.val : ℤ), (q.2.val : ℤ) - (p.2.val : ℤ))

instance (d : ℤ × ℤ) : Decidable (IsDiag d) := by
  unfold IsDiag
  infer_instance

/-- A directed 3-step one-space bishop tour: three distinct squares, each step diagonal. -/
def IsTour {n : ℕ} (p : Fin 3 → Square n) : Prop :=
  Function.Injective p ∧ IsDiag (delta (p 0) (p 1)) ∧ IsDiag (delta (p 1) (p 2))

instance {n : ℕ} (p : Fin 3 → Square n) : Decidable (IsTour p) := by
  unfold IsTour delta
  infer_instance

/-- Number of directed 3-step one-space bishop tours on an `n×n` board. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Fin 3 → Square n => IsTour p)).card

open PowerSeries

/-- The closed form for `n > 1`, Barker's recurrence for `n > 4`, and the
generating function `4*x^3*(5 + x)/(1 - x)^3` with denominator cleared. -/
theorem main :
    (∀ n : ℕ, 1 < n → (a n : ℤ) = 12 * (n : ℤ) ^ 2 - 40 * (n : ℤ) + 32) ∧
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 = 4 * X ^ 3 * (5 + X) := by
  sorry

end OMA.S_oeis_a187156
