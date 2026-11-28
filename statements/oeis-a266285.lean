import Mathlib

/-!
# A266285: Number of ON (black) cells in the n-th iteration of the Rule 13 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266285
Conjectures: Colin Barker, Dec 28 2015 and Apr 14 2019. Ctibor O. Zizka, Mar 11 2025.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Count the indicated color in the displayed row.
-/

namespace OMA.S_oeis_a266285

def update (l c r : Bool) : Bool :=
  (13 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

/-- Each step also updates the common value on both infinite tails. -/
def background : ℕ → Bool
  | 0 => false
  | n + 1 => let b := background n; update b b b

/-- Slide a three-cell window from left to right. -/
def scan (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: rs => update l c r :: scan c r rs

/-- Sites -n through n, represented in increasing order. -/
def row : ℕ → List Bool
  | 0 => [true]
  | n + 1 =>
    let b := background n
    scan b b (row n ++ [b, b])

def a (n : ℕ) : ℕ := (row n).count true

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = ((-1) ^ n * (3 - 2 * (n : ℚ)) + 4 * (n : ℚ) + 1) / 4) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) = 1 + X + 2 * X ^ 3) ∧
    (∀ n : ℕ, (a (2 * n) : ℤ) = (n : ℤ) + 1) ∧
    (∀ n : ℕ, (a (2 * n + 1) : ℤ) = 3 * (n : ℤ) + 1) := by sorry

end OMA.S_oeis_a266285
