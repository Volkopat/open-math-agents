import Mathlib

/-!
# A266286: Number of OFF (white) cells in the n-th iteration of the Rule 13 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266286
Conjectures: Colin Barker, Dec 28 2015 and Apr 14 2019. Andres Cicuttin, Aug 29 2019. Stefano Spezia, Aug 31 2019.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Count the indicated color in the displayed row.
-/

namespace OMA.S_oeis_a266286

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

def a (n : ℕ) : ℕ := (row n).count false

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℚ) = (2 * ((-1) ^ n + 2) * (n : ℚ) - 3 * (-1) ^ n + 3) / 4) ∧
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 2 * (a (n - 2) : ℤ) - (a (n - 4) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2) = X * (2 + 3 * X - X ^ 2)) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = (n ^ 2 % (2 * n - 3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ) / n.factorial) =
      PowerSeries.C (1 / 4 : ℚ) * (PowerSeries.rescale (-1 : ℚ) (PowerSeries.exp ℚ)) *
        (-3 - 2 * X + (PowerSeries.rescale (2 : ℚ) (PowerSeries.exp ℚ)) * (3 + 4 * X))) := by sorry

end OMA.S_oeis_a266286
