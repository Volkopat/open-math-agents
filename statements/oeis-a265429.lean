import Mathlib

/-!
# A265429: Total number of ON (black) cells after n iterations of the Rule 188 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A265429
Conjectures: Colin Barker, Dec 09 2015 and Apr 16 2019. Gevorg Hmayakyan, Sep 01 2019.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Sum the displayed row counts from time zero through n.
-/

namespace OMA.S_oeis_a265429

def update (l c r : Bool) : Bool :=
  (188 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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

def a : ℕ → ℕ
  | 0 => (row 0).count true
  | n + 1 => a n + (row (n + 1)).count true

open PowerSeries in
theorem main :
    (∀ n : ℕ, (a n : ℂ) = 1 / 16 * (6 * (n : ℂ) ^ 2 + 24 * (n : ℂ) - 3 * (-1) ^ n + 2 * (-Complex.I) ^ n + 2 * Complex.I ^ n + 15)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2)) = 1 + X + 2 * X ^ 3 - X ^ 4) ∧
    (∀ k : ℕ, (∃ n : ℕ, a n = k) ↔ 0 < k ∧ ⌊Real.sqrt (8 * ((k : ℝ) + 1) / 3)⌋ ≠ ⌊Real.sqrt (8 * (k : ℝ) / 3)⌋) := by sorry

end OMA.S_oeis_a265429
