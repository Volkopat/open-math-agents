import Mathlib

/-!
# A266609: Binary representation of the n-th iteration of the Rule 41 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266609
Conjectures: Colin Barker, Jan 02 2016 and Apr 18 2019. Karl V. Keller, Jr., Oct 07 2021.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 10.
-/

namespace OMA.S_oeis_a266609

def update (l c r : Bool) : Bool :=
  (41 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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

def a (n : ℕ) : ℕ := Nat.ofDigits 10 ((row n).map Bool.toNat).reverse

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 10000 * (a (n - 2) : ℤ) + (a (n - 4) : ℤ) - 10000 * (a (n - 6) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 100 * X) * (1 + 100 * X) * (1 + X ^ 2)) = 1 - 9899 * X ^ 2 + 1100100 * X ^ 3 - 1010000 * X ^ 4 + 110111000 * X ^ 5) ∧
    (∀ n : ℕ, Odd n → (a n : ℚ) = (⌊((10 * 100 ^ n + 10 - 1010 * ((n % 4 : ℕ) : ℚ)) / 9 : ℚ)⌋ : ℚ) - 10675 * 0 ^ ((n + 1) % 4)) ∧
    (∀ n : ℕ, Even n → (a n : ℚ) = 101 ^ (n % 4 / 2)) := by sorry

end OMA.S_oeis_a266609
