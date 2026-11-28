import Mathlib

/-!
# A267678: Decimal representation of the n-th iteration of the Rule 197 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267678
Conjectures: Colin Barker, Jan 19 2016. Colin Barker, Feb 14 2017. Karl V. Keller, Jr., Jun 01 2022.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 2.
-/

namespace OMA.S_oeis_a267678

def update (l c r : Bool) : Bool :=
  (197 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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

def a (n : ℕ) : ℕ := Nat.ofDigits 2 ((row n).map Bool.toNat).reverse

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 7 * (a (n - 2) : ℤ) - 6 * (a (n - 3) : ℤ) + 8 * (a (n - 4) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 4 * X)) = 1 - 4 * X + 15 * X ^ 2 + 4 * X ^ 3 - 12 * X ^ 4 - 16 * X ^ 5) ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = 2 * (-3 + (-1) ^ n - 2 ^ (2 + n) + 3 * 4 ^ n) / 3) ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = (⌊((6 * 4 ^ n - 8 * 2 ^ n) / 3 : ℚ)⌋ : ℚ) - 2 ^ (n % 2)) := by sorry

end OMA.S_oeis_a267678
