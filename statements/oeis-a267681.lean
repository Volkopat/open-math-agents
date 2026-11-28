import Mathlib

/-!
# A267681: Decimal representation of the n-th iteration of the Rule 201 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267681
Conjectures: Colin Barker, Jan 19 2016. M. F. Hasler, Jul 28 2018.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 2.
-/

namespace OMA.S_oeis_a267681

def update (l c r : Bool) : Bool :=
  (201 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 5 * (a (n - 1) : ℤ) - 20 * (a (n - 3) : ℤ) + 16 * (a (n - 4) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 2 * X) * (1 + 2 * X) * (1 - 4 * X)) = 1 - 5 * X + 21 * X ^ 2 + 14 * X ^ 3 - 40 * X ^ 4) ∧
    (∀ n : ℕ, (a n : ℚ) = 2 * 4 ^ n - (((n % 2 : ℕ) : ℚ) * 2 + (if 0 < n then (1 : ℚ) else 0) * 5) * (2 : ℚ) ^ ((n : ℤ) - 1) - 1) := by sorry

end OMA.S_oeis_a267681
