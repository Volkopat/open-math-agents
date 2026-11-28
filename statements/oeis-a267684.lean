import Mathlib

/-!
# A267684: Binary representation of the n-th iteration of the Rule 203 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A267684
Conjectures: Colin Barker, Jan 19 2016 and Apr 17 2019. Karl V. Keller, Jr., Jun 07 2022.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the displayed row left to right in base 10.
-/

namespace OMA.S_oeis_a267684

def update (l c r : Bool) : Bool :=
  (203 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

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
    (∀ n : ℕ, 4 < n → (a n : ℤ) = 111 * (a (n - 1) : ℤ) - 1110 * (a (n - 2) : ℤ) + 1000 * (a (n - 3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 - 10 * X) * (1 - 100 * X)) = 1 - 11 * X + 1021 * X ^ 2 - 2110 * X ^ 3 + 1000 * X ^ 4) ∧
    (∀ n : ℕ, 1 < n → (a n : ℚ) = (10 * 100 ^ n - 9 * 10 ^ n - 1) / 9) := by sorry

end OMA.S_oeis_a267684
