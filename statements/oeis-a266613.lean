import Mathlib

/-!
# A266613: Decimal representation of the middle column of the Rule 41 elementary cellular automaton starting with a single ON (black) cell.

Source: https://oeis.org/A266613
Conjectures: Colin Barker, Jan 02 2016 and Apr 16 2019. Karl V. Keller, Jr., Oct 07 2021. Andres Cicuttin, Mar 31 2016.
Formalization: @longling12 (drafted with AI assistance)

At time n the list represents sites -n through n on the integer line.
Both infinite tails have the evolving background value. Read the center bits chronologically in base 2.
-/

namespace OMA.S_oeis_a266613

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

def center (n : ℕ) : ℕ := ((row n)[n]?.getD false).toNat

def a : ℕ → ℕ
  | 0 => center 0
  | n + 1 => 2 * a n + center (n + 1)

/-- A000975: the alternating n-bit word starting with 1; the empty word is zero. -/
def a000975 : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * a000975 n + ((n + 1) % 2)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (31 * 2 ^ n - 4 * ((-1) ^ n + 3)) / 24) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = 2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - 2 * (a (n - 3) : ℤ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 2 * X)) = 1 - X ^ 4 + X ^ 5) ∧
    (∀ n : ℕ, 2 < n → (a n : ℚ) = (a000975 n : ℚ) + 20 * (2 : ℚ) ^ ((n : ℤ) - 5)) := by sorry

end OMA.S_oeis_a266613
