import Mathlib

/-!
# A267257: Binary representation of the middle column of the Rule 111 elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A267257
Conjectures by Colin Barker, Jan 13 2016 and Apr 19 2019.
Formalization: @longling12 (drafted with AI assistance)

The finite word stores sites -n through n from left to right; the separate bit
represents both infinite uniform tails and is updated by the same rule.
The centre bits from time zero to time n form a base-10 numeral, oldest first.
The ordinary generating function is stated after clearing its unit-constant denominator.
-/

namespace OMA.S_oeis_a267257

def update (l c r : Bool) : Bool :=
  (111 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail

/-- Both infinite tails have the same value. The list gives sites -n through n. -/
def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))

def centre (n : ℕ) : ℕ := ((row n).2[n]!).toNat

def a : ℕ → ℕ
  | 0 => centre 0
  | n + 1 => 10 * a n + centre (n + 1)

open PowerSeries in
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℚ) = (-9 * (-1 : ℚ) ^ n + 109999999 * (2 : ℚ) ^ (n - 5) * (5 : ℚ) ^ (n - 6) - 11) / 198) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X)) =
      1 + X - X ^ 8) := by sorry

end OMA.S_oeis_a267257
