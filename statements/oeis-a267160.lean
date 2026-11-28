import Mathlib

/-!
# A267160: Number of OFF (white) cells in the n-th iteration of the Rule 107 elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A267160
Conjectures by Colin Barker, Jan 11 2016 and Apr 19 2019.
Formalization: @longling12 (drafted with AI assistance)

The finite word stores sites -n through n from left to right; the separate bit
represents both infinite uniform tails and is updated by the same rule.
Count the indicated colour in the displayed window at time n.
The ordinary generating function is stated after clearing its unit-constant denominator.
-/

namespace OMA.S_oeis_a267160

def update (l c r : Bool) : Bool :=
  (107 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail

/-- Both infinite tails have the same value. The list gives sites -n through n. -/
def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))

def a (n : ℕ) : ℕ := (row n).2.count false

open PowerSeries in
theorem main :
    (∀ n : ℕ, 11 < n → (a n : ℚ) = (a (n - 2) : ℚ) + (a (n - 4) : ℚ) - (a (n - 6) : ℚ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2)) =
      X * (2 + 2 * X + X ^ 3 - X ^ 4 + X ^ 5 - X ^ 6 + 4 * X ^ 7 + X ^ 8 - X ^ 9 - X ^ 10 + X ^ 11)) := by sorry

end OMA.S_oeis_a267160
