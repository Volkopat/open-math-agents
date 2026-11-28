import Mathlib

/-!
# A266975: Binary representation of the n-th iteration of the Rule 78 elementary cellular automaton starting with a single ON (black) cell

Source: https://oeis.org/A266975
Conjectures by Colin Barker, Jan 08 2016 and Apr 18 2019.
Formalization: @longling12 (drafted with AI assistance)

The finite word stores sites -n through n from left to right; the separate bit
represents both infinite uniform tails and is updated by the same rule.
The leftmost site is the most significant digit of the base-10 numeral.
The ordinary generating function is stated after clearing its unit-constant denominator.
-/

namespace OMA.S_oeis_a266975

def update (l c r : Bool) : Bool :=
  (78 : ℕ).testBit (4 * l.toNat + 2 * c.toNat + r.toNat)

def sweep (l c : Bool) : List Bool → List Bool
  | [] => []
  | r :: tail => update l c r :: sweep c r tail

/-- Both infinite tails have the same value. The list gives sites -n through n. -/
def row : ℕ → Bool × List Bool
  | 0 => (false, [true])
  | n + 1 =>
    let (b, w) := row n
    (update b b b, sweep b b (w ++ [b, b]))

def a (n : ℕ) : ℕ :=
  Nat.ofDigits 10 ((row n).2.map Bool.toNat).reverse

open PowerSeries in
theorem main :
    (∀ n : ℕ, 0 < n → (a n : ℚ) = (2 : ℚ) ^ ((n : ℤ) - 2) * (5 : ℚ) ^ (n - 1) * (9 * (-10 : ℚ) ^ n + 2189 * (10 : ℚ) ^ n - 20) / 99) ∧
    (∀ n : ℕ, 3 < n → (a n : ℚ) = 10 * (a (n - 1) : ℚ) + 10000 * (a (n - 2) : ℚ) - 100000 * (a (n - 3) : ℚ)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 10 * X) * (1 - 100 * X) * (1 + 100 * X)) =
      1 + 100 * X - 10000 * X ^ 3) := by sorry

end OMA.S_oeis_a266975
