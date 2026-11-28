import Mathlib

/-!
# The flattened Rule 206 triangle

Wolfram's rule number 206 has binary digits 11001110 in neighborhood
order 111 through 000. Start with one live cell at lattice position zero.
At time t the row consists of the cells from -t to t, in that order.
Its first index in the flattened, zero-based sequence is t², the sum of
the preceding odd row lengths. Thus at index n the row is t = floor(√n)
and the lattice position is n - t² - t.

Velin Yanev's conjecture uses floor(2√n), equivalently the integer square
root of 4n, in the exponent.
Source: https://oeis.org/A267708
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a267708

def rule : Bool → Bool → Bool → Bool
  | true, true, true | true, true, false | false, true, true
  | false, true, false | false, false, true => true
  | _, _, _ => false

def state : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | t + 1, x => rule (state t (x - 1)) (state t x) (state t (x + 1))

def term (n : ℕ) : ℤ :=
  let t := Nat.sqrt n
  if state t ((n : ℤ) - (t : ℤ) * t - t) then 1 else 0

theorem main : ∀ n : ℕ,
    term n = (1 + (-1 : ℤ) ^ Nat.sqrt (4 * n)) / 2 := by
  sorry

end OMA.S_oeis_a267708
