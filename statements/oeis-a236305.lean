import Mathlib

/-!
# A236305: The number of P-positions in the game of Nim with up to 3 piles, allowing for piles of zero, such that the number of objects in each pile does not exceed n.

Source: https://oeis.org/A236305
Credit: @agchua

Formula line of A236305 by Thomas Baruchel, May 15 2018:
  a(n) = 4^floor(log(n)/log(2)) + 3*(n mod 2^floor(log(n)/log(2)))^2 (conjectured).
Offset 0. The P-positions of Nim are the tuples of pile sizes with Nim-sum (bitwise XOR) 0.
Piles of size 0 are allowed and ordered triples are counted ((0,1,1) differs from (1,0,1)), so
a(n) is the number of triples (x, y, z) with 0 <= x, y, z <= n and x XOR y XOR z = 0
(data 1, 4, 7, 16, 19, 28, 43, 64, ...; a(1) = 4 as in the entry's example).
Here floor(log(n)/log(2)) = Nat.log 2 n, the exponent of the largest power of 2 that is <= n.
The formula is stated for every n >= 1, where log(n) is defined.
-/

namespace OMA.S_oeis_a236305

/-- a(n): the number of ordered triples (x, y, z) with x, y, z <= n and x XOR y XOR z = 0. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (n + 1) ×ˢ Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
    (fun t => t.1 ^^^ t.2.1 ^^^ t.2.2 = 0)).card

/-- The conjectured formula of Thomas Baruchel (May 15 2018), for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = 4 ^ Nat.log 2 n + 3 * (n % 2 ^ Nat.log 2 n) ^ 2 := by
  sorry

end OMA.S_oeis_a236305
