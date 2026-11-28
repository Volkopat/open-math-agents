import Mathlib

/-!
# A292349: Pri-most primes: primes p such that the majority of bits in the binary representation of p satisfy the following: complementing this bit produces a prime number.

Source: https://oeis.org/A292349
Credit: @jagraj28

Conjecture (stated in A292349): the sequence is finite. Its known terms are
`7, 19, 23, 43, 71, 101`; any further term is greater than `10 ^ 12` (Lucas A. Brown, 2024).

Formalization notes:
* The bits of `p` are the `L = (Nat.digits 2 p).length` digits of its binary representation,
  at positions `0, …, L - 1` (the leading `1` included). Complementing the bit at position `i`
  gives `p ^^^ 2 ^ i` (bitwise xor).
* "The majority of bits" means strictly more than half of them: `L < 2 * c`, where `c` is the
  number of positions whose complement is prime.
* A direct search with this reading gives exactly the listed terms below `2 · 10 ^ 5`.
-/

namespace OMA.S_oeis_a292349

/-- The number of bit positions of `p` whose complement gives a prime. -/
def primeFlips (p : ℕ) : ℕ :=
  ((Finset.range (Nat.digits 2 p).length).filter (fun i => (p ^^^ 2 ^ i).Prime)).card

/-- `p` is pri-most: complementing a strict majority of its bits gives a prime. -/
def IsPriMost (p : ℕ) : Prop := (Nat.digits 2 p).length < 2 * primeFlips p

/-- The conjecture of A292349: there are only finitely many pri-most primes. -/
theorem main : {p : ℕ | p.Prime ∧ IsPriMost p}.Finite := by
  sorry

end OMA.S_oeis_a292349
