import Mathlib

/-!
# A348358: every prime `p > 7` is a concatenation of smaller primes in some base

Source: https://oeis.org/A348358
Credit: @avivorly

A348358: Primes which are not the concatenation of smaller primes (in base 10 and allowing leading 0's).

Conjecture (in the entry): Conjecture. If p > 7 is a prime, then there exists a base b such that p in base b is the
concatenation of smaller primes in base b.

Conventions:
- A base is a natural number `b ≥ 2`. `Nat.digits b p` is the base-`b` digit list of `p`, least significant digit
  first, with no zero at its most significant end.
- `p` in base `b` is a concatenation of smaller primes when its digit string splits into consecutive nonempty blocks,
  each of which, read as a base-`b` numeral, is a prime smaller than `p`. As in the entry's definition (and its example
  307 = 3 U 07 in base 10), leading zeros are allowed inside a block: a block is read with `Nat.ofDigits b`, so zeros
  at its most significant end add nothing.
- The blocks are taken from the least-significant-first list `Nat.digits b p`, and each block is read least significant
  digit first by `Nat.ofDigits`. Reversing the whole list reverses both the block order and the digit order inside each
  block, so this is the same as splitting the usual (most significant first) digit string of `p` into consecutive
  blocks and reading each block in the usual way.
- At least two blocks are forced: a single block has the value `p`, which is not smaller than `p`. The same prime may
  occur in several blocks (227 = 2 U 2 U 7 in base 10, as in the entry).
- No upper bound is put on `b`; for `b > p` the digit list is the single digit `p`, so such bases never work.
-/

namespace OMA.S_oeis_a348358

/-- `p` written in base `b` is a concatenation of primes smaller than `p`: the base-`b` digit list of `p` (least
significant digit first, as in `Nat.digits`) is the concatenation of consecutive nonempty blocks, each of which, read
in base `b` with leading zeros allowed, is a prime smaller than `p`. -/
def IsConcatOfSmallerPrimes (b p : ℕ) : Prop :=
  ∃ L : List (List ℕ), L.flatten = Nat.digits b p ∧
    ∀ B ∈ L, B ≠ [] ∧ (Nat.ofDigits b B).Prime ∧ Nat.ofDigits b B < p

theorem main :
    ∀ p : ℕ, p.Prime → 7 < p → ∃ b : ℕ, 2 ≤ b ∧ IsConcatOfSmallerPrimes b p := by
  sorry

end OMA.S_oeis_a348358
