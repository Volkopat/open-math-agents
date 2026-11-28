import Mathlib

/-!
# A088884: Primes which when concatenated with their reverse and decremented by 2 yield a new prime

Source: https://oeis.org/A088884
Credit: @xor2k

Formalizes the two conjectural comments of OEIS A088884 (offset 1):

* Conjecture (Davide Rotondo): except for 3, all these primes are of the form 6*k - 1.
* Comment: it appears that if concat(p,reverse(p))-2 is prime, then concat(p,reverse(p))+2 is
  not and vice versa (tested for the first 60000 primes).

Conventions: for a natural number `p`, `concatRev p` is the decimal concatenation of `p` with
its digit reversal, `p * 10^L + reverse(p)` where `L` is the number of decimal digits of `p`
and `reverse(p)` is read off the little-endian list `Nat.digits 10 p` reversed (so
`concatRev 53 = 5335`, matching the OEIS example). A term of the sequence is a prime `p` such
that `concatRev p - 2` is prime; since `concatRev p ≥ 22` for every prime `p`, the natural
subtraction does not truncate. Being of the form `6*k - 1` (with `k ≥ 1`) is rendered as
`p % 6 = 5`, which avoids truncating subtraction. The second comment is stated for every prime
`p`, as two implications (one per direction of the vice versa).
-/

namespace OMA.S_oeis_a088884

/-- Decimal concatenation of `p` with its digit reversal. -/
def concatRev (p : ℕ) : ℕ :=
  p * 10 ^ (Nat.digits 10 p).length + Nat.ofDigits 10 (Nat.digits 10 p).reverse

/-- (1) Every prime `p ≠ 3` with `concatRev p - 2` prime satisfies `p ≡ 5 (mod 6)`.
(2) For every prime `p`, `concatRev p - 2` and `concatRev p + 2` are not both prime, stated as
the implication in each direction. -/
theorem main :
    (∀ p : ℕ, p.Prime → (concatRev p - 2).Prime → p ≠ 3 → p % 6 = 5) ∧
    (∀ p : ℕ, p.Prime →
      ((concatRev p - 2).Prime → ¬ (concatRev p + 2).Prime) ∧
      ((concatRev p + 2).Prime → ¬ (concatRev p - 2).Prime)) := by
  sorry

end OMA.S_oeis_a088884
