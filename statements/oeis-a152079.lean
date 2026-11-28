import Mathlib

/-!
# A152079: Primes p such that A000695(p) are also prime.

Source: https://oeis.org/A152079
Credit: @gblacher2

Conjecture (comment in A152079, an entry by Vladimir Shevelev, Nov 23 2008): The sequence
contains infinitely many terms.

Conventions: A000695 is the Moser-de Bruijn sequence (offset 0: 0, 1, 4, 5, 16, 17, 20, 21, …),
the sums of distinct powers of 4. Its `n`-th term is obtained by reading the binary digits of `n`
in base 4, that is `Nat.ofDigits 4 (Nat.digits 2 n)` (`Nat.digits 2 n` lists the binary digits of
`n`, least significant first). The sequence A152079 lists the primes `p` such that A000695(p) is
also prime; the conjecture says that this set is infinite.
-/

namespace OMA.S_oeis_a152079

/-- The Moser-de Bruijn sequence A000695: the binary digits of `n` read in base 4. -/
def moserDeBruijn (n : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 n)

/-- The terms of A152079: primes `p` with A000695(p) prime. -/
def S : Set ℕ := {p : ℕ | p.Prime ∧ (moserDeBruijn p).Prime}

/-- The conjecture: A152079 contains infinitely many terms. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a152079
