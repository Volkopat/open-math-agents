import Mathlib

/-!
# OEIS A375965: Primes turned into a different prime by exchanging two consecutive digits

Source: https://oeis.org/A375965
Credit: @unserus

OEIS: "But is this sequence even infinite?" and (Robert Israel, Sep 04 2024):
"Dickson's conjecture implies it is infinite, e.g. it implies that there are
infinitely many primes ending in 13 for which changing the last two digits to 31
produces a prime."

The terms are the primes `p` such that swapping two adjacent decimal digits of
`p` gives a prime different from `p`. A leading zero produced by a swap is
allowed (it is dropped): 103 is a term because 013 = 13 is prime; the listed
terms match only with this reading. Digits are handled with the little-endian
list `Nat.digits 10 p`; swapping positions `i` and `i + 1` of that list is a swap
of two adjacent digits, and `Nat.ofDigits 10` reads the result back (a zero that
becomes the leading digit is ignored). The statement is the expected answer:
the sequence is infinite.
-/

namespace OMA.S_oeis_a375965

/-- Swap the entries at positions `i` and `i + 1` of a list. -/
def swapAdj (L : List ℕ) (i : ℕ) : List ℕ :=
  (L.set i (L.getD (i + 1) 0)).set (i + 1) (L.getD i 0)

/-- `p` is a term: some swap of two adjacent digits gives a different prime. -/
def IsTerm (p : ℕ) : Prop :=
  p.Prime ∧ ∃ i, i + 1 < (Nat.digits 10 p).length ∧
    let q := Nat.ofDigits 10 (swapAdj (Nat.digits 10 p) i)
    q ≠ p ∧ q.Prime

/-- A375965 is infinite. -/
theorem main : {p : ℕ | IsTerm p}.Infinite := by
  sorry

end OMA.S_oeis_a375965
