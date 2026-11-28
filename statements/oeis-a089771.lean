import Mathlib

/-!
# A089771: the largest n-digit prime with no prime among its digit blocks

Source: https://oeis.org/A089771
Credit: @R-Dson

`a(n)` is the largest n-digit prime containing no prime substrings, or `0` if no such prime
exists. Conjecture: no term is zero.

Conventions.
- A prime substring of `p` is a block of consecutive decimal digits of `p`, other than the whole
  number, that denotes a prime; single digits count, as in the program of the entry (which
  rejects every substring `s[i:j]` with `(i, j) ≠ (0, length)` that is prime).
- `Nat.digits 10 p` lists the digits least significant first; a block of the printed number is a
  block of that list, and `ofDigits` gives the number it denotes.
- `a(n)` is the supremum in `ℕ` of the set of such primes, so it is `0` exactly when the set is
  empty.
- The offset of the entry is `1`.
- First terms of the entry: 7, 89, 991, 9949, 99469, 996649, ...
-/

namespace OMA.S_oeis_a089771

/-- The number denoted by a list of decimal digits, least significant digit first. -/
def ofDigits : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 10 * ofDigits ds

/-- Some block of consecutive decimal digits of `p`, other than the whole number, denotes a
prime. -/
def HasPrimeSubstring (p : ℕ) : Prop :=
  ∃ i ∈ Finset.range ((Nat.digits 10 p).length + 1),
    ∃ j ∈ Finset.range ((Nat.digits 10 p).length + 1),
      i < j ∧ (i, j) ≠ (0, (Nat.digits 10 p).length) ∧
        (ofDigits (((Nat.digits 10 p).drop i).take (j - i))).Prime

/-- Largest n-digit prime with no prime substring, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {p : ℕ | p.Prime ∧ (Nat.digits 10 p).length = n ∧ ¬ HasPrimeSubstring p}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a089771
