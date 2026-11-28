import Mathlib

/-!
# A088268: Palindromes in A007530.

Source: https://oeis.org/A088268
Credit: @luciusacarr

The entry records one conjecture: the sequence is finite. Its terms begin 5, 11, 101, 191, 16061,
1748471, 179868971, ...

Reading of the source:
* A007530 lists the prime quadruples: the numbers `k` such that `k`, `k + 2`, `k + 6` and `k + 8`
  are all prime (5, 11, 101, 191, 821, ...).
* A palindrome is a number whose decimal expansion reads the same backwards.
* With this reading the terms below `2 * 10^6` are exactly 5, 11, 101, 191, 16061, 1748471, as
  listed.
-/

namespace OMA.S_oeis_a088268

/-- `k` is a term: `k` starts a prime quadruple and is a decimal palindrome. -/
def IsTerm (k : ℕ) : Prop :=
  k.Prime ∧ (k + 2).Prime ∧ (k + 6).Prime ∧ (k + 8).Prime ∧
    (Nat.digits 10 k).reverse = Nat.digits 10 k

theorem main : {k : ℕ | IsTerm k}.Finite := by
  sorry

end OMA.S_oeis_a088268
