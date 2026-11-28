import Mathlib

/-!
# A225106: Prime powers (A025475) that can be represented as a sum of two distinct prime powers.

Source: https://oeis.org/A225106
Credit: @luciusacarr

The entry records one conjecture (Alex Ratushnyak, Feb 03 2020): the sequence is finite. Its
known terms are 9, 25, 81, 125, 512, 5041 (9 = 8 + 1, 25 = 16 + 9, 81 = 32 + 49, 125 = 121 + 4,
512 = 169 + 343, 5041 = 128 + 4913); the next term, if it exists, is bigger than 2^64.

Reading of the source:
* "Prime powers" are the terms of A025475: `1` and the numbers `p^m` with `p` prime and `m ≥ 2`
  (primes themselves are excluded). The example 9 = 8 + 1 shows that `1` counts as a summand.
* `n` is a term if `n` is in A025475 and `n = a + b` with `a ≠ b` both in A025475. With this
  reading the terms below `10^6` are exactly the listed ones.
-/

namespace OMA.S_oeis_a225106

/-- `n` is in A025475: `n = 1` or `n = p^m` with `p` prime and `m ≥ 2`. -/
def IsA025475 (n : ℕ) : Prop := n = 1 ∨ ∃ p m : ℕ, p.Prime ∧ 2 ≤ m ∧ n = p ^ m

theorem main :
    {n : ℕ | IsA025475 n ∧ ∃ a b : ℕ, a ≠ b ∧ IsA025475 a ∧ IsA025475 b ∧ n = a + b}.Finite := by
  sorry

end OMA.S_oeis_a225106
