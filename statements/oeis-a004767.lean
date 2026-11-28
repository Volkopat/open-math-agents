import Mathlib

/-!
# A004767: a(n) = 4*n + 3

Source: https://oeis.org/A004767
Credit: @xor2k

The entry's text is a remark mentioning the Collatz conjecture, not a statement of it:
For the Collatz Conjecture, we identify two types of odd numbers. This sequence contains all the
ascenders: where (3*a(n) + 1) / 2 is odd and greater than a(n). See A016813 for the descenders.

Formalized claim (the Collatz conjecture itself is NOT formalized): an odd natural number `m` is an
ascender, i.e. `(3*m + 1)/2` is odd and greater than `m`, if and only if `m` is a term of the
sequence, i.e. `m = 4*n + 3` for some `n ≥ 0` (offset 0). Thus every term is an ascender and the
sequence contains all ascenders.

Conventions: `m` and `n` are natural numbers; `/` is floor division on `ℕ`, which is exact here since
`3*m + 1` is even for odd `m`.
-/

namespace OMA.S_oeis_a004767

/-- `a(n) = 4*n + 3`. -/
def a (n : ℕ) : ℕ :=
  4 * n + 3

/-- An odd number `m` is an ascender (`(3m+1)/2` odd and `> m`) iff `m` is a term `a(n)`. -/
theorem main :
    ∀ m : ℕ, Odd m → ((Odd ((3 * m + 1) / 2) ∧ (3 * m + 1) / 2 > m) ↔ ∃ n : ℕ, m = a n) := by
  sorry

end OMA.S_oeis_a004767
