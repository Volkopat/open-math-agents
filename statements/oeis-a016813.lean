import Mathlib

/-!
# A016813: a(n) = 4*n + 1

Source: https://oeis.org/A016813
Credit: @xor2k

The entry's text is a remark mentioning the Collatz conjecture, not a statement of it:
For the Collatz conjecture, we identify two types of odd numbers. This sequence contains all the
descenders: where (3*a(n) + 1) / 2 is even and requires additional divisions by 2. See A004767 for
the ascenders.

Formalized claim (the Collatz conjecture itself is NOT formalized): an odd natural number `m` is a
descender, i.e. `(3*m + 1)/2` is even (so it requires additional divisions by 2), if and only if `m`
is a term of the sequence, i.e. `m = 4*n + 1` for some `n ≥ 0` (offset 0). Thus every term is a
descender and the sequence contains all descenders.

Conventions: `m` and `n` are natural numbers; `/` is floor division on `ℕ`, which is exact here since
`3*m + 1` is even for odd `m`.
-/

namespace OMA.S_oeis_a016813

/-- `a(n) = 4*n + 1`. -/
def a (n : ℕ) : ℕ :=
  4 * n + 1

/-- An odd number `m` is a descender (`(3m+1)/2` even) iff `m` is a term `a(n)`. -/
theorem main :
    ∀ m : ℕ, Odd m → (Even ((3 * m + 1) / 2) ↔ ∃ n : ℕ, m = a n) := by
  sorry

end OMA.S_oeis_a016813
