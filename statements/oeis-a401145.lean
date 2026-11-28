import Mathlib

/-!
# A401145: partitions of n into distinct parts with n + (product of the parts) prime

Source: https://oeis.org/A401145

A401145 (offset 1): `a(n)` is the number of partitions of `n` into distinct parts such that `n`
plus the product of the parts is prime: 1, 0, 1, 1, 1, 1, 3, 1, 3, 2, …  For example `a(7) = 3`:
the partitions of 7 into distinct parts are `7`, `6+1`, `5+2`, `4+3`, `4+2+1`, with `7 + product`
equal to 14, 13, 17, 19, 15 respectively, and exactly 13, 17 and 19 are prime. Also `a(2) = 0`:
the only partition of 2 into distinct parts is 2 itself, and `2 + 2 = 4` is composite.

Conjecture (Akash Suresh, Oct 16 2026): `a(n) > 0` for all `n` except for `n = 2`. The entry
notes that this holds for `n ≤ 170`.

`a(n) > 0` says exactly that some partition of `n` into distinct parts has `n + product` prime.
The statement is the equivalence, for every `n ≥ 1`: such a partition exists if and only if
`n ≠ 2`. (That `a(2) = 0` is a one-line computation, shown in the entry's example; the open
content is the existence for all other `n`.)

Conventions: a partition of `n` into distinct parts is a finite set `s` of positive integers
with sum `n` (`Finset ℕ`), and the product of the parts is `∏ x ∈ s, x`.
-/

namespace OMA.S_oeis_a401145

theorem main :
    ∀ n : ℕ, 0 < n →
      ((∃ s : Finset ℕ, (∀ x ∈ s, 0 < x) ∧ ∑ x ∈ s, x = n ∧ Nat.Prime (n + ∏ x ∈ s, x)) ↔
        n ≠ 2) := by
  sorry

end OMA.S_oeis_a401145
