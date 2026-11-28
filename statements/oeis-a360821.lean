import Mathlib

/-!
# A360821: a prime of the form k^2 + 1 between n^2 and 2n^2

Source: https://oeis.org/A360821

A360821 (offset 1): `a(n)` is the number of primes of the form `k^2+1` between `n^2` and `2*n^2`
exclusive: 0, 1, 1, 1, 1, 1, 0, 1, 1, 2, …  For example `a(20) = 3` since
`400 < 401, 577, 677 < 800`.

Conjecture (Michel Lagneau, Feb 21 2023): except for `n = 7`, between the square of an integer
`n > 1` and the double of its square there is always at least one prime number of the form
`k^2+1`.

The conjecture is stated as: for every `n > 1` with `n ≠ 7` there is a `k` such that `k^2 + 1`
is prime and `n^2 < k^2 + 1 < 2*n^2`.

Conventions: everything is in `ℕ`; both inequalities are strict, as in the sequence definition
(between … exclusive).
-/

namespace OMA.S_oeis_a360821

theorem main :
    ∀ n : ℕ, 1 < n → n ≠ 7 →
      ∃ k : ℕ, Nat.Prime (k ^ 2 + 1) ∧ n ^ 2 < k ^ 2 + 1 ∧ k ^ 2 + 1 < 2 * n ^ 2 := by
  sorry

end OMA.S_oeis_a360821
