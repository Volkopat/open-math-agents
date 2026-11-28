import Mathlib

/-!
# OEIS A109925: Number of primes of the form n - 2^k

Source: https://oeis.org/A109925
Credit: @unserus

OEIS: "Erdős conjectures that the numbers in A039669 are the only n for which
n-2^r is prime for all 1<2^r<n."

A039669 = 4, 7, 15, 21, 45, 75, 105 lists the numbers `n > 2` such that
`n - 2^r` is prime for every `r ≥ 1` with `2^r < n` (for `n ≤ 2` the condition
is vacuous, and those `n` are not in A039669). The conjecture is that these
seven numbers are the only ones. The subtraction is in `ℕ`; it does not
truncate because `2^r < n`. (Upstream, Erdős Problem 1142 asks the weaker
question of whether there are infinitely many such `n`.)
-/

namespace OMA.S_oeis_a109925

/-- The numbers `n > 2` such that `n - 2^r` is prime for all `r ≥ 1` with
`2^r < n`. -/
def erdosSet : Set ℕ :=
  {n | 2 < n ∧ ∀ r : ℕ, 1 ≤ r → 2 ^ r < n → (n - 2 ^ r).Prime}

/-- The only such `n` are 4, 7, 15, 21, 45, 75 and 105 (A039669). -/
theorem main : erdosSet = {4, 7, 15, 21, 45, 75, 105} := by
  sorry

end OMA.S_oeis_a109925
