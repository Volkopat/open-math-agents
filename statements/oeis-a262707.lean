import Mathlib

/-!
# A262707: Positive integers m such that pi(k^2)*pi(m^2) is a square for some 1 < k < m

Source: https://oeis.org/A262707
Credit: @gblacher2

`pi(x)` is the number of primes not exceeding `x`, which is Mathlib's `Nat.primeCounting x`.
Zhi-Wei Sun's conjecture in the entry: the sequence has infinitely many terms.
-/

namespace OMA.S_oeis_a262707

/-- There are infinitely many positive integers `m` such that `pi(k^2) * pi(m^2)` is a square for
some `k` with `1 < k < m`. -/
theorem main :
    {m : ℕ | 0 < m ∧ ∃ k : ℕ, 1 < k ∧ k < m ∧
      IsSquare (Nat.primeCounting (k ^ 2) * Nat.primeCounting (m ^ 2))}.Infinite := by
  sorry

end OMA.S_oeis_a262707
