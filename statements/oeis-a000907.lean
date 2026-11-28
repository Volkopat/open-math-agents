import Mathlib

/-!
# A000907: Associated Stirling numbers [[2n+2, n]]

Source: https://oeis.org/A000907
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let `a(n) = [[2n+4, n+1]]` (the 0-indexed version of A000907, with `a(0) = [[4, 1]] = 6`,
`a(1) = [[6, 2]] = 130`, `a(2) = [[8, 3]] = 2380`, ...), where `[[N, k]]` is the number of
`k`-orbit permutations of an `N`-set with at least 2 elements per orbit.
Then for all `n ≥ 1`:
`n * (4*n + 5) * a(n) - (2*n + 3) * (n + 2) * (4*n + 9) * a(n - 1) = 0`.
-/

namespace OMA.S_oeis_a000907

/-- Second-order reciprocal (associated) Stirling number `[[N, k]]`:
number of fixed-point-free permutations of `Fin N` with exactly `k` cycles. -/
noncomputable def assocStirling (N k : ℕ) : ℕ :=
  Nat.card { σ : Equiv.Perm (Fin N) // (∀ x : Fin N, σ x ≠ x) ∧ σ.cycleType.card = k }

/-- 0-indexed A000907: `a(n) = [[2n+4, n+1]]` (`a(0) = 6`, `a(1) = 130`, `a(2) = 2380`, ...). -/
noncomputable def a (n : ℕ) : ℤ :=
  (assocStirling (2 * n + 4) (n + 1) : ℤ)

/-- Conjectured first-order recurrence for A000907. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (n : ℤ) * (4 * (n : ℤ) + 5) * a n -
        (2 * (n : ℤ) + 3) * ((n : ℤ) + 2) * (4 * (n : ℤ) + 9) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a000907
