import Mathlib

/-!
# A001784: Associated Stirling numbers [[2n+3, n]]

Source: https://oeis.org/A001784
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectures:
Let `a(n) = [[2n + 1, n - 1]]` for `n ≥ 2` and `a(0) = a(1) = 0` (the shifted indexing
of A001784 matching the OEIS recurrences, where `a(2) = [[5, 1]] = 24`,
`a(3) = [[7, 2]] = 924`, `a(4) = [[9, 3]] = 26432`, ...).
1. `480*(n+1)*a(n) + 30*(-32*n^2 - 14821*n + 42287)*a(n-1)
    + (878700*n^2 - 403433*n + 5134227)*a(n-2)
    + (911423*n - 656446)*(2*n - 3)*a(n-3) = 0` for `n ≥ 4`.
2. `(n - 2)*(20*n^2 - 5*n - 3)*a(n)
    - n*(2*n + 1)*(20*n^2 + 35*n + 12)*a(n-1) = 0` for `n ≥ 3`.
-/

namespace OMA.S_oeis_a001784

/-- Second-order reciprocal (associated) Stirling number `[[N, k]]`:
number of fixed-point-free permutations of `Fin N` with exactly `k` cycles. -/
noncomputable def assocStirling (N k : ℕ) : ℕ :=
  Nat.card { σ : Equiv.Perm (Fin N) // (∀ x : Fin N, σ x ≠ x) ∧ σ.cycleType.card = k }

/-- Shifted A001784 matching the OEIS recurrence indexing:
`a(n) = [[2n + 1, n - 1]]` for `n ≥ 2`, and `0` for `n < 2`. -/
noncomputable def a (n : ℕ) : ℤ :=
  if n < 2 then 0 else (assocStirling (2 * n + 1) (n - 1) : ℤ)

/-- Both conjectured linear recurrences for A001784. -/
theorem main :
    (∀ n : ℕ, 4 ≤ n →
      480 * ((n : ℤ) + 1) * a n +
        30 * (-32 * (n : ℤ) ^ 2 - 14821 * (n : ℤ) + 42287) * a (n - 1) +
        (878700 * (n : ℤ) ^ 2 - 403433 * (n : ℤ) + 5134227) * a (n - 2) +
        (911423 * (n : ℤ) - 656446) * (2 * (n : ℤ) - 3) * a (n - 3) = 0) ∧
    (∀ n : ℕ, 3 ≤ n →
      ((n : ℤ) - 2) * (20 * (n : ℤ) ^ 2 - 5 * (n : ℤ) - 3) * a n -
        (n : ℤ) * (2 * (n : ℤ) + 1) * (20 * (n : ℤ) ^ 2 + 35 * (n : ℤ) + 12) * a (n - 1) = 0) := by
  sorry

end OMA.S_oeis_a001784
