import OMAStatements.S_oeis_a308028

-- Reduction oeis-a308028.R1 of A308028: the 2-4-6 conjecture on sums of three odd primes
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a308028: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1006`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1006`. This is the open conjecture.
-/

namespace OMA.R_oeis_a308028_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 6 < n → n ≤ 1006 →
    ∃ p q r : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ Nat.Prime q ∧ q ≠ 2 ∧ Nat.Prime r ∧ r ≠ 2 ∧
        p + q + r = 2 * n + 1 ∧ IsSquare (2 * p + 4 * q + 6 * r)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 6 < n → 1006 < n →
    ∃ p q r : ℕ, Nat.Prime p ∧ p ≠ 2 ∧ Nat.Prime q ∧ q ≠ 2 ∧ Nat.Prime r ∧ r ≠ 2 ∧
        p + q + r = 2 * n + 1 ∧ IsSquare (2 * p + 4 * q + 6 * r)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a308028.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1006
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a308028_R1
