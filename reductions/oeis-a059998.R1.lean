import OMAStatements.S_oeis_a059998

-- Reduction oeis-a059998.R1 of OEIS A059998: Primes occurring in ternary Goldbach representations
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a059998: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a059998_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 1005 →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 1005 < n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a059998.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a059998_R1
