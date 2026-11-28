import OMAStatements.S_oeis_a020735

-- Reduction oeis-a020735.R1 of A020735: Odd numbers >= 5.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a020735: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1004`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1004`. This is the open conjecture.
-/

namespace OMA.R_oeis_a020735_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 5 ≤ n → n ≤ 1004 →
    ∃ m p : ℕ, Nat.Prime p ∧ n = m ^ 2 + m + p

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 2 = 1 → 5 ≤ n → 1004 < n →
    ∃ m p : ℕ, Nat.Prime p ∧ n = m ^ 2 + m + p

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a020735.main := by
  intro h1 h2 n hh0 hh1
  by_cases h : n ≤ 1004
  · exact h1 n hh0 hh1 h
  · exact h2 n hh0 hh1 (by omega)

end OMA.R_oeis_a020735_R1
