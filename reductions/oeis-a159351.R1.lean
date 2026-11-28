import OMAStatements.S_oeis_a159351

-- Reduction oeis-a159351.R1 of A159351: Smallest prime of the form a^2 + b^2 with 0 < a < b such that a + b = 2n+1.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a159351: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 633`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 633`. This is the open conjecture.
-/

namespace OMA.R_oeis_a159351_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 633 →
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b = 2 * n + 1 ∧ (a ^ 2 + b ^ 2).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → 633 < n →
    ∃ a b : ℕ, 0 < a ∧ a < b ∧ a + b = 2 * n + 1 ∧ (a ^ 2 + b ^ 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a159351.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 633
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a159351_R1
