import OMAStatements.S_oeis_a187758

-- Reduction oeis-a187758.R1 of A187758: Number of ways to write n=x+y (x,y>0) with 2x-3, 2x+3, 6y+1 and 6y+5 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a187758: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1004`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1004`. This is the open conjecture.
-/

namespace OMA.R_oeis_a187758_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 1004 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x - 3).Prime ∧ (2 * x + 3).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → 1004 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x - 3).Prime ∧ (2 * x + 3).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a187758.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1004
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a187758_R1
