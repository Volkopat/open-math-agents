import OMAStatements.S_oeis_a187757

-- Reduction oeis-a187757.R1 of A187757: Number of ways to write n=x+y (x,y>0) with 6x-1, 6x+1, 6y+1 and 6y+5 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a187757: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a187757_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 1001 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 1001 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a187757.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a187757_R1
