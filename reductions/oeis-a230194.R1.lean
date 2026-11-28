import OMAStatements.S_oeis_a230194

-- Reduction oeis-a230194.R1 of A230194: Number of ways to write n = x + y + z (x, y, z > 0) such that all the 11 integers 6*x-1, 6*x+1, 6*x-5, 6*x+5, 6*y-1, 6*y-5, 6*y+5, 6*(x+y)+5, 6*z-1, 6*z-5 and 6*z+5 are prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230194: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230194_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 1005 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * x - 5).Prime ∧ (6 * x + 5).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y - 5).Prime ∧ (6 * y + 5).Prime ∧ (6 * (x + y) + 5).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z - 5).Prime ∧ (6 * z + 5).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 1005 < n →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * x - 5).Prime ∧ (6 * x + 5).Prime ∧
      (6 * y - 1).Prime ∧ (6 * y - 5).Prime ∧ (6 * y + 5).Prime ∧ (6 * (x + y) + 5).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z - 5).Prime ∧ (6 * z + 5).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230194.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230194_R1
