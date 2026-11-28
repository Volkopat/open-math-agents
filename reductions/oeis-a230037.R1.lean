import OMAStatements.S_oeis_a230037

-- Reduction oeis-a230037.R1 of A230037: Number of ways to write n = x + y + z (0 < x <= y <= z) such that the four pairs {6*x-1, 6*x+1}, {6*y-1, 6*y+1}, {6*z-1, 6*z+1} and {6*x*y-1, 6*x*y+1} are twin prime pairs.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230037: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1002`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1002`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230037_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n ≤ 1002 →
    ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z + 1).Prime ∧ (6 * x * y - 1).Prime ∧ (6 * x * y + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 < n → 1002 < n →
    ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y ≤ z ∧ x + y + z = n ∧
      (6 * x - 1).Prime ∧ (6 * x + 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime ∧
      (6 * z - 1).Prime ∧ (6 * z + 1).Prime ∧ (6 * x * y - 1).Prime ∧ (6 * x * y + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230037.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1002
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230037_R1
