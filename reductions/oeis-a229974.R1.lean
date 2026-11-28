import OMAStatements.S_oeis_a229974

-- Reduction oeis-a229974.R1 of A229974: Number of ways to write n = x + y + z (x, y, z > 0) with the six numbers 2*x-1, 2*x+1, 2*x*y-1, 2*x*y+1, 2*x*y*z-1, 2*x*y*z+1 all prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a229974: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 810`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 810`. This is the open conjecture.
-/

namespace OMA.R_oeis_a229974_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 810 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (2 * x - 1).Prime ∧ (2 * x + 1).Prime ∧ (2 * x * y - 1).Prime ∧ (2 * x * y + 1).Prime ∧
      (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 810 < n →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      (2 * x - 1).Prime ∧ (2 * x + 1).Prime ∧ (2 * x * y - 1).Prime ∧ (2 * x * y + 1).Prime ∧
      (2 * x * y * z - 1).Prime ∧ (2 * x * y * z + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a229974.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 810
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a229974_R1
