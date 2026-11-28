import OMAStatements.S_oeis_a219923

-- Reduction oeis-a219923.R1 of A219923: Number of ways to write n=x+y (x>0, y>0) with x-1, x+1 and 2*x*y+1 all prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a219923: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1623`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1623`. This is the open conjecture.
-/

namespace OMA.R_oeis_a219923_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 623 < n → n ≤ 1623 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
      (x - 1).Prime ∧ (x + 1).Prime ∧ (2 * x * y + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 623 < n → 1623 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
      (x - 1).Prime ∧ (x + 1).Prime ∧ (2 * x * y + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219923.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1623
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a219923_R1
