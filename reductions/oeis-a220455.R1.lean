import OMAStatements.S_oeis_a220455

-- Reduction oeis-a220455.R1 of A220455: Number of ways to write n=x+y (x>0, y>0) with 3x-2, 3x+2 and 2xy+1 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a220455: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1007`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1007`. This is the open conjecture.
-/

namespace OMA.R_oeis_a220455_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 7 < n → n ≤ 1007 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (3 * x - 2).Prime ∧ (3 * x + 2).Prime ∧ (2 * x * y + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → 1007 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (3 * x - 2).Prime ∧ (3 * x + 2).Prime ∧ (2 * x * y + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a220455.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1007
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a220455_R1
