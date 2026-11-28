import OMAStatements.S_oeis_a249061

-- Reduction oeis-a249061.R1 of A249061: a(n) is the least number of successive numbers 1, 2, 3, ... which when added to n produce a prime number.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a249061: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 999`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 999`. This is the open conjecture.
-/

namespace OMA.R_oeis_a249061_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 999 →
    ∃ k : ℕ, 0 < k ∧ (n + k * (k + 1) / 2).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 999 < n →
    ∃ k : ℕ, 0 < k ∧ (n + k * (k + 1) / 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a249061.main := by
  intro h1 h2 n 
  by_cases h : n ≤ 999
  · exact h1 n  h
  · exact h2 n  (by omega)

end OMA.R_oeis_a249061_R1
