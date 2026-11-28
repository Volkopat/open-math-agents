import OMAStatements.S_oeis_a360821

-- Reduction oeis-a360821.R1 of A360821: a prime of the form k^2 + 1 between n^2 and 2n^2
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a360821: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 886`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 886`. This is the open conjecture.
-/

namespace OMA.R_oeis_a360821_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≠ 7 → n ≤ 886 →
    ∃ k : ℕ, Nat.Prime (k ^ 2 + 1) ∧ n ^ 2 < k ^ 2 + 1 ∧ k ^ 2 + 1 < 2 * n ^ 2

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → n ≠ 7 → 886 < n →
    ∃ k : ℕ, Nat.Prime (k ^ 2 + 1) ∧ n ^ 2 < k ^ 2 + 1 ∧ k ^ 2 + 1 < 2 * n ^ 2

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a360821.main := by
  intro h1 h2 n hh0 hh1
  by_cases h : n ≤ 886
  · exact h1 n hh0 hh1 h
  · exact h2 n hh0 hh1 (by omega)

end OMA.R_oeis_a360821_R1
