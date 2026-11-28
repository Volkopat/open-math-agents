import OMAStatements.S_oeis_a231725

-- Reduction oeis-a231725.R1 of A231725: Least positive integer k < n such that n + k + 2^k is prime, or 0 if such an integer k does not exist.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a231725: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 73`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 73`. This is the open conjecture.
-/

namespace OMA.R_oeis_a231725_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 73 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (n + k + 2 ^ k).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 73 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (n + k + 2 ^ k).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a231725.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 73
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a231725_R1
