import OMAStatements.S_oeis_a231557

-- Reduction oeis-a231557.R1 of A231557: Least positive integer k <= n such that 2^k + (n - k) is prime, or 0 if such an integer k does not exist.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a231557: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 162`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 162`. This is the open conjecture.
-/

namespace OMA.R_oeis_a231557_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 162 →
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ (2 ^ k + (n - k)).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 162 < n →
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ (2 ^ k + (n - k)).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a231557.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 162
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a231557_R1
