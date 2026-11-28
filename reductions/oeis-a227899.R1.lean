import OMAStatements.S_oeis_a227899

-- Reduction oeis-a227899.R1 of A227899: Number of primes p < n with 3*p - 4 and n^2 + (n - p)^2 both prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a227899: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 754`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 754`. This is the open conjecture.
-/

namespace OMA.R_oeis_a227899_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 754 →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (3 * p - 4).Prime ∧
      (n ^ 2 + (n - p) ^ 2).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 754 < n →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (3 * p - 4).Prime ∧
      (n ^ 2 + (n - p) ^ 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a227899.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 754
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a227899_R1
