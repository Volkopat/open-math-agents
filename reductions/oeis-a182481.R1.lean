import OMAStatements.S_oeis_a182481

-- Reduction oeis-a182481.R1 of A182481: least k such that 6*k*n - 1 and 6*k*n + 1 are twin primes
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a182481: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1000`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_oeis_a182481_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 1000 →
    ∃ k : ℕ, 0 < k ∧ Nat.Prime (6 * k * n - 1) ∧ Nat.Prime (6 * k * n + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 1000 < n →
    ∃ k : ℕ, 0 < k ∧ Nat.Prime (6 * k * n - 1) ∧ Nat.Prime (6 * k * n + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a182481.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1000
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a182481_R1
