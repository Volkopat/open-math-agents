import OMAStatements.S_oeis_a261625

-- Reduction oeis-a261625.R1 of A261625: Number of primes p <= n such that (p-1)*n+1 is prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a261625: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a261625_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 1001 →
    ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ ((p - 1) * n + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 1001 < n →
    ∃ p : ℕ, p.Prime ∧ p ≤ n ∧ ((p - 1) * n + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a261625.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a261625_R1
