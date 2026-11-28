import OMAStatements.S_oeis_a087243

-- Reduction oeis-a087243.R1 of A087243: Primes arising as n + A087242(n)
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a087243: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1000`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_oeis_a087243_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → Even n → n ≤ 1000 →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → Even n → 1000 < n →
    ∃ p : ℕ, p.Prime ∧ n < p ∧ (p - n).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a087243.main := by
  intro h1 h2 n hh0 hh1
  by_cases h : n ≤ 1000
  · exact h1 n hh0 hh1 h
  · exact h2 n hh0 hh1 (by omega)

end OMA.R_oeis_a087243_R1
