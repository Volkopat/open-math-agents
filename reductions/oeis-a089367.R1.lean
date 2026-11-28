import OMAStatements.S_oeis_a089367

-- Reduction oeis-a089367.R1 of OEIS A089367: smallest prime p with np + 1 prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a089367: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a089367_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n → n ≤ 1001 →
    ∃ p : ℕ, p.Prime ∧ (n * p + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → Even n → 1001 < n →
    ∃ p : ℕ, p.Prime ∧ (n * p + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a089367.main := by
  intro h1 h2 n hh0 hh1
  by_cases h : n ≤ 1001
  · exact h1 n hh0 hh1 h
  · exact h2 n hh0 hh1 (by omega)

end OMA.R_oeis_a089367_R1
