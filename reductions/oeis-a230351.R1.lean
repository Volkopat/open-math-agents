import OMAStatements.S_oeis_a230351

-- Reduction oeis-a230351.R1 of A230351: Number of ordered ways to write n = p + q (q > 0) with p, 2*p^2 - 1 and 2*q^2 - 1 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230351: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 750`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 750`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230351_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 750 →
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧
    p.Prime ∧ (2 * p ^ 2 - 1).Prime ∧ (2 * q ^ 2 - 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 750 < n →
    ∃ p q : ℕ, 0 < q ∧ p + q = n ∧
    p.Prime ∧ (2 * p ^ 2 - 1).Prime ∧ (2 * q ^ 2 - 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230351.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 750
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230351_R1
