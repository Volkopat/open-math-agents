import OMAStatements.S_oeis_a232109

-- Reduction oeis-a232109.R1 of A232109: Least prime p < n + 5 with n + (p-1)*(p-3)/8 prime, or 0 if such a prime p does not exist.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a232109: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1000`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_oeis_a232109_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 1000 →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < n + 5 ∧
      (n + (p - 1) * (p - 3) / 8).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 1000 < n →
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p < n + 5 ∧
      (n + (p - 1) * (p - 3) / 8).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a232109.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1000
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a232109_R1
