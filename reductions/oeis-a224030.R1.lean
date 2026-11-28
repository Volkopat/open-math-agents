import OMAStatements.S_oeis_a224030

-- Reduction oeis-a224030.R1 of A224030: 0 < k < n with 2n + k and 2n^3 + k^3 both prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a224030: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 217`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 217`. This is the open conjecture.
-/

namespace OMA.R_oeis_a224030_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 217 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * n + k) ∧ Nat.Prime (2 * n ^ 3 + k ^ 3)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → 217 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ Nat.Prime (2 * n + k) ∧ Nat.Prime (2 * n ^ 3 + k ^ 3)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a224030.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 217
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a224030_R1
