import OMAStatements.S_oeis_a035050

-- Reduction oeis-a035050.R1 of OEIS A035050: Smallest k Such That k * 2^n + 1 Is Prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a035050: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 30`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 30`. This is the open conjecture.
-/

namespace OMA.R_oeis_a035050_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → n ≤ 30 →
    ∃ k : ℕ, 1 ≤ k ∧ k < 2 ^ n ∧ Nat.Prime (k * 2 ^ n + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → 30 < n →
    ∃ k : ℕ, 1 ≤ k ∧ k < 2 ^ n ∧ Nat.Prime (k * 2 ^ n + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a035050.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 30
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a035050_R1
