import OMAStatements.S_oeis_a303702

-- Reduction oeis-a303702.R1 of A303702: even numbers as a prime plus a power of 2 plus a power of 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a303702: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a303702_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 1001 →
    ∃ p k m : ℕ, Nat.Prime p ∧ p + 2 ^ k + 3 ^ m = 2 * n

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 1001 < n →
    ∃ p k m : ℕ, Nat.Prime p ∧ p + 2 ^ k + 3 ^ m = 2 * n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a303702.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a303702_R1
