import OMAStatements.S_oeis_a124867

-- Reduction oeis-a124867.R1 of A124867: Numbers that are the sum of 3 distinct primes.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a124867: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1017`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1017`. This is the open conjecture.
-/

namespace OMA.R_oeis_a124867_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 17 < n → n ≤ 1017 →
    ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p < q ∧ q < r ∧ p + q + r = n

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 17 < n → 1017 < n →
    ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p < q ∧ q < r ∧ p + q + r = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a124867.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1017
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a124867_R1
