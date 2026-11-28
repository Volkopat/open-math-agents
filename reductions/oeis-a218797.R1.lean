import OMAStatements.S_oeis_a218797

-- Reduction oeis-a218797.R1 of A218797: 2n - 1 = p + q + r with p, q, r and p^2 + q^2 + r^2 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a218797: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1828`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1828`. This is the open conjecture.
-/

namespace OMA.R_oeis_a218797_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1715 ≤ n → n ≤ 1828 →
    ∃ p q r : ℕ, p ≤ q ∧ q ≤ r ∧ p + q + r + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime r ∧ Nat.Prime (p ^ 2 + q ^ 2 + r ^ 2)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1715 ≤ n → 1828 < n →
    ∃ p q r : ℕ, p ≤ q ∧ q ≤ r ∧ p + q + r + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime r ∧ Nat.Prime (p ^ 2 + q ^ 2 + r ^ 2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a218797.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1828
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a218797_R1
