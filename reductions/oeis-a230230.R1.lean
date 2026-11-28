import OMAStatements.S_oeis_a230230

-- Reduction oeis-a230230.R1 of A230230: 2n = p + q with p, q, 3p - 10, 3q + 10 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230230: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1003`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1003`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230230_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 3 < n → n ≤ 1003 →
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime (3 * p - 10) ∧
        Nat.Prime (3 * q + 10)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 3 < n → 1003 < n →
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime (3 * p - 10) ∧
        Nat.Prime (3 * q + 10)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230230.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1003
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230230_R1
