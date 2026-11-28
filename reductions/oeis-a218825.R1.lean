import OMAStatements.S_oeis_a218825

-- Reduction oeis-a218825.R1 of A218825: 2n - 1 = p + 2q with p, q and p^2 + 60q^2 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a218825: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 349`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 349`. This is the open conjecture.
-/

namespace OMA.R_oeis_a218825_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 8 < n → n ≤ 349 →
    ∃ p q : ℕ, p + 2 * q + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (p ^ 2 + 60 * q ^ 2)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 8 < n → 349 < n →
    ∃ p q : ℕ, p + 2 * q + 1 = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (p ^ 2 + 60 * q ^ 2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a218825.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 349
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a218825_R1
