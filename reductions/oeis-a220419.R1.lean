import OMAStatements.S_oeis_a220419

-- Reduction oeis-a220419.R1 of A220419: n = x + y with 2x + 1, 2y - 1 and x^3 + 2y^3 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a220419: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 557`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 557`. This is the open conjecture.
-/

namespace OMA.R_oeis_a220419_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 527 < n → n ≤ 557 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (2 * x + 1) ∧ Nat.Prime (2 * y - 1) ∧
        Nat.Prime (x ^ 3 + 2 * y ^ 3)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 527 < n → 557 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ Nat.Prime (2 * x + 1) ∧ Nat.Prime (2 * y - 1) ∧
        Nat.Prime (x ^ 3 + 2 * y ^ 3)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a220419.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 557
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a220419_R1
