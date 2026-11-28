import OMAStatements.S_oeis_a218654

-- Reduction oeis-a218654.R1 of A218654: n = x + y with 0 < x ≤ y and x^2 + 3xy + y^2 prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a218654: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 892`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 892`. This is the open conjecture.
-/

namespace OMA.R_oeis_a218654_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 892 →
    ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x ^ 2 + 3 * x * y + y ^ 2)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → 892 < n →
    ∃ x y : ℕ, 0 < x ∧ x ≤ y ∧ x + y = n ∧ Nat.Prime (x ^ 2 + 3 * x * y + y ^ 2)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a218654.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 892
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a218654_R1
