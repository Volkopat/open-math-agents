import OMAStatements.S_oeis_a228431

-- Reduction oeis-a228431.R1 of A228431: Number of ordered ways to write n = x + y (x, y > 0) with p(3, x) + p(6, y) prime, where p(3, k) denotes the triangular number k*(k+1)/2 and p(6, k) denotes the hexagonal number k*(2*k-1) = p(3, 2*k-1).
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a228431: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 764`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 764`. This is the open conjecture.
-/

namespace OMA.R_oeis_a228431_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 764 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
        (x * (x + 1) / 2 + y * (2 * y - 1)).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 764 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
        (x * (x + 1) / 2 + y * (2 * y - 1)).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a228431.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 764
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a228431_R1
