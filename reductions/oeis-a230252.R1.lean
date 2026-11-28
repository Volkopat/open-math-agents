import OMAStatements.S_oeis_a230252

-- Reduction oeis-a230252.R1 of A230252: Number of ways to write n = x + y (x, y > 0) with 2*x + 1, x^2 + x + 1 and y^2 + y + 1 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230252: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 890`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 890`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230252_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 890 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x + 1).Prime ∧ (x ^ 2 + x + 1).Prime ∧ (y ^ 2 + y + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 890 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
    (2 * x + 1).Prime ∧ (x ^ 2 + x + 1).Prime ∧ (y ^ 2 + y + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230252.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 890
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230252_R1
