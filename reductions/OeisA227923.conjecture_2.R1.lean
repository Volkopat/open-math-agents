import FormalConjectures.OEIS.«227923»

-- Reduction OeisA227923.conjecture_2.R1 of A227923 — conjecture 2
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA227923.conjecture_2: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 4`, `n ≠ 13`, is `x + y`, `1 < x ≠ y > 1`, with `6x - 1`, `12x - 1`, `6y - 1`, `6y + 1` prime, for `n ≤ 1004`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1004`. This is the open conjecture.
-/

namespace OMA.R_OeisA227923_conjecture_2_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 4 → n ≠ 13 → n ≤ 1004 →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 4 → n ≠ 13 → 1004 < n →
    ∃ x y : ℕ, 1 < x ∧ 1 < y ∧ x ≠ y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y - 1).Prime ∧ (6 * y + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA227923.conjecture_2 := by
  intro h1 h2 n hn h13
  by_cases h : n ≤ 1004
  · exact h1 n hn h13 h
  · exact h2 n hn h13 (by omega)

end OMA.R_OeisA227923_conjecture_2_R1
