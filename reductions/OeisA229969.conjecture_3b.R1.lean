import FormalConjectures.OEIS.«229969»

-- Reduction OeisA229969.conjecture_3b.R1 of A229969 — conjecture 3b
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA229969.conjecture_3b: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 2` is `x + y + z` with `x ∈ {1, 2, 3}` and `2x + 1`, `2y + 1`, `2z + 1`, `2xyz + 1` prime, for `n ≤ 1002`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1002`. This is the open conjecture.
-/

namespace OMA.R_OeisA229969_conjecture_3b_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 2 → n ≤ 1002 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 3} : Finset ℕ) ∧
      (2 * x + 1).Prime ∧ (2 * y + 1).Prime ∧ (2 * z + 1).Prime ∧
      (2 * x * y * z + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 2 → 1002 < n →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 3} : Finset ℕ) ∧
      (2 * x + 1).Prime ∧ (2 * y + 1).Prime ∧ (2 * z + 1).Prime ∧
      (2 * x * y * z + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA229969.conjecture_3b := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1002
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA229969_conjecture_3b_R1
