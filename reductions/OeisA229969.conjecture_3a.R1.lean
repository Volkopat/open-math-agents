import FormalConjectures.OEIS.«229969»

-- Reduction OeisA229969.conjecture_3a.R1 of A229969 — conjecture 3a
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA229969.conjecture_3a: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 6` is `x + y + z` with `x ∈ {2, 3, 4}` and `2x - 1`, `2y - 1`, `2z - 1`, `2xyz - 1` prime, for `n ≤ 1006`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1006`. This is the open conjecture.
-/

namespace OMA.R_OeisA229969_conjecture_3a_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 6 → n ≤ 1006 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({2, 3, 4} : Finset ℕ) ∧
      (2 * x - 1).Prime ∧ (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y * z - 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 6 → 1006 < n →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({2, 3, 4} : Finset ℕ) ∧
      (2 * x - 1).Prime ∧ (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y * z - 1).Prime

theorem main : H1 → H2 → type_of% @OeisA229969.conjecture_3a := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1006
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA229969_conjecture_3a_R1
