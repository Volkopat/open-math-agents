import FormalConjectures.OEIS.«229969»

-- Reduction OeisA229969.conjecture_2.R1 of A229969 — conjecture 2
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA229969.conjecture_2: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 6` is `x + y + z` with `x ∈ {3, 4, 6, 10, 15}` and `2y - 1`, `2z - 1`, `2xy - 1`, `2xz - 1`, `2yz - 1` prime, for `n ≤ 1006`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1006`. This is the open conjecture.
-/

namespace OMA.R_OeisA229969_conjecture_2_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 6 → n ≤ 1006 →
    ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
      (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y - 1).Prime ∧ (2 * x * z - 1).Prime ∧ (2 * y * z - 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 6 → 1006 < n →
    ∃ x y z : ℕ, 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({3, 4, 6, 10, 15} : Finset ℕ) ∧
      (2 * y - 1).Prime ∧ (2 * z - 1).Prime ∧
      (2 * x * y - 1).Prime ∧ (2 * x * z - 1).Prime ∧ (2 * y * z - 1).Prime

theorem main : H1 → H2 → type_of% @OeisA229969.conjecture_2 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1006
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA229969_conjecture_2_R1
