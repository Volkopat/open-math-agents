import FormalConjectures.OEIS.«229969»

-- Reduction OeisA229969.conjecture_5b.R1 of A229969 — conjecture 5b
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA229969.conjecture_5b: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 2`, `n ≠ 16`, is `x + y + z` with `x ∈ {1, 2, 6}` and `xy + 1`, `xz + 1`, `yz + 1` prime, for `n ≤ 1002`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1002`. This is the open conjecture.
-/

namespace OMA.R_OeisA229969_conjecture_5b_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 2 → n ≠ 16 → n ≤ 1002 →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 6} : Finset ℕ) ∧
      (x * y + 1).Prime ∧ (x * z + 1).Prime ∧ (y * z + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 2 → n ≠ 16 → 1002 < n →
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x + y + z = n ∧
      x ∈ ({1, 2, 6} : Finset ℕ) ∧
      (x * y + 1).Prime ∧ (x * z + 1).Prime ∧ (y * z + 1).Prime

theorem main : H1 → H2 → type_of% @OeisA229969.conjecture_5b := by
  intro h1 h2 n hn hne
  by_cases h : n ≤ 1002
  · exact h1 n hn hne h
  · exact h2 n hn hne (by omega)

end OMA.R_OeisA229969_conjecture_5b_R1
