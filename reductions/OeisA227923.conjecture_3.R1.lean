import FormalConjectures.OEIS.«227923»

-- Reduction OeisA227923.conjecture_3.R1 of A227923 — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA227923.conjecture_3: a kernel-checkable initial range, and the open rest

* `H1`: every `n > 1` is `x + y` with `6x - 1`, `12x - 1`, `6y + 1`, `6y + 5` all prime, for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_OeisA227923_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 1 → n ≤ 1001 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n > 1 → 1001 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧
      (6 * x - 1).Prime ∧ (12 * x - 1).Prime ∧ (6 * y + 1).Prime ∧ (6 * y + 5).Prime

theorem main : H1 → H2 → type_of% @OeisA227923.conjecture_3 := by
  intro h1 h2 n hn
  by_cases h : n ≤ 1001
  · exact h1 n hn h
  · exact h2 n hn (by omega)

end OMA.R_OeisA227923_conjecture_3_R1
