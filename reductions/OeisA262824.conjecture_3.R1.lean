import FormalConjectures.OEIS.«262824»

-- Reduction OeisA262824.conjecture_3.R1 of A262824 — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# OeisA262824.conjecture_3: a kernel-checkable initial range, and the open rest

* `H1`: every `n` is `w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4`, for `n ≤ 4999`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 4999`. This is the open conjecture.
-/

namespace OMA.R_OeisA262824_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≤ 4999 →
    ∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4999 < n →
    ∃ w x y z : ℕ, n = w ^ 2 + x ^ 3 + 2 * y ^ 3 + 3 * z ^ 4

theorem main : H1 → H2 → type_of% @OeisA262824.conjecture_3 := by
  intro h1 h2 n 
  by_cases h : n ≤ 4999
  · exact h1 n  h
  · exact h2 n  (by omega)

end OMA.R_OeisA262824_conjecture_3_R1
