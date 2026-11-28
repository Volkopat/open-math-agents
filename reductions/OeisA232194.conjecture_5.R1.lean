import FormalConjectures.OEIS.«232194»

-- Reduction OeisA232194.conjecture_5.R1 of Ways to write $n = x + y$ with $nx + y$ and $ny - x$ both prime — conjecture 5
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Conjecture 5 of A232194: a kernel-checkable initial range, and the open rest

* `H1`: for `1 < n ≤ 1000`, `n ≠ 8`, there are `x, y > 0` with `x + y = n` and `x ^ 4 + n * y`
  prime. A finite statement, checkable inside the Lean kernel by a verified trial-division search.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_OeisA232194_conjecture_5_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 1 → n ≤ 1000 → n ≠ 8 →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + n * y).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (x ^ 4 + n * y).Prime

theorem main : H1 → H2 → type_of% @OeisA232194.conjecture_5 := by
  intro h1 h2 n hn hne
  by_cases h : n ≤ 1000
  · exact h1 n hn h hne
  · exact h2 n (by omega)

end OMA.R_OeisA232194_conjecture_5_R1
