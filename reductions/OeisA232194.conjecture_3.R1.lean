import FormalConjectures.OEIS.«232194»

-- Reduction OeisA232194.conjecture_3.R1 of Ways to write $n = x + y$ with $nx + y$ and $ny - x$ both prime — conjecture 3
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Conjecture 3 of A232194: a kernel-checkable initial range, and the open rest

* `H1`: for `0 < n ≤ 1000`, `n ∉ {1, 30, 54}`, there are `x, y > 0` with `x + y = n` and both
  `n * x + y` and `n * y + x` prime. A finite statement, checkable inside the Lean kernel by a
  verified trial-division search.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_OeisA232194_conjecture_3_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n > 0 → n ≤ 1000 → n ∉ ({1, 30, 54} : Finset ℕ) →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x + y).Prime ∧ (n * y + x).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000 < n →
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x + y = n ∧ (n * x + y).Prime ∧ (n * y + x).Prime

theorem main : H1 → H2 → type_of% @OeisA232194.conjecture_3 := by
  intro h1 h2 n hn hne
  by_cases h : n ≤ 1000
  · exact h1 n hn h hne
  · exact h2 n (by omega)

end OMA.R_OeisA232194_conjecture_3_R1
