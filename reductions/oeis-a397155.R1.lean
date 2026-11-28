import OMAStatements.S_oeis_a397155

-- Reduction oeis-a397155.R1 of Cubes as a semiprime plus a prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a397155: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 250`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 250`. This is the open conjecture.
-/

namespace OMA.R_oeis_a397155_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 250 →
    ∃ p q r : ℕ,
    p.Prime ∧ q.Prime ∧ r.Prime ∧ n ^ 3 = p * q + r

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 250 < n →
    ∃ p q r : ℕ,
    p.Prime ∧ q.Prime ∧ r.Prime ∧ n ^ 3 = p * q + r

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a397155.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 250
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a397155_R1
