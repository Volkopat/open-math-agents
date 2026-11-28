import OMAStatements.S_oeis_a230243

-- Reduction oeis-a230243.R1 of A230243: Number of primes p < n with 3*p + 8 and (p-1)*n + 1 both prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a230243: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1004`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1004`. This is the open conjecture.
-/

namespace OMA.R_oeis_a230243_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 1004 →
    ∃ p : ℕ, p < n ∧ p.Prime ∧ (3 * p + 8).Prime ∧ ((p - 1) * n + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → 1004 < n →
    ∃ p : ℕ, p < n ∧ p.Prime ∧ (3 * p + 8).Prime ∧ ((p - 1) * n + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230243.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1004
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a230243_R1
