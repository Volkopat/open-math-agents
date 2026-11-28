import OMAStatements.S_oeis_a227898

-- Reduction oeis-a227898.R1 of A227898: Number of primes p < n with p + 6 and n + (n - p)^2 both prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a227898: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 906`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 906`. This is the open conjecture.
-/

namespace OMA.R_oeis_a227898_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 906 →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (p + 6).Prime ∧ (n + (n - p) ^ 2).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 906 < n →
    ∃ p : ℕ, p.Prime ∧ p < n ∧ (p + 6).Prime ∧ (n + (n - p) ^ 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a227898.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 906
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a227898_R1
