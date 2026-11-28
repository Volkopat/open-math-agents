import OMAStatements.S_oeis_a061357

-- Reduction oeis-a061357.R1 of A061357: Number of 0<k<n such that n-k and n+k are both primes.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a061357: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1003`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1003`. This is the open conjecture.
-/

namespace OMA.R_oeis_a061357_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ 1003 →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (n - k).Prime ∧ (n + k).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 ≤ n → 1003 < n →
    ∃ k : ℕ, 0 < k ∧ k < n ∧ (n - k).Prime ∧ (n + k).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a061357.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1003
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a061357_R1
