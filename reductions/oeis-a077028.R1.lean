import OMAStatements.S_oeis_a077028

-- Reduction oeis-a077028.R1 of A077028: Primes in every row of the rascal triangle except rows 0, 1, 6, 30, and 54
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a077028: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 999`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 999`. This is the open conjecture.
-/

namespace OMA.R_oeis_a077028_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, n ≠ 0 → n ≠ 1 → n ≠ 6 → n ≠ 30 → n ≠ 54 → n ≤ 999 →
    ∃ k : ℕ, k ≤ n ∧ Nat.Prime (k * (n - k) + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, n ≠ 0 → n ≠ 1 → n ≠ 6 → n ≠ 30 → n ≠ 54 → 999 < n →
    ∃ k : ℕ, k ≤ n ∧ Nat.Prime (k * (n - k) + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a077028.main := by
  intro h1 h2 n hh0 hh1 hh2 hh3 hh4
  by_cases h : n ≤ 999
  · exact h1 n hh0 hh1 hh2 hh3 hh4 h
  · exact h2 n hh0 hh1 hh2 hh3 hh4 (by omega)

end OMA.R_oeis_a077028_R1
