import OMAStatements.S_oeis_a014091

-- Reduction oeis-a014091.R1 of A014091: Numbers that are the sum of 2 primes.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a014091: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1002`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1002`. This is the open conjecture.
-/

namespace OMA.R_oeis_a014091_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n → n % 2 = 0 → n ≤ 1002 →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 < n → n % 2 = 0 → 1002 < n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a014091.main := by
  intro h1 h2 n hh0 hh1
  by_cases h : n ≤ 1002
  · exact h1 n hh0 hh1 h
  · exact h2 n hh0 hh1 (by omega)

end OMA.R_oeis_a014091_R1
