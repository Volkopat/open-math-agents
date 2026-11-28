import OMAStatements.S_oeis_a047949

-- Reduction oeis-a047949.R1 of OEIS A047949: Largest m such that n - m and n + m are both primes
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a047949: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a047949_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ≤ n → n ≤ 1001 →
    ∃ m : ℕ, m ≤ n ∧ Nat.Prime (n - m) ∧ Nat.Prime (n + m)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 ≤ n → 1001 < n →
    ∃ m : ℕ, m ≤ n ∧ Nat.Prime (n - m) ∧ Nat.Prime (n + m)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a047949.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a047949_R1
