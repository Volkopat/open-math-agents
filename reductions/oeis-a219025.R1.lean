import OMAStatements.S_oeis_a219025

-- Reduction oeis-a219025.R1 of A219025: primes p < n with 6n - p and 6n + p both prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a219025: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a219025_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 6 ≤ n → n ≤ 1005 →
    ∃ p : ℕ, p < n ∧ Nat.Prime p ∧ Nat.Prime (6 * n - p) ∧ Nat.Prime (6 * n + p)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 6 ≤ n → 1005 < n →
    ∃ p : ℕ, p < n ∧ Nat.Prime p ∧ Nat.Prime (6 * n - p) ∧ Nat.Prime (6 * n + p)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219025.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a219025_R1
