import OMAStatements.S_oeis_a240233

-- Reduction oeis-a240233.R1 of A240233: smallest prime p such that p + 6n and p + 12n are both prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a240233: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1000`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1000`. This is the open conjecture.
-/

namespace OMA.R_oeis_a240233_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n ≤ 1000 →
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 6 * n) ∧ Nat.Prime (p + 12 * n)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → 1000 < n →
    ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 6 * n) ∧ Nat.Prime (p + 12 * n)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a240233.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1000
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a240233_R1
