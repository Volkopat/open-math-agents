import OMAStatements.S_oeis_a227909

-- Reduction oeis-a227909.R1 of A227909: 2n = p + q with p, q and (p-1)*(q+1) - 1 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a227909: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a227909_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 1001 →
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime ((p - 1) * (q + 1) - 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 1001 < n →
    ∃ p q : ℕ, p + q = 2 * n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime ((p - 1) * (q + 1) - 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a227909.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a227909_R1
