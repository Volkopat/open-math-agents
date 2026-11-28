import OMAStatements.S_oeis_a237531

-- Reduction oeis-a237531.R1 of A237531: 0 < k < n/2 with phi(k*(n-k)) - 1 and phi(k*(n-k)) + 1 both prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a237531: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1005`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1005`. This is the open conjecture.
-/

namespace OMA.R_oeis_a237531_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 5 < n → n ≤ 1005 →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ Nat.Prime (Nat.totient (k * (n - k)) - 1) ∧
        Nat.Prime (Nat.totient (k * (n - k)) + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 5 < n → 1005 < n →
    ∃ k : ℕ, 0 < k ∧ 2 * k < n ∧ Nat.Prime (Nat.totient (k * (n - k)) - 1) ∧
        Nat.Prime (Nat.totient (k * (n - k)) + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a237531.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1005
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a237531_R1
