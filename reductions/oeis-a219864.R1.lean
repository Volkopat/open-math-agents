import OMAStatements.S_oeis_a219864

-- Reduction oeis-a219864.R1 of A219864: n = p + q with p and 2pq + 1 both prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a219864: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1007`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1007`. This is the open conjecture.
-/

namespace OMA.R_oeis_a219864_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 7 < n → n ≤ 1007 →
    ∃ p q : ℕ, p + q = n ∧ Nat.Prime p ∧ Nat.Prime (2 * p * q + 1)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 7 < n → 1007 < n →
    ∃ p q : ℕ, p + q = n ∧ Nat.Prime p ∧ Nat.Prime (2 * p * q + 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219864.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1007
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a219864_R1
