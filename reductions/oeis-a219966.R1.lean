import OMAStatements.S_oeis_a219966

-- Reduction oeis-a219966.R1 of A219966: n = p + q + (n mod 2)*q with q ≤ n/2 and p, q, q + 6 all prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a219966: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1011`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1011`. This is the open conjecture.
-/

namespace OMA.R_oeis_a219966_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 11 < n → n ≤ 1011 →
    ∃ p q : ℕ, p + q + (n % 2) * q = n ∧ 2 * q ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (q + 6)

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 11 < n → 1011 < n →
    ∃ p q : ℕ, p + q + (n % 2) * q = n ∧ 2 * q ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧
        Nat.Prime (q + 6)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a219966.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1011
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a219966_R1
