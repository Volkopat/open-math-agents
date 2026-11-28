import OMAStatements.S_oeis_a224487

-- Reduction oeis-a224487.R1 of A224487: least b > F(n) with sum_{k=1}^n F(k)*b^(k-1) prime
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a224487: a kernel-checkable initial range, and the open rest

* `H1`: part 1 of the conjecture for `n ≤ 6`. Finite, proved in the Lean kernel by checked witnesses.
* `H2`: part 1 for every `n > 7`. Open.
* `H3`: part 2 (infinitely many prime values for each `n > 1`). Open.
-/

namespace OMA.R_oeis_a224487_R1

open OMA.S_oeis_a224487

/-- The finite range of part 1. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 6 → ∃ b : ℕ, Nat.fib n < b ∧ b < Nat.fib (n + 4) ∧ (S n b).Prime

/-- The open rest of part 1. -/
def H2 : Prop :=
  ∀ n : ℕ, 6 < n → ∃ b : ℕ, Nat.fib n < b ∧ b < Nat.fib (n + 4) ∧ (S n b).Prime

/-- Part 2, unchanged. -/
def H3 : Prop :=
  ∀ n : ℕ, 1 < n → {b : ℕ | Nat.fib n < b ∧ (S n b).Prime}.Infinite

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a224487.main := by
  intro h1 h2 h3
  refine ⟨fun n hn => ?_, h3⟩
  by_cases h : n ≤ 6
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_oeis_a224487_R1
