import OMAStatements.S_oeis_a144559

-- Reduction oeis-a144559.R1 of A144559: a(n) = number of triples [i,j,k] with i+j+k = n, i an odd prime, j an odd Fibonacci number and k a positive Fibonacci number.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a144559: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1004`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1004`. This is the open conjecture.
-/

namespace OMA.R_oeis_a144559_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 4 < n → n ≤ 1004 →
    ∃ p a b : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (Nat.fib a) ∧ 0 < Nat.fib b ∧
      p + Nat.fib a + Nat.fib b = n

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 4 < n → 1004 < n →
    ∃ p a b : ℕ, p.Prime ∧ p ≠ 2 ∧ Odd (Nat.fib a) ∧ 0 < Nat.fib b ∧
      p + Nat.fib a + Nat.fib b = n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a144559.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1004
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a144559_R1
