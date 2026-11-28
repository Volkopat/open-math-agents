import OMAStatements.S_oeis_a237184

-- Reduction oeis-a237184.R1 of A237184: Number of ordered ways to write n = (1+(n mod 2))*p + q with p, q, phi(p+1) - 1 and phi(q-1) + 1 all prime.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a237184: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1023`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1023`. This is the open conjecture.
-/

namespace OMA.R_oeis_a237184_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 23 < n → n ≤ 1023 →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = (1 + n % 2) * p + q ∧
      (Nat.totient (p + 1) - 1).Prime ∧ (Nat.totient (q - 1) + 1).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 23 < n → 1023 < n →
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = (1 + n % 2) * p + q ∧
      (Nat.totient (p + 1) - 1).Prime ∧ (Nat.totient (q - 1) + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a237184.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1023
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a237184_R1
