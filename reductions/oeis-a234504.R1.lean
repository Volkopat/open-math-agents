import OMAStatements.S_oeis_a234504

-- Reduction oeis-a234504.R1 of A234504: Number of ways to write n = k + m with k > 0 and m > 0 such that 2^(phi(k) + phi(m)/4) - 5 is prime, where phi(.) is Euler's totient function.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a234504: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 140`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 140`. This is the open conjecture.
-/

namespace OMA.R_oeis_a234504_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 10 < n → n ≤ 140 →
    ∃ k m e : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      4 * Nat.totient k + Nat.totient m = 4 * e ∧ (2 ^ e - 5).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 10 < n → 140 < n →
    ∃ k m e : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      4 * Nat.totient k + Nat.totient m = 4 * e ∧ (2 ^ e - 5).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a234504.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 140
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a234504_R1
