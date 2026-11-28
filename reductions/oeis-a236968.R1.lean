import OMAStatements.S_oeis_a236968

-- Reduction oeis-a236968.R1 of A236968: Number of ordered ways to write n = k + m with k > 0 and m > 0 such that 6*k - 1, 6*k + 1 and k + phi(m) are all prime, where phi(.) is Euler's totient function.
-- Credit: @prathameshnium
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# oeis-a236968: a kernel-checkable initial range, and the open rest

* `H1`: the statement of `main` for `n ≤ 1001`. A finite statement, proved in the Lean kernel by a checked witness table.
* `H2`: the same for every `n > 1001`. This is the open conjecture.
-/

namespace OMA.R_oeis_a236968_R1

/-- The finite range. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → n ≤ 1001 →
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧ (k + Nat.totient m).Prime

/-- The open part. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → 1001 < n →
    ∃ k m : ℕ, 0 < k ∧ 0 < m ∧ k + m = n ∧
      (6 * k - 1).Prime ∧ (6 * k + 1).Prime ∧ (k + Nat.totient m).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a236968.main := by
  intro h1 h2 n hh0
  by_cases h : n ≤ 1001
  · exact h1 n hh0 h
  · exact h2 n hh0 (by omega)

end OMA.R_oeis_a236968_R1
