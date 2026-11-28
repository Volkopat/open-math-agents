import Mathlib

namespace OMA.S_oeis_a166103

/-- OEIS A166100(`n`): sum of positive integers `1 ≤ i ≤ 2*n + 1` with Jacobi symbol `J(i, 2*n + 1) = 1`. -/
def a166100 (n : ℕ) : ℕ :=
  ∑ i ∈ (Finset.Icc 1 (2 * n + 1)).filter (fun (i : ℕ) => jacobiSym (i : ℤ) (2 * n + 1) = 1), i

/-- OEIS A166104 membership: positive integers whose prime factors are all congruent to `3` or `5` mod `6`. -/
def IsA166104 (m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ p : ℕ, p.Prime → p ∣ m → p % 6 = 3 ∨ p % 6 = 5

/-- OEIS A166103 membership: squares of terms of `A166104`. -/
def IsA166103 (x : ℕ) : Prop :=
  ∃ m : ℕ, IsA166104 m ∧ x = m ^ 2

/-- OEIS A166102 membership: odd integers `k` such that `A166100((k - 1) / 2) / k` is not an integer. -/
def IsA166102 (k : ℕ) : Prop :=
  Odd k ∧ ¬ k ∣ a166100 ((k - 1) / 2)

/-- OEIS A166103 Conjecture: `A166103(n) = A166102(n) / 3` for all `n ≥ 1`, i.e.,
every term of `A166102` is divisible by `3`, and `x` is a term of `A166103` if and only if
`3 * x` is a term of `A166102`. -/
theorem main :
    (∀ k : ℕ, IsA166102 k → 3 ∣ k) ∧
    (∀ x : ℕ, IsA166103 x ↔ IsA166102 (3 * x)) := by
  sorry

end OMA.S_oeis_a166103
