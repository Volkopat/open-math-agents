import Mathlib

/-!
# OEIS A034878 versus the Jordan–Pólya numbers

Source: https://oeis.org/A034878
`A034878`: numbers `k` such that `k!` is a product of smaller factorials
(1, 4, 6, 8, 9, 10, 12, 16, …). Conjecture: except for the numbers `2`, `9` and `10` this
sequence is the same as `A001013` (the Jordan–Pólya numbers, products of factorials). That is,
`A034878 = (A001013 \ {2}) ∪ {9, 10}`.

Conventions. `k ≥ 1`. "`k!` is a product of smaller factorials" means `k! = ∏ mᵢ!` for a
finite list of `mᵢ < k` (the empty product covers `k = 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a034878

/-- `k!` is a product of factorials of numbers smaller than `k`. -/
def InA034878 (k : ℕ) : Prop :=
  ∃ l : List ℕ, (∀ m ∈ l, m < k) ∧ (l.map Nat.factorial).prod = k.factorial

/-- Jordan–Pólya numbers: products of factorials. -/
def IsJordanPolya (k : ℕ) : Prop := ∃ l : List ℕ, (l.map Nat.factorial).prod = k

theorem main :
    ∀ k : ℕ, 1 ≤ k → (InA034878 k ↔ (IsJordanPolya k ∧ k ≠ 2) ∨ k = 9 ∨ k = 10) := by
  sorry

end OMA.S_oeis_a034878
