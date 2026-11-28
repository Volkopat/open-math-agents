import Mathlib

/-!
# A016777: the Erdős–Sárközy problem on no term dividing the sum of two larger terms

Source: https://oeis.org/A016777
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Erdős–Sárközy, listed in A016777): a set of `n` positive integers with property P
must have some element at least `a(n-1) = 3n - 2`. Property P: for `x, y, z` in the set with
`z < x, y`, `z` does not divide `x + y`.

Conventions:
* `x` and `y` are distinct elements (the "sum of two larger terms" of the problem; Bedert proved
  the statement for all large `n`). `n ≥ 1`.
-/

namespace OMA.S_oeis_a016777

/-- Property P. -/
def PropP (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → z < x → z < y → ¬ z ∣ x + y

theorem main :
    ∀ (n : ℕ) (A : Finset ℕ), 1 ≤ n → A.card = n → (∀ a ∈ A, 0 < a) → PropP A →
      ∃ a ∈ A, 3 * n - 2 ≤ a := by
  sorry

end OMA.S_oeis_a016777
