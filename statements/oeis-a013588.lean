import Mathlib

/-!
# A013588: smallest positive integer not a `{0,1}`-determinant

Source: https://oeis.org/A013588
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A013588): the sequence of maximal determinants of `n × n` `{0,1}`-matrices
majorizes `a(n)` for all terms after the 6th, where `a(n)` is the smallest positive integer that
is not the determinant of an `n × n` `{0,1}`-matrix.

Conventions:
* Offset 1 (`a(1) = 2`), so "after the 6th term" means `n ≥ 7`. Since `a(n)` is not a
  determinant and the maximum is, majorizing means `a(n) < maxdet(n)`.
-/

namespace OMA.S_oeis_a013588

/-- `k` is the determinant of an `n × n` `{0,1}`-matrix. -/
def IsDet01 (n : ℕ) (k : ℤ) : Prop :=
  ∃ M : Matrix (Fin n) (Fin n) ℤ, (∀ i j, M i j = 0 ∨ M i j = 1) ∧ M.det = k

/-- `a(n)`: the smallest positive integer that is not such a determinant. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ ¬ IsDet01 n k}

theorem main :
    ∀ n : ℕ, 7 ≤ n → ∃ M : Matrix (Fin n) (Fin n) ℤ,
      (∀ i j, M i j = 0 ∨ M i j = 1) ∧ (a n : ℤ) < M.det := by
  sorry

end OMA.S_oeis_a013588
