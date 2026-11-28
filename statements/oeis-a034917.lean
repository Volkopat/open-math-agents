import Mathlib

/-!
# OEIS A034917: minimal determinants of persymmetric `{-1, 0, 1}` matrices

Source: https://oeis.org/A034917
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the minimal determinant, negated, of an `n × n` persymmetric matrix with entries in
`{-1, 0, 1}`. Conjectures (OEIS entry): the minimal-determinant matrices have no zero entries;
`a(10) = 73728`, `a(11) = 327680` and `a(12) = 2097152`.

Conventions:
* `M` is persymmetric if it is symmetric about the anti-diagonal: `M i j = M (n-1-j) (n-1-i)`,
  written with `Fin.rev`. `n ≥ 1`.
* 'The minimal-determinant matrices have no zero entries' is read for every `n ≥ 1`: every
  persymmetric `{-1, 0, 1}` matrix attaining the minimum has all entries `±1`.
-/

namespace OMA.S_oeis_a034917

/-- Persymmetric matrices with entries in `{-1, 0, 1}`. -/
def Adm (n : ℕ) (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, M i j = M j.rev i.rev) ∧ ∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1

/-- `a(n)`: the negated minimum determinant (over a finite set of matrices). -/
noncomputable def a (n : ℕ) : ℤ := -sInf {d : ℤ | ∃ M, Adm n M ∧ M.det = d}

/-- The conjectured values and the no-zero-entries property. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∀ M, Adm n M → M.det = -a n → ∀ i j, M i j ≠ 0) ∧
    a 10 = 73728 ∧ a 11 = 327680 ∧ a 12 = 2097152 := by
  sorry

end OMA.S_oeis_a034917
