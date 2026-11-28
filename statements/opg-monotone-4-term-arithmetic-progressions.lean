import Mathlib

/-!
# Monotone 4-term Arithmetic Progressions

Source: https://www.openproblemgarden.org/op/monotone_4_term_arithmetic_progressions
Credit: @mburv

Question (Davis, Entringer, Graham, Simmons [DEGS]): Is it true that every permutation of the
positive integers must contain a monotone 4-term arithmetic progression?

Convention (standard, as in [DEGS] and Erdős Problem 196): a permutation `σ` of the positive
integers is viewed as the sequence `σ 1, σ 2, σ 3, ...`. It contains a monotone `k`-term arithmetic
progression if some `k` terms of this sequence, read in increasing order of position, form an
increasing or a decreasing arithmetic progression (common difference nonzero). The value `v`
sits at position `σ.symm v`, so for `k = 4` this means: there are positive integers `a` and `d`
such that the values `a, a + d, a + 2d, a + 3d` occur at strictly increasing positions
(increasing progression) or at strictly decreasing positions (decreasing progression).

[DEGS] show that every permutation of the positive integers contains a monotone 3-term
arithmetic progression, and that some permutation contains no monotone 5-term one.

Literature note (not part of the statement): this is the same question as Erdős Problem 196,
stated upstream in formal-conjectures as `Erdos196.erdos_196` (over permutations of `ℕ`). The
answer there is recorded as no: B. S. Ho, A 4AP-free permutation of the positive integers,
arXiv:2609.12780. So `main` below, which states the question affirmatively as posed, is expected
to be refuted (a disproof `¬ main` would settle it).

[DEGS] J. A. Davis, R. C. Entringer, R. L. Graham, G. J. Simmons, On permutations containing no
long arithmetic progression, Acta Arith. 34 (1977), 81-90.
-/

namespace OMA.S_opg_monotone_4_term_arithmetic_progressions

/-- The values `a, a + d, a + 2d, a + 3d` (with `a, d` positive integers) appear in the sequence
`σ 1, σ 2, ...` at strictly increasing positions, or at strictly decreasing positions. -/
def HasMonotone4APAt (σ : Equiv.Perm ℕ+) (a d : ℕ+) : Prop :=
  (σ.symm a < σ.symm (a + d) ∧ σ.symm (a + d) < σ.symm (a + 2 * d) ∧
      σ.symm (a + 2 * d) < σ.symm (a + 3 * d)) ∨
    (σ.symm (a + 3 * d) < σ.symm (a + 2 * d) ∧ σ.symm (a + 2 * d) < σ.symm (a + d) ∧
      σ.symm (a + d) < σ.symm a)

/-- Every permutation of the positive integers contains a monotone 4-term arithmetic
progression. -/
theorem main : ∀ σ : Equiv.Perm ℕ+, ∃ a d : ℕ+, HasMonotone4APAt σ a d := by
  sorry

end OMA.S_opg_monotone_4_term_arithmetic_progressions
