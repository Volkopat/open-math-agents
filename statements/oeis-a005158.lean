import Mathlib

/-!
# A005158: Robbins' Recurrence for Half-Turn Symmetric Alternating Sign Matrices

Source: https://oeis.org/A005158
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A005158(n) is the number of `n × n` alternating sign matrices (entries in `{-1, 0, 1}`, every row
and column sums to `1`, and all partial sums along every row and column lie in `{0, 1}`) that are
invariant under a 180-degree rotation (half-turn): `M (rev i) (rev j) = M i j`.

Conjecture (Robbins): For all `n > 1`,
`a(n) = a(n - 1) * (1 + [n even] / 3) * C(3 * (n / 2), n / 2) / C(2 * (n / 2), n / 2)`.
-/

namespace OMA.S_oeis_a005158

/-- `IsHalfTurnASM M` holds if `M` is an `n × n` alternating sign matrix invariant under a
half-turn (`180°` rotation). -/
def IsHalfTurnASM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, M i j = -1 ∨ M i j = 0 ∨ M i j = 1) ∧
  (∀ i, ∑ j : Fin n, M i j = 1) ∧
  (∀ j, ∑ i : Fin n, M i j = 1) ∧
  (∀ i k : Fin n,
    let s := ∑ j ∈ Finset.univ.filter (· ≤ k), M i j
    s = 0 ∨ s = 1) ∧
  (∀ j k : Fin n,
    let s := ∑ i ∈ Finset.univ.filter (· ≤ k), M i j
    s = 0 ∨ s = 1) ∧
  (∀ i j : Fin n, M i.rev j.rev = M i j)

/-- Number of `n × n` half-turn symmetric alternating sign matrices (A005158). -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard { M : Matrix (Fin n) (Fin n) ℤ | IsHalfTurnASM M }

theorem main :
    ∀ n : ℕ, 1 < n →
      (a n : ℚ) =
        (a (n - 1) : ℚ) *
          (1 + if Even n then (1 : ℚ) / 3 else 0) *
          (Nat.choose (n / 2 * 3) (n / 2) : ℚ) /
          (Nat.choose (n / 2 * 2) (n / 2) : ℚ) := by
  sorry

end OMA.S_oeis_a005158
