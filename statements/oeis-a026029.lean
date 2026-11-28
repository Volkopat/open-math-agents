import Mathlib

/-!
# OEIS A026029: a conjectured P-recurrence for lattice walks

Source: https://oeis.org/A026029
`a n` is the number of sequences `s(0), …, s(2n)` of nonnegative integers with
`|s(i) - s(i-1)| = 1`, `s(0) = 3` and `s(2n) = 3` (1, 2, 6, 20, 69, …). Conjecture:
`(n+4) a(n) + 6(-n-2) a(n-1) + 4(2n-1) a(n-2) = 0`.

Conventions. Stated for `n ≥ 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a026029

/-- Nonnegative `±1`-walks of length `2n` from `3` to `3`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : Fin (2 * n + 1) → ℕ | s 0 = 3 ∧ s (Fin.last _) = 3 ∧
    ∀ i : Fin (2 * n), (s i.succ : ℤ) - s i.castSucc = 1 ∨ (s i.succ : ℤ) - s i.castSucc = -1}

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 4) * a n + 6 * (-(n : ℤ) - 2) * a (n - 1) + 4 * (2 * n - 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a026029
