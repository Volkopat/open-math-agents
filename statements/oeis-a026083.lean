import Mathlib

/-!
# OEIS A026083: a conjectured P-recurrence for constrained lattice paths

Source: https://oeis.org/A026083
`a n` (offset `4`) is the number of integer sequences `s(0), …, s(n)` with `s(0) = 0 = s(n)`,
`|s(i) - s(i-1)| = 1` for `i = 1, 2, 3` and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`
(6, 12, 38, 104, 300, …). Conjecture:
`n a(n) + (-3n + 5) a(n-1) + (-n - 6) a(n-2) + 3(n - 5) a(n-3) = 0`.

Conventions. Stated for `n ≥ 7`, so that all terms lie in the range `≥ 4` of the sequence.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a026083

/-- The constrained paths of length `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {s : Fin (n + 1) → ℤ | s 0 = 0 ∧ s (Fin.last _) = 0 ∧
    ∀ i : Fin n, (i.val < 3 → |s i.succ - s i.castSucc| = 1) ∧
      (3 ≤ i.val → |s i.succ - s i.castSucc| ≤ 1)}

theorem main :
    ∀ n : ℕ, 7 ≤ n →
      (n : ℤ) * a n + (-3 * n + 5) * a (n - 1) + (-(n : ℤ) - 6) * a (n - 2) +
        3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026083
