import Mathlib

/-!
# OEIS A225034: a conjectured recurrence for 101-avoiding words

Source: https://oeis.org/A225034
`a n` is the number of binary words containing `n` ones and at most `n` zeros that do not
contain the substring `101`. Conjecture: `(n+1) a(n) - (2n+3) a(n-1) - 3(n-2) a(n-2) = 0`
for `n > 1`.

Conventions. Words are lists over `Bool` (`true = 1`); "substring" means contiguous factor
(`List.IsInfix`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a225034

/-- Words with exactly `n` ones and `z` zeros avoiding `101`. -/
noncomputable def cnt (n z : ℕ) : ℕ :=
  Set.ncard {w : List Bool | w.count true = n ∧ w.count false = z ∧
    ¬ [true, false, true] <:+: w}

/-- A225034. -/
noncomputable def a (n : ℕ) : ℕ := ∑ z ∈ Finset.range (n + 1), cnt n z

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * a n - (2 * n + 3) * a (n - 1) - 3 * ((n : ℤ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a225034
