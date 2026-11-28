import Mathlib

/-!
# OEIS A029795: k and k³ with the same set of digits

Source: https://oeis.org/A029795
`a n` lists the `k` such that `k` and `k³` have the same set of decimal digits
(0, 1, 10, 100, …). Conjecture: there exist `m` and `N` with `a(n) = m + n` for all `n ≥ N`
(eventually the sequence contains every integer).

Conventions. Offset `1`: `a n = Nat.nth P (n - 1)`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a029795

/-- `k` and `k³` have the same set of decimal digits. -/
def P (k : ℕ) : Prop := (Nat.digits 10 k).toFinset = (Nat.digits 10 (k ^ 3)).toFinset

/-- A029795, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

theorem main : ∃ m N : ℕ, ∀ n ≥ N, a n = m + n := by
  sorry

end OMA.S_oeis_a029795
