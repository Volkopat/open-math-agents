import Mathlib

/-!
# OEIS A058887: the prime Sierpiński problem

Source: https://oeis.org/A058887
A Sierpiński number is an odd `k` such that `k · 2^n + 1` is composite for all `n ≥ 1`. The
entry notes that for large `n`, `a(n)` will likely be the first prime Sierpiński number,
which is conjectured to be `271129`. `main` states that `271129` is the least prime
Sierpiński number.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a058887

/-- `k` is a Sierpiński number. -/
def IsSierpinski (k : ℕ) : Prop := Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n + 1).Prime

theorem main : IsLeast {p : ℕ | p.Prime ∧ IsSierpinski p} 271129 := by
  sorry

end OMA.S_oeis_a058887
