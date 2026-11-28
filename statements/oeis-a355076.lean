import Mathlib

namespace OMA.S_oeis_a355076

/-- Stern's diatomic sequence `fusc` (A002487): `fusc 0 = 0`, `fusc 1 = 1`,
`fusc (2n) = fusc n`, `fusc (2n+1) = fusc n + fusc (n+1)`. -/
def fusc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fusc ((n + 2) / 2) + if n % 2 = 1 then fusc ((n + 3) / 2) else 0

/-- A355076(n): the denominator of `Sum_{k=0..n} fusc(k)/fusc(k+1)`. -/
def a (n : ℕ) : ℕ := (∑ k ∈ Finset.range (n + 1), (fusc k : ℚ) / fusc (k + 1)).den

/-- Conjecture (OEIS A355076): a(n) = 1 for n of the form 2*4^k - 1 or 2*4^k - 2. -/
theorem main : ∀ k : ℕ, a (2 * 4 ^ k - 1) = 1 ∧ a (2 * 4 ^ k - 2) = 1 := by
  sorry

end OMA.S_oeis_a355076
