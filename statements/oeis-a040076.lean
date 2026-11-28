import Mathlib

/-!
# A040076: smallest m such that n*2^m + 1 is prime

Source: https://oeis.org/A040076
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A040/A040076.seq
Credit: @Bondyboy2001

For positive `n`, `a(n)` is the least nonnegative integer `m` such that `n * 2^m + 1` is prime,
or `-1` if no such `m` exists. The OEIS entry records the conjecture that `a(n) ≥ 0` for every
`n < 78557`.

The sequence offset is `1`, so the conjecture is stated for positive `n`.
-/

namespace OMA.S_oeis_a040076

/-- The nonnegative-witness condition defining A040076. -/
def IsWitness (n m : ℕ) : Prop := (n * 2 ^ m + 1).Prime

open scoped Classical in
/-- `a n`: the least nonnegative witness, or `-1` if no witness exists. -/
noncomputable def a (n : ℕ) : ℤ :=
  if h : ∃ m : ℕ, IsWitness n m then (Nat.find h : ℤ) else -1

theorem main : ∀ n : ℕ, 1 ≤ n → n < 78557 → 0 ≤ a n := by
  sorry

end OMA.S_oeis_a040076
