import Mathlib

/-!
# Nested twin primes in OEIS A093245

For each positive index, the sequence records the least first prime of a twin
pair whose image under `p ↦ (p² + n)² + n` also starts a twin pair. It records
zero if no such pair exists. Robert Israel conjectures that a zero can occur
only at an index divisible by three.

Source: https://oeis.org/A093245
-/

namespace OMA.S_oeis_a093245

def StartsTwinPair (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

def Qualifies (n p : ℕ) : Prop :=
  StartsTwinPair p ∧ StartsTwinPair ((p ^ 2 + n) ^ 2 + n)

noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ p, Qualifies n p then Nat.find h else 0

theorem main : ∀ n : ℕ, 1 ≤ n → a n = 0 → 3 ∣ n := by
  sorry

end OMA.S_oeis_a093245
