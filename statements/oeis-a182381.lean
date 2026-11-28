import Mathlib

/-!
# OEIS A182381: Carmichael numbers divisible by 17 and 29

Source: https://oeis.org/A182381
Credit: @Heart-galaxy

Marius Coman's recorded conjecture states that every Carmichael number C divisible
by both 17 and 29 has the form C = 952*n + 561 for a natural number n.
Charles R Greathouse IV noted on October 2, 2012 that this follows from Korselt's
criterion, and that the stronger congruence C = 2465 (mod 55216) holds.
This is a known result.

Carmichael numbers are defined as composite positive integers C > 1 for which
b^(C-1) = 1 (mod C) for every natural base b coprime to C.
Korselt's criterion is not assumed in the definition. The existential n may be zero.
-/

namespace OMA.S_oeis_a182381

/-- The defining universal Fermat property of a composite Carmichael number. -/
def IsCarmichael (C : ℕ) : Prop :=
  1 < C ∧ ¬C.Prime ∧ ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]

/-- The OEIS conjecture on Carmichael numbers divisible by 17 and 29. -/
theorem main : ∀ C : ℕ, IsCarmichael C → 17 ∣ C → 29 ∣ C →
    ∃ n : ℕ, C = 952 * n + 561 := by
  sorry

end OMA.S_oeis_a182381
