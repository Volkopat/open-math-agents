import Mathlib

/-!
# OEIS A182208: factor forms of Carmichael numbers divisible by 7

Source: https://oeis.org/A182208
Credit: @Heart-galaxy

Marius Coman conjectured that each Carmichael number C divisible by 7 can be written
as 7*(6m+1)*(6n+1) or as 7*(6m-1)*(6n-1), with natural m and n.
Charles R Greathouse IV noted on October 2, 2012 that this follows from Korselt's
criterion. This is a known result. The accompanying proof produces positive m and n.

Carmichael numbers are composite integers C > 1 satisfying the universal Fermat
congruence for every natural base coprime to C. No Korselt condition is assumed.
The subtractions in the second form are natural subtraction.
-/

namespace OMA.S_oeis_a182208

def IsCarmichael (C : ℕ) : Prop :=
  1 < C ∧ ¬C.Prime ∧ ∀ b : ℕ, b.Coprime C → b ^ (C - 1) ≡ 1 [MOD C]

/-- The two factor forms recorded in OEIS A182208. -/
theorem main : ∀ C : ℕ, IsCarmichael C → 7 ∣ C → ∃ m n : ℕ,
    C = 7 * (6 * m + 1) * (6 * n + 1) ∨
    C = 7 * (6 * m - 1) * (6 * n - 1) := by
  sorry

end OMA.S_oeis_a182208
