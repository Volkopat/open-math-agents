import Mathlib

/-!
# A360930: Odd numbers which cannot be expressed as p + q*(q-1) where p and q are primes.

Source: https://oeis.org/A360930
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a360930

def Expressible (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q * (q - 1)

theorem main : ¬ Expressible 772277 ∧
    ∀ n : ℕ, n % 2 = 1 → 772277 < n → Expressible n := by
  sorry

end OMA.S_oeis_a360930
