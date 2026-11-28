import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs

/-!
# A350905 and A350176

Juri-Stepan Gerasimov conjectured that every member of the intersection is prime.
Both sequences test integers starting at 3, where the common divisor is positive.

Sources: https://oeis.org/A350905 and https://oeis.org/A350176
Credit: @jacklarmer
-/

namespace OMA.S_oeis_a350905

theorem main : ∀ k : ℕ, 3 ≤ k →
    k.choose 3 ∣ Nat.choose (3 ^ k - 3) 2 →
    k.choose 3 ∣ Nat.choose (3 ^ k - 2) 3 → Nat.Prime k := by
  sorry

end OMA.S_oeis_a350905
