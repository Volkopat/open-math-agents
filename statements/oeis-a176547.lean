import Mathlib

/-!
# A176547: Numbers n such that 2*n^2 + 6*n + 1 is prime.

Source: https://oeis.org/A176547
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a176547

theorem main : ∀ n p : ℕ, p = 2 * n ^ 2 + 6 * n + 1 → Nat.Prime p →
    ¬ Nat.Prime (2 ^ p - 1) := by
  sorry

end OMA.S_oeis_a176547
