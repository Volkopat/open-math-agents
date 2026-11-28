import Mathlib

/-!
# A049094: Numbers m such that 2^m - 1 is divisible by a square > 1

Source: https://oeis.org/A049094
Credit: @AkiRA-COM-FP

Formalizes Vladeta Jovovic's 2002 OEIS A049094 conjecture (offset 1): for every `n >= 1`,
`2^n - 1` is squarefree if and only if `gcd(n, 2^n - 1) = 1`.
(Known to be false, e.g. at `n = 364` where `1093^2 | 2^364 - 1`.)
-/

namespace OMA.S_oeis_a049094

/-- Conjecture: for every `n >= 1`, `2^n - 1` is squarefree iff `gcd(n, 2^n - 1) = 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (Squarefree (2 ^ n - 1) ↔ Nat.Coprime n (2 ^ n - 1)) := by
  sorry

end OMA.S_oeis_a049094
