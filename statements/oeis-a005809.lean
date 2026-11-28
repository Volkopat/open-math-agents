import Mathlib

/-!
# A005809: a(n) = binomial(3n,n).

Source: https://oeis.org/A005809
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a005809

theorem main : ∀ n : ℕ, 1 < n →
    (Nat.choose (3 * n) n ≡ 3 [MOD n ^ 3] ↔ Nat.Prime n ∧ n % 2 = 1) := by
  sorry

end OMA.S_oeis_a005809
