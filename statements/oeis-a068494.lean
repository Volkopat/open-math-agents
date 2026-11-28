import Mathlib

/-!
# A068494: a(n) = n mod phi(n).

Source: https://oeis.org/A068494
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a068494

theorem main : ∀ n : ℕ, 2 < n →
    (n % Nat.totient n = 1 ↔ Nat.Prime n) := by
  sorry

end OMA.S_oeis_a068494
