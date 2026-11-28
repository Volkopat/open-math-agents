import Mathlib

/-!
# A051783: Numbers k such that 3^k + 2 is prime.

Source: https://oeis.org/A051783
Credit: @Nealanio

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a051783

def n (k : ℕ) : ℕ :=
  3 ^ k + 2

theorem main : ∀ k : ℕ,
    (Nat.Prime (n k) ↔ 2 ^ ((n k - 1) / 2) ≡ n k - 1 [MOD n k]) := by
  sorry

end OMA.S_oeis_a051783
