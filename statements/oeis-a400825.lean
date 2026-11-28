import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic

namespace OMA.S_oeis_a400825

/-- `N(k) = (2^k - 1) * 2^(k + 4) + 1` as in OEIS A400825. -/
def N (k : ℕ) : ℕ :=
  (2 ^ k - 1) * 2 ^ (k + 4) + 1

/-- OEIS A400825 conjecture: for every `k ≥ 1`, letting `N = (2^k - 1) * 2^(k + 4) + 1`,
if `2 ^ ((N - 1) / 4) ≡ -1 (mod N)`, then `N` is prime. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      (2 : ZMod (N k)) ^ ((N k - 1) / 4) = -1 → (N k).Prime := by
  sorry

end OMA.S_oeis_a400825
