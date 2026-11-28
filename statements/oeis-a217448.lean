import Mathlib

/-!
# A217448: Least k > 0 such that 1 + n^2 and 1 + (n+k)^2 have the same smallest prime factor

Source: https://oeis.org/A217448
Credit: @xor2k
Sibling of OEIS A262965 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the OEIS A217448 conjecture: a(n) exists for all n.
That is, for every `n` in the index range there is an integer `k > 0` such that `1 + n^2` and
`1 + (n+k)^2` have the same smallest prime factor (then the least such `k` exists automatically).

Conventions:
* Offset 1, so `n` ranges over the positive integers (`0 < n`); then `1 + n^2 ≥ 2`.
* The smallest prime factor (A020639, here A089120(n) = A020639(n^2 + 1)) is `Nat.minFac`; both
  arguments are at least `2`, so `Nat.minFac` is their least prime divisor.
-/

namespace OMA.S_oeis_a217448

/-- For every `n > 0` there is `k > 0` such that `1 + n^2` and `1 + (n+k)^2` have the same smallest
prime factor. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ k : ℕ, 0 < k ∧ Nat.minFac (1 + n ^ 2) = Nat.minFac (1 + (n + k) ^ 2) := by
  sorry

end OMA.S_oeis_a217448
