import Mathlib

/-!
# A360587: a(n) is the least positive integer k such that k*(k+1)*...*(k+n-1) does not contain the digit 2, or -1 if there is no such k.

Source: https://oeis.org/A360587
Credit: @eltociear

`a(n)` (offset 1) is the least `k ≥ 1` such that the decimal expansion of
`k (k+1) ⋯ (k+n-1)` has no digit `2`, or `-1` if there is no such `k` (`a(4) = 3`:
`3·4·5·6 = 360`). The entry conjectures:

  a(n) = -1 for n = 31 and all n >= 33.

`main` states that for `n = 31` and every `n ≥ 33`, every product of `n` consecutive positive
integers contains the digit `2` in base 10.
-/

namespace OMA.S_oeis_a360587


/-- The conjecture in OEIS A360587. -/
theorem main : ∀ n : ℕ, (n = 31 ∨ 33 ≤ n) → ∀ k : ℕ, 1 ≤ k →
      2 ∈ Nat.digits 10 (∏ i ∈ Finset.range n, (k + i)) := by
  sorry

end OMA.S_oeis_a360587
