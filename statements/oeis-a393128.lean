import Mathlib

/-!
# A393128: Positive integers not of the form floor(k + log(k) + log(Pi)).

Source: https://oeis.org/A393128
Credit: @sobrien032

The entry (M. F. Hasler, 2026) records the conjecture that for every prime `p` there is exactly
one integer `k` such that `p = k + floor(log(Pi*k))`. As `log(Pi*k)` is defined only for `k > 0`,
`k` ranges over the positive integers, taken here in `ℕ` with `0 < k`. (No integer `k ≤ 0` could
give a prime value in any case.)
-/

namespace OMA.S_oeis_a393128

/-- For every prime `p` there is exactly one positive integer `k` with
`p = k + ⌊log (π * k)⌋`. -/
theorem main : ∀ p : ℕ, p.Prime →
    ∃! k : ℕ, 0 < k ∧ (p : ℤ) = k + ⌊Real.log (Real.pi * k)⌋ := by
  sorry

end OMA.S_oeis_a393128
