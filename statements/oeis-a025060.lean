import Mathlib

/-!
# A025060: Numbers of the form i*j + j*k + k*i, where 1 <= i < j < k.

Source: https://oeis.org/A025060
Credit: @sntntHb

Conjecture (Jon Perry, Apr 21 2013): if `i`, `j` and `k` are allowed to be negative, but not zero,
and are still distinct, then the sequence is all the integers.

That is: every integer `z` can be written as `z = i*j + j*k + k*i` with `i, j, k` pairwise
distinct nonzero integers.
-/

namespace OMA.S_oeis_a025060

theorem main : ∀ z : ℤ, ∃ i j k : ℤ,
    i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ z = i * j + j * k + k * i := by
  sorry

end OMA.S_oeis_a025060
