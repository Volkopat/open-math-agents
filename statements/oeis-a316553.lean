import Mathlib

/-!
# A316553: Number of elements of order 2 in the group SL(2, Z(n)).

Source: https://oeis.org/A316553
Credit: @warshanks

`a(n)` is the number of elements of order 2 in `SL(2, ℤ/nℤ)`, the group of `2 × 2` matrices over
`ZMod n` with determinant `1` (offset 1: `n ≥ 1`). The entry records one conjecture:

  `a(n) = 2^(omega(n) + min(3, valuation(n, 2))) - 1`,

where `omega(n)` is the number of distinct prime factors of `n` (`n.primeFactors.card`) and
`valuation(n, 2)` is the exponent of `2` in `n` (`padicValNat 2 n`).

The count is `Nat.card` of the subtype of elements whose `orderOf` is `2`; for `n ≥ 1` the group is
finite, so this is the actual number of such elements. The conjecture is stated for `n ≥ 1`, the
range of the sequence (for `n = 0`, `ZMod 0 = ℤ` and the formula does not apply).
-/

namespace OMA.S_oeis_a316553

/-- `a n`: the number of elements of order `2` in `SL(2, ℤ/nℤ)` (OEIS A316553). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod n) // orderOf g = 2}

/-- The conjecture of OEIS A316553:
`a(n) = 2^(omega(n) + min(3, valuation(n, 2))) - 1` for every `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = 2 ^ (n.primeFactors.card + min 3 (padicValNat 2 n)) - 1 := by
  sorry

end OMA.S_oeis_a316553
