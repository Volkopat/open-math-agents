import Mathlib

/-!
# OEIS A098464: Numbers k such that lcm(1,2,3,...,k) equals the denominator of the k-th
harmonic number H(k).

Source: https://oeis.org/A098464
Credit: @unserus

OEIS (A. Eldar): "Shiu (2016) conjectured that this sequence is infinite."
`H(k) = 1 + 1/2 + ... + 1/k` is Mathlib's `harmonic k : ℚ`, and its denominator is the reduced
denominator `Rat.den`. The terms are positive integers (first terms `1, 2, 3, 4, 5, 9`).
-/

namespace OMA.S_oeis_a098464

/-- The terms of A098464: positive `k` with `lcm(1, ..., k) = denominator of H(k)`. -/
def a098464Set : Set ℕ := {k : ℕ | 0 < k ∧ (Finset.Icc 1 k).lcm id = (harmonic k).den}

/-- A098464 is infinite. -/
theorem main : a098464Set.Infinite := by
  sorry

end OMA.S_oeis_a098464
