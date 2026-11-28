import Mathlib

/-!
# A120275: Smallest prime factor of the odd Catalan number A038003(n).

Source: https://oeis.org/A120275
Credit: @divmxnd0x

Conjecture (Robert Israel, Nov 18 2015, stated in A120275): `a(n) ≠ 3` iff the base-3
representation of `2^n - 1` has no 2's, and this only occurs for `n = 2, 5, 8` (verified up to
`n = 10^4`).

Formalization notes:
* The conjecture is stated through its arithmetic form: among the indices `n ≥ 2` of A120275
  (offset 2), the numbers `2^n - 1` whose base-3 digits contain no `2` are exactly `n = 2, 5, 8`.
-/

namespace OMA.S_oeis_a120275

/-- For `n ≥ 2`, `2^n - 1` has no digit `2` in base 3 exactly when `n ∈ {2, 5, 8}`. -/
theorem main : {n : ℕ | 2 ≤ n ∧ 2 ∉ Nat.digits 3 (2 ^ n - 1)} = {2, 5, 8} := by
  sorry

end OMA.S_oeis_a120275
