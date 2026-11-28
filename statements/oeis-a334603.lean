import Mathlib

/-!
# A334603: Period of the fraction 1/11^n for n >= 1

Source: https://oeis.org/A334603
Credit: @jagong-cmu

Formalizes the formula marked as conjectured in the OEIS entry (offset 1):
a(n) = 2 * 11^(n-1) for n >= 1.

Conventions:
* The period of the decimal expansion of `1/m`, for `m` coprime to 10, is the length of the
  repeating block of digits. It is the least `k >= 1` with `10^k = 1 (mod m)`, that is, the
  multiplicative order of 10 modulo `m` (this is also A051626(m)). It is written here as
  `orderOf (10 : ZMod m)`. Since `11^n` is coprime to 10, the expansion of `1/11^n` is purely
  periodic and this order is its period.
* The offset is 1, so the statement is for every `n >= 1`. The subtraction `n - 1` on `ℕ` is
  the usual one for `n >= 1`.
-/

namespace OMA.S_oeis_a334603

/-- The period of the decimal expansion of `1/m`, for `m` coprime to 10. -/
noncomputable def period (m : ℕ) : ℕ := orderOf (10 : ZMod m)

/-- A334603, offset 1: the period of `1/11^n`. -/
noncomputable def a (n : ℕ) : ℕ := period (11 ^ n)

theorem main : ∀ n : ℕ, 1 ≤ n → a n = 2 * 11 ^ (n - 1) := by
  sorry

end OMA.S_oeis_a334603
