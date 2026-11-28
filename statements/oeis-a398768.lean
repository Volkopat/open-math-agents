import Mathlib

/-!
# A398768: Numbers without digits 0 or 1 divisible by (product of digits) * (sum of digits)

Source: https://oeis.org/A398768

Conjecture (OEIS A398768):
Every positive integer `k` whose base-10 representation contains neither `0` nor `1`
and which is divisible by `(product of base-10 digits of k) * (sum of base-10 digits of k)`
is even.

Conventions:
- Offset: `1`; first terms: `432, 248832, 2322432, 2772224, ...`.
- For `k = 432`, the digits are `4, 3, 2`, with product `24` and sum `9`, and
  `24 * 9 = 216 ∣ 432`.
-/

namespace OMA.S_oeis_a398768

/-- Predicate stating that `k ≥ 1` has no decimal digits `0` or `1` and is divisible by
the product of its decimal digits times the sum of its decimal digits (OEIS A398768). -/
def IsValid (k : ℕ) : Prop :=
  1 ≤ k ∧
  (∀ d ∈ Nat.digits 10 k, d ≠ 0 ∧ d ≠ 1) ∧
  ((Nat.digits 10 k).prod * (Nat.digits 10 k).sum) ∣ k

/-- Conjecture: every term of OEIS A398768 is even. -/
theorem main :
    ∀ k : ℕ, IsValid k → Even k := by
  sorry

end OMA.S_oeis_a398768
