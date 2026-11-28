import Mathlib.Data.Nat.Prime.Basic

namespace OMA.S_oeis_a286348

/-- OEIS A286348 conjecture: for any integer `y` and natural number `x`, if `(1 + y)^x + (-y)^x`
is a prime number (i.e., a positive integer whose natural value is prime), then `x = 0`, or `x`
is an even power of two (`∃ k ≥ 1, x = 2 ^ k`), or `x` is an odd prime. -/
theorem main :
    ∀ (y : ℤ) (x : ℕ),
      0 < (1 + y) ^ x + (-y) ^ x →
      ((1 + y) ^ x + (-y) ^ x).toNat.Prime →
      x = 0 ∨ (∃ k ≥ 1, x = 2 ^ k) ∨ (x.Prime ∧ Odd x) := by
  sorry

end OMA.S_oeis_a286348
