import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a182336

/-- The binary Hamming distance between two natural numbers `n` and `m`:
the number of `1`-bits in `n ^^^ m`. -/
def hammingDist (n m : ℕ) : ℕ :=
  (Nat.digits 2 (n ^^^ m)).count 1

/-- `a(n)` (OEIS A182336): the least `m ≥ n` such that the binary Hamming distance
between `n` and `m` is `4`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | n ≤ m ∧ hammingDist n m = 4}

/-- Conjecture (OEIS A182336): for all `n > 96`, `n + 1 ≤ a(n) ≤ 9*n/8 + 1`. -/
theorem main : ∀ n : ℕ, 96 < n →
    ((n + 1 : ℕ) : ℚ) ≤ (a n : ℚ) ∧ (a n : ℚ) ≤ (9 : ℚ) * (n : ℚ) / 8 + 1 := by
  sorry

end OMA.S_oeis_a182336
