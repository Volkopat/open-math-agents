import Mathlib

/-!
# Twin primes between successive fourth-order prime-indexed primes

OEIS A088973 conjectures that each of these closed intervals contains a twin-prime
pair. The source uses one-based indexing for primes and for the intervals.

Source: https://oeis.org/A088973
-/

namespace OMA.S_oeis_a088973

/-- The prime with positive index `n` in OEIS A000040. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The fourth-order prime-indexed prime with positive index `n` in OEIS A049203. -/
noncomputable def pips4 (n : ℕ) : ℕ := (primeAt^[5]) n

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ pips4 n ≤ p ∧ p + 2 ≤ pips4 (n + 1) := by
  sorry

end OMA.S_oeis_a088973
