import Mathlib

/-!
# A322293: Integers k such that A322292(k) <= k

Source: https://oeis.org/A322293
Author: Paul Erdős (1979; Erdős Problem #385)

Conjecture (Paul Erdős, OEIS A322293):
Let `A322292(k) = max { m + lpf(m) | m < k, m composite }` (with `0` when no composite
`m < k` exists), where `lpf(m) = Nat.minFac m` is the smallest prime factor of `m`.
Then only finitely many positive integers `k` satisfy `A322292(k) ≤ k`.

Conventions:
- First terms of A322293: `1, 2, 3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 42, 44, 48, ...`.
- The condition `A322292(k) ≤ k` is equivalent to `∀ m < k, 1 < m → ¬ Nat.Prime m → m + m.minFac ≤ k`.
-/

namespace OMA.S_oeis_a322293

/-- The set of positive integers `k` such that `m + minFac(m) ≤ k` for every composite
`m < k` (OEIS A322293). -/
def S : Set ℕ :=
  {k : ℕ | 1 ≤ k ∧ ∀ m : ℕ, m < k → 1 < m → ¬ Nat.Prime m → m + m.minFac ≤ k}

/-- Conjecture (Erdős): the sequence A322293 is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a322293
