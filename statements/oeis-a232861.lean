import Mathlib

/-!
# A232861: Numbers k with k - 1, k + 1, prime(k) - k, prime(k) + k, k*prime(k) - 1, k*prime(k) + 1 all prime.

Source: https://oeis.org/A232861
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A232861 (Zhi-Wei Sun, Dec 01 2013), part (i): This
sequence contains infinitely many terms.

Conventions:
* The sequence has offset 1 (data 22110, 23742, 128238, 275592, 346560, 1061910, 1281522, 1339002,
  1378188, 1461600, 1850130, 2064150, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* Since prime(k) > k, the subtraction prime(k) - k is exact; k - 1 and k*prime(k) - 1 are exact
  for k >= 1, and k = 0 is excluded by 0 < k.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
-/

namespace OMA.S_oeis_a232861

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A232861, part (i). -/
theorem main : Set.Infinite {k : ℕ | 0 < k ∧ (k - 1).Prime ∧ (k + 1).Prime ∧ (pr k - k).Prime ∧
    (pr k + k).Prime ∧ (k * pr k - 1).Prime ∧ (k * pr k + 1).Prime} := by
  sorry

end OMA.S_oeis_a232861
