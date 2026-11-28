import Mathlib

/-!
# A259628: Numbers m with m-1, m+1, prime(m)+2, prime(m)-m, prime(m)+m, m*prime(m)-1 and m*prime(m)+1 all prime.

Source: https://oeis.org/A259628
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A259628 (Zhi-Wei Sun, Jul 01 2015): The sequence
contains infinitely many terms.

Conventions:
* The sequence has offset 1 (data 2523708, 6740478, 6759030, 14655522, 22885698, 28384200,
  44630148, 71742300, 87002328, 87466500, 89842200, 153110622, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* Since prime(m) > m, the subtraction prime(m) - m is exact; m - 1 and m*prime(m) - 1 are exact
  for m >= 1, and m = 0 is excluded by 0 < m.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a259628

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A259628. -/
theorem main : Set.Infinite {m : ℕ | 0 < m ∧ (m - 1).Prime ∧ (m + 1).Prime ∧ (pr m + 2).Prime ∧
    (pr m - m).Prime ∧ (pr m + m).Prime ∧ (m * pr m - 1).Prime ∧ (m * pr m + 1).Prime} := by
  sorry

end OMA.S_oeis_a259628
