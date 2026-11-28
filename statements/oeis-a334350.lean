import Mathlib

/-!
# A334350: Least positive integer m relatively prime to n such that phi(m*n) = phi(m)*phi(n) is a fourth power, where phi is Euler's totient function (A000010).

Source: https://oeis.org/A334350
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A334350 (Zhi-Wei Sun, Apr 24 2020): For any positive
integers k and m, there is a positive integer n relatively prime to m such that phi(m*n) =
phi(m)*phi(n) is a k-th power.

Conventions:
* The sequence has offset 1 (data 1, 1, 16, 15, 8, 703, 247, 5, 247, 489, 1255, 5, ...).
* phi is the Euler totient function `Nat.totient`.
* A k-th power is t^k for a natural number t. Both the equality phi(m*n) = phi(m)*phi(n) (which
  follows from coprimality) and the k-th power condition are stated, as in the conjecture.
* This is the general conjecture stated in the entry (the sequence itself is the case k = 4, with
  the roles of the letters m and n exchanged).
-/

namespace OMA.S_oeis_a334350

/-- The conjecture recorded in A334350. -/
theorem main : ∀ k m : ℕ, 0 < k → 0 < m → ∃ n : ℕ, 0 < n ∧ Nat.Coprime n m ∧
    Nat.totient (m * n) = Nat.totient m * Nat.totient n ∧
    ∃ t : ℕ, Nat.totient (m * n) = t ^ k := by
  sorry

end OMA.S_oeis_a334350
