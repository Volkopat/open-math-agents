import Mathlib

/-!
# Strict decrease of the roots of prime-indexed primes

OEIS A006450 records Zhi-Wei Sun’s conjecture that the nth root of the
prime in position p_n decreases strictly with n, starting at n = 1.
Source https://oeis.org/A006450
-/

namespace OMA.S_oeis_a006450

-- The source numbers primes from one. Nat.nth numbers them from zero.
theorem main :
    StrictAntiOn
      (fun n : ℕ ↦
        (Nat.nth Nat.Prime (Nat.nth Nat.Prime (n - 1) - 1) : ℝ) ^
          (1 / (n : ℝ)))
      (Set.Ici 1) := by
  sorry

end OMA.S_oeis_a006450
