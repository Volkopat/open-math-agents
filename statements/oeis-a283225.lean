import Mathlib

/-!
# A283225: Primes prime(k) such that prime(k)^2 mod prime(k+2) is different from prime(k+2)^2 mod prime(k).

Source: https://oeis.org/A283225
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A283225 (Arnaud Vernier, Mar 03 2017): there are no
other terms in this sequence.

Conventions:
* The sequence has offset 1 (data 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 43, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* The terms are the primes prime(k) (k >= 1) such that prime(k)^2 mod prime(k+2) is different from
  prime(k+2)^2 mod prime(k). `There are no other terms` is stated as: every such prime is one of
  the 34 terms listed in the OEIS data.
-/

namespace OMA.S_oeis_a283225

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The conjecture recorded in A283225. -/
theorem main : ∀ k : ℕ, 0 < k → pr k ^ 2 % pr (k + 2) ≠ pr (k + 2) ^ 2 % pr k →
    pr k ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 43, 47, 53, 59, 61, 73, 79, 83, 89, 109,
      113, 137, 139, 199, 211, 241, 283, 293, 313, 317, 523, 1321, 1327} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a283225
