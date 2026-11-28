import Mathlib

/-!
# A050216: Number of primes between (prime(n))^2 and (prime(n+1))^2, with a(0) = 2 by convention.

Source: https://oeis.org/A050216
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A050216 (Eric W. Weisstein): for n >= 2, a(n) >= 4
(Brocard's Conjecture).

Conventions:
* The sequence has offset 0 (data 2, 2, 5, 6, 15, 9, 22, 11, 27, 47, 16, 57, ...).
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* For n >= 1, `a n` is the number of primes strictly between prime(n)^2 and prime(n+1)^2 (a finite
  set, counted with `Set.ncard`); a(0) = 2 by the convention in the OEIS name.
-/

namespace OMA.S_oeis_a050216

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- A050216: number of primes between prime(n)^2 and prime(n+1)^2, with a(0) = 2. -/
noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 2 else Set.ncard {q : ℕ | q.Prime ∧ pr n ^ 2 < q ∧ q < pr (n + 1) ^ 2}

/-- Brocard's conjecture, as recorded in A050216. -/
theorem main : ∀ n : ℕ, 2 ≤ n → 4 ≤ a n := by
  sorry

end OMA.S_oeis_a050216
