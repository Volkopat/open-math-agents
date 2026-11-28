import Mathlib

/-!
# A359199: Least prime p such that 2n can be written as a signed sum of p and the next 3 primes, or -1 if no such prime exists.

Source: https://oeis.org/A359199
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A359199 (Karl-Heinz Hofmann and Peter Munn, Jun 04
2023): a satisfactory prime p exists for all n.

Conventions:
* The sequence has offset 0 (data 5, 3, 3, 3, 7, 3, 3, 5, 3, 19, 3, 5, ...).
* A prime p is satisfactory for n when 2n = e0*p + e1*p1 + e2*p2 + e3*p3, where p1 < p2 < p3 are
  the next 3 primes after p and each sign e_i is +1 or -1 (each of the 4 primes appears exactly
  once). The four consecutive primes are `Nat.nth Nat.Prime (k + i)` for i = 0, 1, 2, 3 (`Nat.nth
  Nat.Prime` is 0-indexed), and the signed sum is computed in `ℤ`.
* n ranges over all natural numbers (the sequence has offset 0, with a(0) = 5 since 5 - 7 - 11 +
  13 = 0).
-/

namespace OMA.S_oeis_a359199

/-- The conjecture recorded in A359199. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, ∃ e : Fin 4 → ℤ, (∀ i, e i = 1 ∨ e i = -1) ∧
    ∑ i : Fin 4, e i * (Nat.nth Nat.Prime (k + i) : ℤ) = 2 * n := by
  sorry

end OMA.S_oeis_a359199
