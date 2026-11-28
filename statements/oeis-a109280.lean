import Mathlib

/-!
# A109280: Numbers n such that z(n) and z(n+1) are both prime, where z(n) = a^d + b^d + c^d + ..., where a*b*c* ... is the prime factorization of n and d is the largest digit of n.

Source: https://oeis.org/A109280
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A109280 (Jason Earls, Jun 24 2005): Sequence is
infinite.

Conventions:
* The sequence has offset 1 (data 10, 11, 567, 1209, 2034, 3114, 3311, 5243, 5290, 7256, 7436,
  9558, ...).
* z(n) is the sum of p^d over the prime factors p of n counted with multiplicity (the list
  `Nat.primeFactorsList n`), where d is the largest decimal digit of n (the maximum of the list
  `Nat.digits 10 n`, computed by folding `max`). For n = 0, 1 the list of prime factors is empty
  and z(n) = 0.
* `The sequence is infinite` / `has infinitely many terms` is rendered as `Set.Infinite` of the
  set of all numbers with the defining property of the OEIS name.
-/

namespace OMA.S_oeis_a109280

/-- z(n) = sum of p^d over the prime factors p of n with multiplicity, d the largest digit of n. -/
def z (n : ℕ) : ℕ :=
  ((Nat.primeFactorsList n).map (fun p => p ^ ((Nat.digits 10 n).foldr max 0))).sum

/-- The conjecture recorded in A109280. -/
theorem main : Set.Infinite {n : ℕ | (z n).Prime ∧ (z (n + 1)).Prime} := by
  sorry

end OMA.S_oeis_a109280
