import Mathlib

/-!
# A235508: Number of ways to write 2*n = p + q with q > 0 such that p, p*(p+1) - prime(p) and prime(q) - q + 1 are all prime.

Source: https://oeis.org/A235508
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235508 (Zhi-Wei Sun, Jan 14 2014): a(n) > 0 for all n
> 1.

Conventions:
* The sequence has offset 1 (data 0, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3, ...). `a n` is the number of
  pairs (p, q) of natural numbers with 2*n = p + q, q > 0, and p, p*(p+1) - prime(p) and prime(q)
  - q + 1 all prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* The natural-number subtractions are exact: prime(p) <= p*(p+1) for every prime p, and prime(q)
  >= q for q >= 1.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235508

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A235508 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = 2 * n ∧ 0 < q ∧ p.Prime ∧ (p * (p + 1) - pr p).Prime ∧ (pr q - q + 1).Prime

/-- A235508: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235508. -/
theorem main : ∀ n : ℕ, 1 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235508
