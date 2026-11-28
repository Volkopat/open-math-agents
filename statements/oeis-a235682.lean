import Mathlib

/-!
# A235682: Number of ways to write n = k + m with k > 0 and m > 2 such that p = phi(k) + phi(m)/2 + 1, prime(p) - p + 1 and p*(p+1) - prime(p) are all prime, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235682
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235682 (Zhi-Wei Sun, Jan 13 2014): a(n) > 0 for all n
> 84.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 2, 1, 1, 3, 2, 1, 3, 1, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k + m, k > 0, m > 2, such that p = phi(k) + phi(m)/2 +
  1, prime(p) - p + 1 and p*(p+1) - prime(p) are all prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* phi is the Euler totient function `Nat.totient`.
* For m > 2, phi(m) is even, so the natural-number division phi(m)/2 is exact. The helper `p k m`
  is p.
* prime(p) - p is exact since prime(p) >= p; the last subtraction is truncated, which does not
  change primality (a negative value and 0 are both not prime).
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235682

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- p = phi(k) + phi(m)/2 + 1. -/
def p (k m : ℕ) : ℕ := Nat.totient k + Nat.totient m / 2 + 1

/-- The condition in the name of A235682 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  k + m = n ∧ 0 < k ∧ 2 < m ∧ (p k m).Prime ∧ (pr (p k m) - p k m + 1).Prime ∧
  (p k m * (p k m + 1) - pr (p k m)).Prime

/-- A235682: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235682. -/
theorem main : ∀ n : ℕ, 84 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235682
