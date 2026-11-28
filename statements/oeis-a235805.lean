import Mathlib

/-!
# A235805: a(n) = |{0 < k < n - 2: 2*m + 1, m*(m+1) - prime(m) and m*(m+1) - prime(m+1) are all prime with m = phi(k) + phi(n-k)/2}|, where phi(.) is Euler's totient function.

Source: https://oeis.org/A235805
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235805 (Zhi-Wei Sun, Jan 16 2014): a(n) > 0 for all n
> 5.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 2, 3, 2, 4, 4, 4, 4, ...). `a n` is the number of
  integers k with 0 < k < n - 2 such that 2*m + 1, m*(m+1) - prime(m) and m*(m+1) - prime(m+1) are
  all prime, where m = phi(k) + phi(n-k)/2, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* phi is the Euler totient function `Nat.totient`.
* m = phi(k) + phi(n-k)/2 is the helper `m n k`; for 0 < k < n - 2 we have n - k > 2, so phi(n-k)
  is even and the natural-number division by 2 is exact. The range 0 < k < n - 2 is written k + 2
  < n to avoid subtraction.
* Natural-number subtraction is truncated: where the true value would be negative the truncated
  value is 0, and neither is prime, so the condition is unchanged.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235805

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- m = phi(k) + phi(n-k)/2 for the given n and k. -/
def m (n k : ℕ) : ℕ := Nat.totient k + Nat.totient (n - k) / 2

/-- The condition in the name of A235805 on a tuple, for a given n. -/
def P (n : ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k + 2 < n ∧ (2 * m n k + 1).Prime ∧ (m n k * (m n k + 1) - pr (m n k)).Prime ∧
  (m n k * (m n k + 1) - pr (m n k + 1)).Prime

/-- A235805: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A235805. -/
theorem main : ∀ n : ℕ, 5 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235805
