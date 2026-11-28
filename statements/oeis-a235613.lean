import Mathlib

/-!
# A235613: Number of ways to write n = k + m (0 < k <= m) with k and m terms of A235592.

Source: https://oeis.org/A235613
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235613 (Zhi-Wei Sun, Jan 12 2014): a(n) > 0 for all n
> 3.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 2, 2, 3, 2, 3, 3, 3, ...). `a n` is the number of
  pairs (k, m) with 0 < k <= m, n = k + m and k, m both terms of A235592, exactly as in the OEIS
  name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* A235592 is the set of positive integers k such that k*(k+1) - prime(k) is prime; this is the
  helper `T`. Since prime(k) <= k*(k+1) for k >= 1, the natural-number subtraction is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a235613

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- k is a term of A235592: k > 0 and k*(k+1) - prime(k) is prime. -/
def T (k : ℕ) : Prop := 0 < k ∧ (k * (k + 1) - pr k).Prime

/-- The condition in the name of A235613 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ k ≤ m ∧ k + m = n ∧ T k ∧ T m

/-- A235613: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235613. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a235613
