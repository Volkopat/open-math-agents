import Mathlib

/-!
# A236765: Number of ways to write n = k^2 + m with k > 1 and m > 1 such that sigma(k^2) + prime(m) - 1 is prime, where sigma(j) denotes the sum of all positive divisors of j.

Source: https://oeis.org/A236765
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A236765 (Zhi-Wei Sun, Jan 30 2014), part (i): If n > 6
is not equal to 18, then a(n) > 0.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k^2 + m, k > 1, m > 1 and sigma(k^2) + prime(m) - 1
  prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* sigma(j) is the sum of all positive divisors of j, written as the sum over `Nat.divisors`. The
  subtraction of 1 is exact.
* Only part (i) of the conjecture is formalized; the other parts are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a236765

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The condition in the name of A236765 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  1 < k ∧ 1 < m ∧ k ^ 2 + m = n ∧ ((∑ d ∈ (k ^ 2).divisors, d) + pr m - 1).Prime

/-- A236765: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A236765. -/
theorem main : ∀ n : ℕ, 6 < n → n ≠ 18 → 0 < a n := by
  sorry

end OMA.S_oeis_a236765
