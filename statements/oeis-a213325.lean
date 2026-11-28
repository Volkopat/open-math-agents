import Mathlib

/-!
# A213325: Number of ways to write n = q + sum_{k=1}^m(-1)^{m-k}p_k, where p_k is the k-th prime, and q is a practical number with q-4 and q+4 also practical.

Source: https://oeis.org/A213325
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A213325 (Zhi-Wei Sun, Mar 03 2013): a(n)>0 for all n>8.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, ...). `a n` is the number of
  pairs (q, m) with m >= 1 and n = q + sum_{k=1..m} (-1)^(m-k)*p_k, where p_k is the k-th prime
  and q is a practical number with q - 4 and q + 4 also practical, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* s_m = sum_{k=1..m} (-1)^(m-k) p_k is the helper `s m`, computed in `ℤ`; m ranges over the
  positive integers (m >= 1), and the equation is stated in `ℤ` with n and the other summand cast.
  Representations are counted as pairs (summand, m).
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* Natural-number subtraction is truncated: where the true value would be zero or negative the
  truncated value is 0, which is neither prime nor practical, so the condition is unchanged.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a213325

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- s_m = sum_{k=1..m} (-1)^(m-k) p_k, the alternating sum of the first m primes, as an integer. -/
noncomputable def s (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (m - k) * (pr k : ℤ)

/-- The condition in the name of A213325 on a tuple, for a given n. -/
def P (n : ℕ) (q m : ℕ) : Prop :=
  0 < m ∧ (q : ℤ) + s m = n ∧ Practical q ∧ Practical (q - 4) ∧ Practical (q + 4)

/-- A213325: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A213325. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a213325
