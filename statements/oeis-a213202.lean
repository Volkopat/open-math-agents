import Mathlib

/-!
# A213202: Number of ways to write n = p + sum_{k=1..m}(-1)^(m-k)*p_k, where p is a Sophie Germain prime and p_k is the k-th prime.

Source: https://oeis.org/A213202
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A213202 (Zhi-Wei Sun, Mar 01 2013): a(n)>0 for all n>2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 2, 2, 3, 3, 2, 2, 3, 1, 2, ...). `a n` is the number of
  pairs (p, m) with m >= 1 and n = p + sum_{k=1..m} (-1)^(m-k)*p_k, where p is a Sophie Germain
  prime and p_k is the k-th prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* s_m = sum_{k=1..m} (-1)^(m-k) p_k is the helper `s m`, computed in `ℤ`; m ranges over the
  positive integers (m >= 1), and the equation is stated in `ℤ` with n and the other summand cast.
  Representations are counted as pairs (summand, m).
* A Sophie Germain prime is a prime p such that 2*p + 1 is also prime.
* Only the first sentence of the conjecture (the claim about this sequence) is formalized; the
  further claims in the comment are different statements.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a213202

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- s_m = sum_{k=1..m} (-1)^(m-k) p_k, the alternating sum of the first m primes, as an integer. -/
noncomputable def s (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 m, (-1 : ℤ) ^ (m - k) * (pr k : ℤ)

/-- The condition in the name of A213202 on a tuple, for a given n. -/
def P (n : ℕ) (p m : ℕ) : Prop :=
  0 < m ∧ (p : ℤ) + s m = n ∧ p.Prime ∧ (2 * p + 1).Prime

/-- A213202: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A213202. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a213202
