import Mathlib

/-!
# A242753: Number of ordered ways to write n = k + m with 0 < k <= m such that the inverse of k mod prime(k) among 1, ..., prime(k) - 1 is prime and the inverse of m mod prime(m) among 1, ..., prime(m) - 1 is also prime.

Source: https://oeis.org/A242753
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A242753 (Zhi-Wei Sun, May 22 2014): a(n) > 0 for all n
> 3.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 1, 2, 1, 2, 2, 2, 1, 2, ...). `a n` is the number of
  pairs (k, m) of natural numbers with n = k + m, 0 < k <= m, such that the inverse of k mod
  prime(k) among 1, ..., prime(k) - 1 is prime and the inverse of m mod prime(m) among 1, ...,
  prime(m) - 1 is also prime, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* For j >= 1 we have j < prime(j), so j is invertible modulo prime(j) and its inverse among 1,
  ..., prime(j) - 1 is the unique q in that range with j*q == 1 (mod prime(j)). The helper `Q j`
  says that this q is prime: there is a prime q < prime(j) with j*q mod prime(j) = 1.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a242753

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- The inverse of j mod prime(j) among 1, ..., prime(j) - 1 is prime. -/
def Q (j : ℕ) : Prop := ∃ q : ℕ, q.Prime ∧ q < pr j ∧ j * q % pr j = 1

/-- The condition in the name of A242753 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  k + m = n ∧ 0 < k ∧ k ≤ m ∧ Q k ∧ Q m

/-- A242753: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A242753. -/
theorem main : ∀ n : ℕ, 3 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a242753
