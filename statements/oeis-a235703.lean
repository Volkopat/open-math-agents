import Mathlib

/-!
# A235703: Number of ordered ways to write n = p + q with p a term of A234695 and q a term of A235592.

Source: https://oeis.org/A235703
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A235703 (Zhi-Wei Sun, Jan 14 2014): a(n) > 0 for all n
> 3, and a(n) = 1 only for n = 4, 30, 83.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 2, 2, 3, 3, 3, 3, 4, 2, ...). `a n` is the number of
  pairs (p, q) with n = p + q, p a term of A234695 (a prime p with prime(p) - p + 1 also prime)
  and q a term of A235592, exactly as in the OEIS name.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed (`Nat.nth
  Nat.Prime 0 = 2`), prime(k) is `Nat.nth Nat.Prime (k - 1)` for k >= 1. The helper `pr k` below
  is prime(k).
* A235592 is the set of positive integers k such that k*(k+1) - prime(k) is prime; this is the
  helper `T`. Since prime(k) <= k*(k+1) for k >= 1, the natural-number subtraction is exact.
* A234695 is the sequence of primes p with prime(p) - p + 1 also prime; since prime(p) > p the
  subtraction is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a235703

/-- prime(k), the k-th prime with prime(1) = 2 (for k >= 1). -/
noncomputable def pr (k : ℕ) : ℕ := Nat.nth Nat.Prime (k - 1)

/-- k is a term of A235592: k > 0 and k*(k+1) - prime(k) is prime. -/
def T (k : ℕ) : Prop := 0 < k ∧ (k * (k + 1) - pr k).Prime

/-- The condition in the name of A235703 on a tuple, for a given n. -/
def P (n : ℕ) (p q : ℕ) : Prop :=
  p + q = n ∧ p.Prime ∧ (pr p - p + 1).Prime ∧ T q

/-- A235703: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A235703. -/
theorem main : ∀ n : ℕ, 0 < n → ((3 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({4, 30, 83} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a235703
