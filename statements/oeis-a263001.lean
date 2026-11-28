import Mathlib

/-!
# A263001: Number of ordered pairs (k, m) with k > 0 and m > 0 such that n = pi(k*(k+1)) + pi(m*(m+1)/2), where pi(x) denotes the number of primes not exceeding x.

Source: https://oeis.org/A263001
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A263001 (Zhi-Wei Sun, Oct 07 2015): a(n) > 0 for all n
> 2, and a(n) = 1 only for n = 1, 4, 6.

Conventions:
* The sequence has offset 1 (data 1, 0, 2, 1, 3, 1, 3, 2, 3, 3, 3, 4, ...). `a n` is the number of
  pairs (k, m) with k > 0, m > 0 and n = pi(k*(k+1)) + pi(m*(m+1)/2), exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The division by 2 is exact.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a263001

/-- The condition in the name of A263001 on a tuple, for a given n. -/
def P (n : ℕ) (k m : ℕ) : Prop :=
  0 < k ∧ 0 < m ∧ Nat.primeCounting (k * (k + 1)) + Nat.primeCounting (m * (m + 1) / 2) = n

/-- A263001: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A263001. -/
theorem main : ∀ n : ℕ, 0 < n → ((2 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({1, 4, 6} : Finset ℕ))) := by
  sorry

end OMA.S_oeis_a263001
