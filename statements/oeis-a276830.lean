import Mathlib

/-!
# A276830: Number of ways to write n as ((p-1)/2)^2 + P_2, where p is an odd prime and P_2 is a product of at most two primes.

Source: https://oeis.org/A276830
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A276830 (Zhi-Wei Sun, Sep 20 2016): a(n) > 0 for all n
> 1, and a(n) = 1 only for n = 2, 3, 4, 9, 17, 21, 25, 33, 49, 109, 169, 189, 361, 841, 961,
12769, 19321.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, ...). `a n` is the number of
  pairs (p, m) with p an odd prime, m a product of at most two primes and n = ((p-1)/2)^2 + m,
  exactly as in the OEIS name.
* P_2, `a product of at most two primes`, is a positive integer m with at most two prime factors
  counted with multiplicity (the length of `Nat.primeFactorsList m` is at most 2); this includes m
  = 1, the empty product, which is the reading that reproduces the OEIS data (a(2) = 1 comes from
  2 = ((3-1)/2)^2 + 1).
* For an odd prime p, (p-1)/2 is an exact division.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
* The `a(n) = 1 only for` part is rendered literally as an only-if: a(n) = 1 implies that n is one
  of the listed values.
-/

namespace OMA.S_oeis_a276830

/-- The condition in the name of A276830 on a tuple, for a given n. -/
def P (n : ℕ) (p m : ℕ) : Prop :=
  p.Prime ∧ Odd p ∧ ((p - 1) / 2) ^ 2 + m = n ∧ 0 < m ∧ (Nat.primeFactorsList m).length ≤ 2

/-- A276830: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ | P n t.1 t.2}

/-- The conjecture recorded in A276830. -/
theorem main : ∀ n : ℕ, 0 < n → ((1 < n → 0 < a n) ∧ (a n = 1 →
      n ∈ ({2, 3, 4, 9, 17, 21, 25, 33, 49, 109, 169, 189, 361, 841, 961, 12769, 19321} :
        Finset ℕ))) := by
  sorry

end OMA.S_oeis_a276830
