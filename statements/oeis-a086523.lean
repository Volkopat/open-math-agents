import Mathlib

/-!
# A086523: Beginning with 5, distinct odd primes such that the arithmetic mean of every pair of successive terms is prime.

Source: https://oeis.org/A086523
Credit: @agchua

Comment of A086523 (the entry is by Amarnath Murthy, Jul 30 2003):
  Conjecture: every prime of the form 6k-1 is a member. Comment from Vim Wenders, May 27 2008:
  The conjecture is wrong. For example 11 and 23 are missing.
The sequence has offset 1 and a(1) = 5. Each later term is the least odd prime p not used before
such that (h + p)/2 is a prime, where h is the previous term (this rule gives all listed terms,
5, 17, 29, 53, 41, 101, ...); the mean is required to be exactly a prime q, 2*q = h + p. If no such
p existed the term would be 0 (sInf of the empty set). The conjecture is stated literally: every
prime p with p mod 6 = 5 is some term a(n), n >= 1.
-/

namespace OMA.S_oeis_a086523

/-- The next term after the terms l (latest first): the least odd prime p not in l whose mean with
the latest term is a prime. -/
noncomputable def next (l : List ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ Odd p ∧ p ∉ l ∧ ∃ q : ℕ, q.Prime ∧ 2 * q = l.headD 0 + p}

/-- seq k is the list a(k+1), a(k), ..., a(1), latest first. -/
noncomputable def seq : ℕ → List ℕ
  | 0 => [5]
  | k + 1 => next (seq k) :: seq k

/-- A086523(n) for n >= 1. -/
noncomputable def a (n : ℕ) : ℕ := (seq (n - 1)).headD 0

/-- The conjecture: every prime of the form 6k-1 is a term. -/
theorem main : ∀ p : ℕ, p.Prime → p % 6 = 5 → ∃ n : ℕ, 1 ≤ n ∧ a n = p := by
  sorry

end OMA.S_oeis_a086523
