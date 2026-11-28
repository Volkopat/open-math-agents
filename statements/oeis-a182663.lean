import Mathlib

/-!
# A182663: Number of ordered ways to write n = p + q with q > 0 such that p and 2*p + prime(q) are both prime.

Source: https://oeis.org/A182663
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A182663 (Zhi-Wei Sun), part (i):
a(n) > 0 for all n > 5.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 1, 0, 2, 2, 2, 3, 3, 1, 1, ...). `a n` is the number
  of natural numbers p < n (so that q = n - p > 0) such that p is prime and
  2*p + prime(n - p) is prime.
* prime(k) is the k-th prime with prime(1) = 2; since `Nat.nth Nat.Prime` is 0-indexed
  (`Nat.nth Nat.Prime 0 = 2`), prime(q) is `Nat.nth Nat.Prime (q - 1)`, here with
  q = n - p >= 1.
* Only part (i) of the conjecture in the entry is formalized; parts (ii) and (iii) are
  different statements not about this sequence.
-/

namespace OMA.S_oeis_a182663

/-- A182663: number of p < n with p prime and 2*p + prime(n - p) prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p < n ∧ p.Prime ∧ (2 * p + Nat.nth Nat.Prime (n - p - 1)).Prime}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 5. -/
theorem main : ∀ n : ℕ, 5 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a182663
