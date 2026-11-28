import Mathlib

/-!
# A210722: Number of ways to write n = (2-(n mod 2))p+q+2^k with p, q-1, q+1 all prime, and p-1, p+1, q all practical.

Source: https://oeis.org/A210722
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A210722 (Zhi-Wei Sun, Jan 29 2013): a(n)>0 except for n
= 1,...,8, 10, 520, 689, 740.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 3, 1, ...). `a n` is the number of
  triples (p, q, k) of natural numbers with n = (2 - (n mod 2))*p + q + 2^k, such that p, q - 1, q
  + 1 are all prime and p - 1, p + 1, q are all practical, exactly as in the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* k ranges over the natural numbers 0, 1, 2, ... (2^k >= 1).
* 2 - n % 2 is an exact subtraction (n mod 2 is 0 or 1); p - 1 is exact since p is prime; q - 1 is
  exact since practical numbers are positive.
* `a(n) > 0 except for n = ...` is rendered as an equivalence for n >= 1 (the offset): a(n) > 0
  exactly when n is not one of the listed values. That a(n) = 0 at each listed value agrees with
  direct computation.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a210722

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A210722 on a tuple, for a given n. -/
def P (n : ℕ) (p q k : ℕ) : Prop :=
  (2 - n % 2) * p + q + 2 ^ k = n ∧ p.Prime ∧ (q - 1).Prime ∧ (q + 1).Prime ∧ Practical (p - 1) ∧
  Practical (p + 1) ∧ Practical q

/-- A210722: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A210722. -/
theorem main : ∀ n : ℕ, 0 < n → (0 < a n ↔
      n ∉ ({1, 2, 3, 4, 5, 6, 7, 8, 10, 520, 689, 740} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a210722
