import Mathlib

/-!
# A211165: Number of ways to write n as the sum of a prime p with p-1 and p+1 both practical, a prime q with q+2 also prime, and a Fibonacci number.

Source: https://oeis.org/A211165
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A211165 (Zhi-Wei Sun, Jan 30 2013): a(n)>0 for all n>5.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 1, 1, 3, 3, 4, 5, 3, ...). `a n` is the number of
  triples (p, q, f) with n = p + q + f, where p is a prime with p - 1 and p + 1 both practical, q
  is a prime with q + 2 also prime, and f is a Fibonacci number, exactly as in the OEIS name.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* A Fibonacci number is a value of `Nat.fib` (0, 1, 2, 3, 5, 8, ...); representations are counted
  by the value f of the Fibonacci number (so the value 1 = F(1) = F(2) is counted once) and the
  value 0 = F(0) is allowed. This is the reading that reproduces the OEIS data (for example a(6) =
  1 comes from 6 = 3 + 3 + 0).
* p - 1 is an exact subtraction since p is prime.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a211165

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- The condition in the name of A211165 on a tuple, for a given n. -/
def P (n : ℕ) (p q f : ℕ) : Prop :=
  p + q + f = n ∧ p.Prime ∧ Practical (p - 1) ∧ Practical (p + 1) ∧ q.Prime ∧ (q + 2).Prime ∧
  (∃ j : ℕ, Nat.fib j = f)

/-- A211165: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A211165. -/
theorem main : ∀ n : ℕ, 5 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a211165
