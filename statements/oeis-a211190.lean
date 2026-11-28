import Mathlib

/-!
# A211190: Number of ways to write 2n = p+2q+3r with p,q,r terms of A210479.

Source: https://oeis.org/A211190
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A211190 (Zhi-Wei Sun, Feb 03 2013): a(n)>0 for all n>8.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, ...). `a n` is the number of
  triples (p, q, r) with 2n = p + 2q + 3r and p, q, r terms of A210479, exactly as in the OEIS
  name.
* A210479 is the sequence of primes p with p - 1 and p + 1 both practical (the helper `S`); p - 1
  is an exact subtraction since p is prime.
* A positive integer m is practical (A005153) if every natural number k <= sigma(m) is a sum of
  distinct divisors of m; this is the helper `Practical`, where sigma(m) is the sum over
  `Nat.divisors m` and a sum of distinct divisors is the sum over a subset of `Nat.divisors m`. 0
  is not practical.
* Only the first sentence of the conjecture is formalized; the `Moreover` sentence (about general
  triples (a, b, c)) is a different statement.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a211190

/-- m is a practical number (A005153): m > 0 and every k <= sigma(m) is a sum of distinct
divisors of m. -/
def Practical (m : ℕ) : Prop :=
  0 < m ∧ ∀ k : ℕ, k ≤ ∑ d ∈ m.divisors, d → ∃ s : Finset ℕ, s ⊆ m.divisors ∧ ∑ d ∈ s, d = k

/-- p is a term of A210479: a prime with p - 1 and p + 1 both practical. -/
def S (p : ℕ) : Prop := p.Prime ∧ Practical (p - 1) ∧ Practical (p + 1)

/-- The condition in the name of A211190 on a tuple, for a given n. -/
def P (n : ℕ) (p q r : ℕ) : Prop :=
  p + 2 * q + 3 * r = 2 * n ∧ S p ∧ S q ∧ S r

/-- A211190: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ × ℕ × ℕ | P n t.1 t.2.1 t.2.2}

/-- The conjecture recorded in A211190. -/
theorem main : ∀ n : ℕ, 8 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a211190
