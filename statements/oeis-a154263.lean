import Mathlib

/-!
# A154263: Number of triples <p, s,t> such that p+F_s+(F_t)^3=n, where p is an odd prime, s and t are greater than one and F_s or F_t is odd.

Source: https://oeis.org/A154263
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A154263 (Zhi-Wei Sun): a(n)>0 for every n=5,6,...;
in other words, any integer n>4 can be written as the sum of an odd prime, a positive Fibonacci
number and a cube of a positive Fibonacci number, with one of two Fibonacci numbers odd.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 1, 2, 1, 3, 1, 2, 2, ...). `a n` is the number
  of triples (p, s, t) of natural numbers with p an odd prime, s > 1, t > 1,
  p + F_s + (F_t)^3 = n and (F_s odd or F_t odd), exactly as in the OEIS name; triples are
  counted by the indices (s, t), as in the OEIS example for n = 14.
* F_k is the Fibonacci number `Nat.fib k` (F_0 = 0, F_1 = 1, F_2 = 1, F_3 = 2).
* The set of such triples is finite for every n (p <= n, and F_s <= n, F_t <= n bound s and t),
  so `Set.ncard` is its number of elements.
* The conjecture is stated for all n >= 5, the range given in the entry.
-/

namespace OMA.S_oeis_a154263

/-- A154263: number of triples (p, s, t) with p an odd prime, s, t > 1,
p + F_s + (F_t)^3 = n and F_s or F_t odd. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | x.1.Prime ∧ Odd x.1 ∧ 1 < x.2.1 ∧ 1 < x.2.2 ∧
    x.1 + Nat.fib x.2.1 + (Nat.fib x.2.2) ^ 3 = n ∧
    (Odd (Nat.fib x.2.1) ∨ Odd (Nat.fib x.2.2))}

/-- The conjecture of Sun: a(n) > 0 for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a154263
