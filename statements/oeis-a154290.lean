import Mathlib

/-!
# A154290: Number of ordered triples <p,s,t> satisfying p+F_s+L_t = n, where p is an odd prime, s >= 2 and F_s or L_t is odd.

Source: https://oeis.org/A154290
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A154290 (Zhi-Wei Sun): a(n)>0 for every n=5,6,...;
in other words, any integer n>4 can be written as the sum of an odd prime, a positive Fibonacci
number and a Lucas number, with the Fibonacci number or the Lucas number odd.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 1, 2, 3, 5, 5, 7, 6, 8, ...). `a n` is the number
  of triples (p, s, t) of natural numbers with p an odd prime, s >= 2, t >= 0,
  p + F_s + L_t = n and (F_s odd or L_t odd), exactly as in the OEIS name. Triples are counted
  by the indices (s, t); the index t ranges over all natural numbers including 0 and 1, as in
  the OEIS example for n = 10, which uses L_0 = 2 and L_1 = 1.
* F_k is `Nat.fib k`. L_k is the Lucas number, defined below by L_0 = 2, L_1 = 1,
  L_(k+2) = L_k + L_(k+1).
* The set of such triples is finite for every n, so `Set.ncard` is its number of elements.
* Only the first sentence of the conjecture (a(n) > 0 for n >= 5) is formalized; the
  additional lim inf claim in the entry is a separate conjecture and is not part of the
  statement.
-/

namespace OMA.S_oeis_a154290

/-- The Lucas numbers: L_0 = 2, L_1 = 1, L_(k+2) = L_k + L_(k+1). -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (k + 2) => L k + L (k + 1)

/-- A154290: number of triples (p, s, t) with p an odd prime, s >= 2,
p + F_s + L_t = n and F_s or L_t odd. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {x : ℕ × ℕ × ℕ | x.1.Prime ∧ Odd x.1 ∧ 2 ≤ x.2.1 ∧
    x.1 + Nat.fib x.2.1 + L x.2.2 = n ∧ (Odd (Nat.fib x.2.1) ∨ Odd (L x.2.2))}

/-- The conjecture of Sun: a(n) > 0 for every n >= 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a154290
