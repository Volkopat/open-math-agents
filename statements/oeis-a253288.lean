import Mathlib

/-!
# OEIS A253288: the permutation is self-inverse

Source: https://oeis.org/A253288 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane, Dec 29 2014), offset 1: Each term a(n) satisfies four properties: 1,
divisible by all prime factors of n; 2, divisible by only the prime factors of n; 3, not equal to
any of the terms a(1), a(2), ... a(n-1); 4, smallest number satisfying 1-3 if A005361(n) is even,
or second smallest number satisfying 1-3 if A005361(n) is odd. Data: 1, 4, 9, 2, 25, 12, 49, ...
Comment: Conjecture: this permutation of positive integers is self-inverse. (Michael De Vlieger,
Dec 10 2022.) A005361: product of exponents of prime factorization of n.

Formalization notes:
* Properties 1 and 2 are stated literally (`SameFactors n k`); property 3 says k differs from
  a(m) for 1 <= m < n; the smallest and second smallest numbers with properties 1-3 are
  `Nat.nth _ 0` and `Nat.nth _ 1` (0 never has property 2, so all candidates are positive).
* A005361(n) is the product of the exponents of n, the empty product 1 for n = 1.
* a(1) = 1, as in the data and in the entry's Maple program: the only number with properties 1-2
  for n = 1 is 1 itself, so no second smallest one exists. `a 0 = 0` is a placeholder outside the
  entry's range.
* `main` is the conjecture: a(a(n)) = n for every n >= 1.
* Controls proved in the proof file: a(1) = 1, a(2) = 4, a(4) = 2.
-/

namespace OMA.S_oeis_a253288

/-- A005361(n): the product of the exponents in the prime factorization of n (1 for n = 1). -/
def a005361 (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, n.factorization p

/-- Properties 1 and 2: k is divisible by all prime factors of n and by no other prime. -/
def SameFactors (n k : ℕ) : Prop :=
  (∀ p, p.Prime → p ∣ n → p ∣ k) ∧ (∀ p, p.Prime → p ∣ k → p ∣ n)

/-- A253288: a(1) = 1, and for n >= 2, a(n) is the smallest (A005361(n) even) or second smallest
(A005361(n) odd) number with properties 1-2 that is not among a(1), ..., a(n-1). (a(0) = 0 is a
placeholder outside the entry's range.) -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => Nat.nth (fun k => SameFactors (n + 2) k ∧ ∀ m (_ : m < n + 2), 1 ≤ m → a m ≠ k)
      (if Even (a005361 (n + 2)) then 0 else 1)

/-- De Vlieger's conjecture: the permutation is self-inverse. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (a n) = n := by
  sorry

end OMA.S_oeis_a253288
