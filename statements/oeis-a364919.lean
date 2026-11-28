import Mathlib

/-!
# OEIS A364919: the sequence is a permutation of the positive integers

Source: https://oeis.org/A364919 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Michael De Vlieger, Aug 30 2023), offset 0: a(0) = 1; a(n) is the smallest number m not
already in the sequence such that rad(m) divides A019565(n). Comments: Let k be a squarefree number
and define R_k to be the set of numbers m such that rad(m) | k. For n > 0, a(n) is the smallest m
in R_k such that a(j) != m, j < n. Conjecture: permutation of natural numbers.

Formalization notes:
* A019565(n) is the product of prime(i+1) over the positions i of the 1-bits of n
  (A019565(n) = Product_{k >= 0} prime(k+1)^(floor(n/2^k) mod 2)); `Nat.nth Nat.Prime i` is
  prime(i+1). rad(m) is the product of the distinct primes dividing m.
* The terms are positive integers: m = 0 is excluded (with rad(0) = 1 it would otherwise be
  a(1), while the data give a(1) = 2).
* The natural numbers of the conjecture are the positive integers, the values of the sequence:
  `main` says that every term is positive, that the sequence is injective, and that every
  positive integer is a term.
* Controls proved in the proof file: a(1) = 2 and a(2) = 3, as in the entry's data.
-/

namespace OMA.S_oeis_a364919

/-- A019565(n): the product of prime(i+1) over the positions i of the 1-bits of n
(`Nat.nth Nat.Prime i` is prime(i+1)). -/
noncomputable def P (n : ℕ) : ℕ :=
  ∏ i ∈ (Finset.range n).filter (fun i => n.testBit i), Nat.nth Nat.Prime i

/-- rad(m): the product of the distinct primes dividing m. -/
def rad (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, p

/-- A364919(n): a(0) = 1, and a(n) is the smallest positive m, different from every earlier term,
with rad(m) dividing A019565(n). -/
noncomputable def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf {m | 0 < m ∧ (∀ j : Fin (n + 1), a j ≠ m) ∧ rad m ∣ P (n + 1)}
decreasing_by exact j.isLt

/-- The conjecture: a is a permutation of the positive integers. -/
theorem main : (∀ n, 0 < a n) ∧ Function.Injective a ∧ ∀ m, 0 < m → ∃ n, a n = m := by
  sorry

end OMA.S_oeis_a364919
