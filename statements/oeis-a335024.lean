import Mathlib

/-!
# OEIS A335024: the two conjectures on when consecutive terms of A056612 are equal

Source: https://oeis.org/A335024 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Petros Hadjicostas, May 19 2020), offset 1: Ratios of consecutive terms of A056612.
Formula: a(n) = A056612(n+1)/A056612(n). Comments: Conjecture 1: a(n) = 1 if and only if
n + 1 = p^k for some prime p and some positive integer k < p. Conjecture 2 (due to Alois P.
Heinz): a(n) = 1 <=> n+1 in A136327.
A056612 (offset 1): a(n) = gcd(n!, n!*(1 + 1/2 + 1/3 + ... + 1/n)).
A136327: Numbers k > 1 such that binomial(2k-1, k-1) == 1 (mod k).

Formalization notes:
* n! (1 + 1/2 + ... + 1/n) is the integer Sum_{i=1..n} n!/i (each quotient is exact), so
  A056612(n) is the gcd of two natural numbers.
* a(n) = A056612(n+1) / A056612(n) as natural-number division; A056612(n) divides
  A056612(n+1) (the proof file proves this), so the quotient is exact.
* Membership in A136327 is k > 1 and binomial(2k-1, k-1) mod k = 1.
* `main` is the conjunction of the two conjectures, each for all n >= 1.
-/

namespace OMA.S_oeis_a335024

/-- A056612(n) = gcd(n!, n! (1 + 1/2 + ... + 1/n)); n! H_n is the integer Sum_{i=1..n} n!/i. -/
def g (n : ℕ) : ℕ := Nat.gcd n.factorial (∑ i ∈ Finset.Icc 1 n, n.factorial / i)

/-- A335024(n) = A056612(n+1) / A056612(n). -/
def a (n : ℕ) : ℕ := g (n + 1) / g n

/-- Membership in A136327: k > 1 and binomial(2k-1, k-1) == 1 (mod k). -/
def InA136327 (k : ℕ) : Prop := 1 < k ∧ Nat.choose (2 * k - 1) (k - 1) % k = 1

/-- Conjecture 1 and Conjecture 2 of the entry. -/
theorem main : (∀ n : ℕ, 1 ≤ n →
      (a n = 1 ↔ ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ k < p ∧ n + 1 = p ^ k)) ∧
    (∀ n : ℕ, 1 ≤ n → (a n = 1 ↔ InA136327 (n + 1))) := by
  sorry

end OMA.S_oeis_a335024
