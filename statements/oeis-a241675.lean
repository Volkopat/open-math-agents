import Mathlib

/-!
# A241675: a(n) = |{0 < k < n/2: k is a Fibonacci number with x^2 == k (mod n) for no integer x}|.

Source: https://oeis.org/A241675
Credit: @agchua

Comments of A241675:
  a(n) > 0 for all n > 4 if and only if the conjecture in A241568 holds.
  In fact, if n > 0 is a multiple of 4, then x^2 == F(3) = 2 (mod n) for no integer x. If n > 4
  is composite with an odd prime divisor p, then by the conjecture in A241568 there should exist
  a Fibonacci number k < p <= n/2 such that x^2 == k (mod p) for no integer x and hence
  x^2 == k (mod n) for no integer x.
The conjecture in A241568 meant here is its part (i), which the entry A241568 states as:
  Conjecture: (i) a(n) > 0 for all n > 2. In other words, for any prime p > 3, there is a
  Fibonacci number among 1, ..., (p-1)/2 which is a quadratic nonresidue modulo p.
It is stated in its second form (for 1 <= k <= (p-1)/2, k is a quadratic nonresidue modulo p iff
x^2 == k (mod p) for no integer x). The first claim of A241675 is stated: a(n) > 0 for all n > 4
iff that conjecture holds. The offset of A241675 is 1; 0 < k < n/2 is written 0 < k and 2k < n.
The definition below gives the listed terms 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 1, 3, ...
-/

namespace OMA.S_oeis_a241675

/-- a(n): the number of Fibonacci numbers k with 0 < k < n/2 such that x^2 == k (mod n) for no
integer x. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {k : ℕ | 0 < k ∧ 2 * k < n ∧ (∃ i : ℕ, Nat.fib i = k) ∧
    ∀ x : ℤ, ¬ x ^ 2 ≡ (k : ℤ) [ZMOD (n : ℤ)]}

/-- Part (i) of the conjecture in A241568: for any prime p > 3 there is a Fibonacci number among
1, ..., (p-1)/2 which is a quadratic nonresidue modulo p. -/
def ConjectureA241568 : Prop :=
  ∀ p : ℕ, p.Prime → 3 < p → ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (∃ i : ℕ, Nat.fib i = k) ∧
    ∀ x : ℤ, ¬ x ^ 2 ≡ (k : ℤ) [ZMOD (p : ℤ)]

/-- The comment of A241675: a(n) > 0 for all n > 4 iff the conjecture in A241568 holds. -/
theorem main : (∀ n : ℕ, 4 < n → 0 < a n) ↔ ConjectureA241568 := by
  sorry

end OMA.S_oeis_a241675
