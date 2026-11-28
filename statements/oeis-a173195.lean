import Mathlib

/-!
# Squares which are sums of three powers of four

A173195 lists in increasing order the positive integers which are square
roots of sums of three powers of four, allowing arbitrary integer exponents.
A263132 lists the positive m for which binomial(4m−1,m) is odd. George
Beck conjectured that the first list is three times the second.

To encode integer exponents exactly, multiply the square equation by 4^h.
The three exponents before clearing the denominator are x−h, x+a−h and
x+b−h in the integers. Every ordered triple has this representation, and
the gaps satisfy a ≤ b. Multiplication by three preserves the increasing
order of the two lists, so their elementwise equality is equivalent to the
membership equivalence below.

Sources: https://oeis.org/A173195 and https://oeis.org/A263132
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a173195

def threePowers (k : ℕ) : Prop :=
  ∃ h x a b : ℕ, a ≤ b ∧ 4^x * (1 + 4^a + 4^b) = 4^h * k^2

def binomialOdd (m : ℕ) : Prop := (4*m-1).choose m % 2 = 1

theorem main : ∀ k : ℕ, 0 < k →
    (threePowers k ↔ ∃ m : ℕ, 0 < m ∧ binomialOdd m ∧ k = 3*m) := by
  sorry

end OMA.S_oeis_a173195
