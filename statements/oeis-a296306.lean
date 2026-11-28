import Mathlib

/-!
# Divisor power sums and palindromic prefixes

The first three conjectures of OEIS A296306 compare divisor power sums over
all divisors and over odd divisors. The sequence is indexed from one.
A002450(j) = (4^j - 1)/3.
Sources: https://oeis.org/A296306, https://oeis.org/A002450 and https://oeis.org/A006095
(OEIS Foundation, CC BY-SA 4.0).
Credit: @marcelopierry
-/

namespace OMA.S_oeis_a296306

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Sum of the k-th powers of the odd positive divisors of n. -/
def oddSum (k n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter Odd, d^k

/-- A296306, defined as the quotient of the two sums of squares. -/
def a (n : ℕ) : ℕ := sigma 2 n / oddSum 2 n

/-- A002450, indexed from zero. -/
def geometric (j : ℕ) : ℕ := (4^j-1)/3

/-- Divisibility for every power, the full set of positive-indexed values
including their power-of-two witnesses, and palindromicity of each requested prefix. -/
theorem main :
    (∀ k n : ℕ, 0 < n → oddSum k n ∣ sigma k n) ∧
    ((∀ n : ℕ, 0 < n → ∃ j : ℕ, 0 < j ∧ a n = geometric j) ∧
     (∀ j : ℕ, 0 < j → a (2^(j-1)) = geometric j)) ∧
    (∀ h : ℕ, 0 < h → ∀ i : ℕ, 0 < i → i < 2^h → a i = a (2^h-i)) := by
  sorry

end OMA.S_oeis_a296306
