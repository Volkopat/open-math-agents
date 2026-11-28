import Mathlib

/-!
# Row sums of the divisor triangle A103994

A104117 takes the value k+1 at 2^k and zero elsewhere, starting at n=1.
Its conjectured interpretation is the row sum of A103994.

For a function f, write D(f)(n,k) = f(n/k) if k divides n and zero
otherwise, with positive indices. Products of these matrices correspond
to Dirichlet convolution: an intermediate column is a divisor between
k and n. The Möbius matrix A054525 is D(μ). A115361 is D(P), where
P indicates powers of two: it is the inverse of the identity minus the
matrix with a one at (2k,k). The defining matrix products for A129360
and A103994 therefore give A103994 = D(μ * P * P). Its row n is summed
over the divisor columns, since all remaining entries vanish.

Sources: https://oeis.org/A104117, https://oeis.org/A103994,
https://oeis.org/A129360, https://oeis.org/A115361
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a104117
open ArithmeticFunction

def powerIndicator : ArithmeticFunction ℤ where
  toFun n := if n = 2 ^ n.log2 then 1 else 0
  map_zero' := by decide

def coefficient : ArithmeticFunction ℤ := moebius * powerIndicator * powerIndicator

theorem main : ∀ n : ℕ, 0 < n →
    (∑ k ∈ n.divisors, coefficient (n / k)) =
      if n = 2 ^ n.log2 then (n.log2 : ℤ) + 1 else 0 := by
  sorry

end OMA.S_oeis_a104117
