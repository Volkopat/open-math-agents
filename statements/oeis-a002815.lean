import Mathlib

/-!
# A002815: the generating function of n + pi(1) + ... + pi(n)

Source: https://oeis.org/A002815
Credit: @ivillar

A002815 (offset 0): a(n) = n + Sum_{k=1..n} pi(k), where pi(k) is the number of primes ≤ k;
data 0, 1, 3, 6, 9, 13, 17, 22, 27, 32, 37, 43, ...

Conjecture (L. Edson Jeffery, Nov 25 2013): the g.f. is (Sum_{N>=1} x^A008578(N))/(1-x)^2 =
(x + x^2 + x^3 + x^5 + x^7 + x^11 + x^13 + ...)/(1-x)^2, where A008578 lists 1 together with the
primes.

Formalization: the generating function is a formal power series over ℤ and the identity is stated
with the denominator cleared. The numerator is the series whose coefficient of x^n is 1 when
n = 1 or n is prime, and 0 otherwise.
-/

namespace OMA.S_oeis_a002815

open PowerSeries

/-- a(n) = n + ∑_{k=1}^{n} π(k). -/
def a (n : ℕ) : ℕ := n + ∑ k ∈ Finset.Icc 1 n, Nat.primeCounting k

/-- Jeffery's conjectured generating function. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 2 =
      PowerSeries.mk (fun n => if n = 1 ∨ n.Prime then (1 : ℤ) else 0) := by
  sorry

end OMA.S_oeis_a002815
