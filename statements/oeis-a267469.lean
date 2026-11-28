import Mathlib

/-!
# A267469: Number of length-n 0..6 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267469
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267469:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(7 - 189*x + 2086*x^2 - 12110*x^3 + 39543*x^4 - 71617*x^5 + 65212*x^6 - 22212*x^7) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)*(1 - 6*x)^2*(1 - 7*x)).
  a(n) = (-504 - 315*2^n - 280*3^n - 315*4^n - 504*5^n + 3409*6^n + 360*7^n + 35*2^(1+n)*3^n*n) / 2520.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℚ.
Definition (as for A267465, the 0..2 case): an array is x(0), ..., x(n-1) with entries in 0..6 (a
function Fin n → Fin 7, read as the list of its values). Its first repeated value is x(i) for the
least i with x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays
without a repeated value qualify. The function ok below checks this from the left: if the first
two entries are equal, they give the first repeated value and every later entry must be at most
it; otherwise the first repeated value of the array is that of its tail. This reproduces the
listed values 7, 49, 322, 2072, 13216, ... for n = 1, 2, 3, ... (checked by direct enumeration up
to n = 5 and through the recurrence a(n+2) = 6a(n+1) + 1 + 2^n + ... + 7^n for all
listed terms).
-/

namespace OMA.S_oeis_a267469

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267469: the number of arrays of length n with entries in 0..6 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 7)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 7) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f.
x(7 - 189x + 2086x^2 - 12110x^3 + 39543x^4 - 71617x^5 + 65212x^6 - 22212x^7)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)(1 - 6x)^2(1 - 7x)),
and a(n) = (-504 - 315*2^n - 280*3^n - 315*4^n - 504*5^n + 3409*6^n + 360*7^n + 35*2^(1+n)*3^n*n)/2520 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) * (1 - 6 * PowerSeries.X) ^ 2 * (1 - 7 * PowerSeries.X)) =
      PowerSeries.X * (7 - 189 * PowerSeries.X + 2086 * PowerSeries.X ^ 2 - 12110 * PowerSeries.X ^ 3 + 39543 * PowerSeries.X ^ 4 - 71617 * PowerSeries.X ^ 5 + 65212 * PowerSeries.X ^ 6 - 22212 * PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-504 - 315 * 2 ^ n - 280 * 3 ^ n - 315 * 4 ^ n - 504 * 5 ^ n + 3409 * 6 ^ n + 360 * 7 ^ n + 35 * 2 ^ (1 + n) * 3 ^ n * n) / 2520 := by
  sorry

end OMA.S_oeis_a267469
