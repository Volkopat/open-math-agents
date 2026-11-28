import Mathlib

/-!
# A267467: Number of length-n 0..4 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267467
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267467:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(5 - 70*x + 365*x^2 - 870*x^3 + 920*x^4 - 326*x^5) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)^2*(1 - 5*x)).
  a(n) = (-80 - 15*2^(2+n) - 80*3^n + 335*4^n + 48*5^n) / 240 + 4^(-2+n)*n.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator. The closed form is stated for all n ≥ 1 in ℚ, with the power 4^(-2+n) taken
as an integer power, so that it is 1/4 for n = 1 (the formula then gives a(1) = 19/4 + 1/4 = 5).
Definition (as for A267465, the 0..2 case): an array is x(0), ..., x(n-1) with entries in 0..4 (a
function Fin n → Fin 5, read as the list of its values). Its first repeated value is x(i) for the
least i with x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays
without a repeated value qualify. The function ok below checks this from the left: if the first
two entries are equal, they give the first repeated value and every later entry must be at most
it; otherwise the first repeated value of the array is that of its tail. This reproduces the
listed values 5, 25, 115, 515, 2285, ... for n = 1, 2, 3, ... (checked by direct enumeration up
to n = 7 and through the recurrence a(n+2) = 4a(n+1) + 1 + 2^n + 3^n + 4^n + 5^n for all listed
terms).
-/

namespace OMA.S_oeis_a267467

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267467: the number of arrays of length n with entries in 0..4 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 5)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 5) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f.
x(5 - 70x + 365x^2 - 870x^3 + 920x^4 - 326x^5)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)^2(1 - 5x)), and
a(n) = (-80 - 15*2^(2+n) - 80*3^n + 335*4^n + 48*5^n)/240 + 4^(-2+n)*n for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
          (1 - 4 * PowerSeries.X) ^ 2 * (1 - 5 * PowerSeries.X)) =
      PowerSeries.X * (5 - 70 * PowerSeries.X + 365 * PowerSeries.X ^ 2 -
        870 * PowerSeries.X ^ 3 + 920 * PowerSeries.X ^ 4 - 326 * PowerSeries.X ^ 5) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-80 - 15 * 2 ^ (2 + n) - 80 * 3 ^ n + 335 * 4 ^ n + 48 * 5 ^ n) / 240 +
        4 ^ (-2 + (n : ℤ)) * n := by
  sorry

end OMA.S_oeis_a267467
