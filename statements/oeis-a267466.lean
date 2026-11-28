import Mathlib

/-!
# A267466: Number of length-n 0..3 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267466
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267466:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: 2*x*(2 - 18*x + 55*x^2 - 65*x^3 + 23*x^4) / ((1 - x)*(1 - 2*x)*(1 - 3*x)^2*(1 - 4*x)).
  a(n) = (-18 - 9*2^(1+n) + 50*3^n + 9*4^n + 4*3^n*n) / 36.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℚ.
Definition (as for A267465, the 0..2 case): an array is x(0), ..., x(n-1) with entries in 0..3 (a
function Fin n → Fin 4, read as the list of its values). Its first repeated value is x(i) for the
least i with x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays
without a repeated value qualify. The function ok below checks this from the left: if the first
two entries are equal, they give the first repeated value and every later entry must be at most
it; otherwise the first repeated value of the array is that of its tail. This reproduces the
listed values 4, 16, 58, 204, 712, ... for n = 1, 2, 3, ... (checked by direct enumeration up to
n = 7 and through the recurrence a(n+2) = 3a(n+1) + 1 + 2^n + 3^n + 4^n for all listed terms).
-/

namespace OMA.S_oeis_a267466

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267466: the number of arrays of length n with entries in 0..3 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 4)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 4) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 2x(2 - 18x + 55x^2 - 65x^3 + 23x^4)/((1 - x)(1 - 2x)(1 - 3x)^2(1 - 4x)),
and a(n) = (-18 - 9*2^(1+n) + 50*3^n + 9*4^n + 4*3^n*n)/36 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) ^ 2 *
          (1 - 4 * PowerSeries.X)) =
      2 * PowerSeries.X * (2 - 18 * PowerSeries.X + 55 * PowerSeries.X ^ 2 -
        65 * PowerSeries.X ^ 3 + 23 * PowerSeries.X ^ 4) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-18 - 9 * 2 ^ (1 + n) + 50 * 3 ^ n + 9 * 4 ^ n + 4 * 3 ^ n * n) / 36 := by
  sorry

end OMA.S_oeis_a267466
