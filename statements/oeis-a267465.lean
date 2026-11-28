import Mathlib

/-!
# A267465: Number of length-n 0..2 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267465
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267465:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(3 - 15*x + 21*x^2 - 7*x^3) / ((1 - x)*(1 - 2*x)^2*(1 - 3*x)).
  a(n) = 2^n + 3^(n-1) + 2^(n-2)*(n+1) - 1.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator. The closed form is stated for all n ≥ 1 in ℚ, with the power 2^(n-2) taken
as an integer power, so that it is 1/2 for n = 1 (the formula gives a(1) = 2 + 1 + 1 - 1 = 3).
Definition: an array is x(0), ..., x(n-1) with entries in 0..2 (a function Fin n → Fin 3, read
as the list of its values). Its first repeated value is x(i) for the least i with
x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays without a
repeated value qualify. The function ok below checks this from the left: if the first two
entries are equal, they give the first repeated value and every later entry must be at most it;
otherwise the first repeated value of the array is that of its tail. This reproduces the listed
values 3, 9, 24, 62, 160, ... for n = 1, 2, 3, ... (checked up to n = 11).
-/

namespace OMA.S_oeis_a267465

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267465: the number of arrays of length n with entries in 0..2 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 3)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 3) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. x(3 - 15x + 21x^2 - 7x^3)/((1 - x)(1 - 2x)^2(1 - 3x)), and
a(n) = 2^n + 3^(n-1) + 2^(n-2)(n+1) - 1 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) ^ 2 * (1 - 3 * PowerSeries.X)) =
      PowerSeries.X * (3 - 15 * PowerSeries.X + 21 * PowerSeries.X ^ 2 -
        7 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = 2 ^ n + 3 ^ (n - 1) + 2 ^ ((n : ℤ) - 2) * (n + 1) - 1 := by
  sorry

end OMA.S_oeis_a267465
