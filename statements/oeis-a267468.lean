import Mathlib

/-!
# A267468: Number of length-n 0..5 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267468
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267468:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(6 - 120*x + 945*x^2 - 3710*x^3 + 7539*x^4 - 7336*x^5 + 2556*x^6) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)^2*(1 - 6*x)).
  a(n) = (-75 - 25*2^(1+n) - 50*3^n + 25*2^(1+n)*3^n - 75*4^n + 413*5^n + 12*5^n*n) / 300.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℚ.
Definition (as for A267465, the 0..2 case): an array is x(0), ..., x(n-1) with entries in 0..5 (a
function Fin n → Fin 6, read as the list of its values). Its first repeated value is x(i) for the
least i with x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays
without a repeated value qualify. The function ok below checks this from the left: if the first
two entries are equal, they give the first repeated value and every later entry must be at most
it; otherwise the first repeated value of the array is that of its tail. This reproduces the
listed values 6, 36, 201, 1096, 5921, ... for n = 1, 2, 3, ... (checked by direct enumeration up
to n = 6 and through the recurrence a(n+2) = 5a(n+1) + 1 + 2^n + 3^n + 4^n + 5^n + 6^n for all
listed terms).
-/

namespace OMA.S_oeis_a267468

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267468: the number of arrays of length n with entries in 0..5 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 6)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 6) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f.
x(6 - 120x + 945x^2 - 3710x^3 + 7539x^4 - 7336x^5 + 2556x^6)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)^2(1 - 6x)),
and a(n) = (-75 - 25*2^(1+n) - 50*3^n + 25*2^(1+n)*3^n - 75*4^n + 413*5^n + 12*5^n*n)/300 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
          (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2 * (1 - 6 * PowerSeries.X)) =
      PowerSeries.X * (6 - 120 * PowerSeries.X + 945 * PowerSeries.X ^ 2 -
        3710 * PowerSeries.X ^ 3 + 7539 * PowerSeries.X ^ 4 - 7336 * PowerSeries.X ^ 5 +
        2556 * PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-75 - 25 * 2 ^ (1 + n) - 50 * 3 ^ n + 25 * 2 ^ (1 + n) * 3 ^ n - 75 * 4 ^ n +
        413 * 5 ^ n + 12 * 5 ^ n * n) / 300 := by
  sorry

end OMA.S_oeis_a267468
