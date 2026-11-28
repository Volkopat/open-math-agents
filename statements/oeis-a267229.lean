import Mathlib

/-!
# A267229: Number of length-n 0..5 arrays with no following elements greater than or equal to the first repeated value.

Source: https://oeis.org/A267229
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267229:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(6 - 84*x + 435*x^2 - 1010*x^3 + 969*x^4 - 172*x^5 - 120*x^6) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)^2).
  a(n) = (-5*(15 + 5*2^(1+n) + 10*3^n + 15*4^n - 97*5^n) + 12*5^n*n) / 300 for n>1. (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for n ≥ 2 in ℚ, as printed (at n = 1 it would
give 31/5 instead of a(1) = 6).
Definition (R. H. Hardin's convention for these arrays, as in A267235): an array is
x(0), ..., x(n-1) with entries in 0..5 (a function Fin n → Fin 6, read as the list of its
values). Its first repeated value is x(i) for the least i with x(i) = x(i+1), and the elements
following it are x(i+2), ..., x(n-1). The condition is that none of these is greater than or
equal to x(i), i.e. all of them are less than x(i); an array with no two equal adjacent entries
satisfies it. The function ok below checks this from the left: if the first two entries are
equal, they give the first repeated value and every later entry must be less than it; otherwise
the first repeated value of the array is that of its tail. This reproduces the listed values
6, 36, 195, 1030, 5375, ... for n = 1, 2, 3, ... (checked by direct enumeration up to n = 6 and
through the recurrence a(n+2) = 5a(n+1) + 0^n + 1 + 2^n + 3^n + 4^n + 5^n for all listed terms).
-/

namespace OMA.S_oeis_a267229

/-- The condition on the list of values of an array: every element after the first repeated
value is less than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c < x)) else ok l
  | _ => true

/-- A267229: the number of arrays of length n with entries in 0..5 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 6)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 6) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f.
x(6 - 84x + 435x^2 - 1010x^3 + 969x^4 - 172x^5 - 120x^6)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)^2),
and a(n) = (-5(15 + 5*2^(1+n) + 10*3^n + 15*4^n - 97*5^n) + 12*5^n*n)/300 for n > 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) ^ 2) =
      PowerSeries.X * (6 - 84 * PowerSeries.X + 435 * PowerSeries.X ^ 2 - 1010 * PowerSeries.X ^ 3 + 969 * PowerSeries.X ^ 4 - 172 * PowerSeries.X ^ 5 - 120 * PowerSeries.X ^ 6) ∧
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = (-5 * (15 + 5 * 2 ^ (1 + n) + 10 * 3 ^ n + 15 * 4 ^ n - 97 * 5 ^ n) + 12 * 5 ^ n * n) / 300 := by
  sorry

end OMA.S_oeis_a267229
