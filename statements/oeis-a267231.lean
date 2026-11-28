import Mathlib

/-!
# A267231: Number of length-n 0..7 arrays with no following elements greater than or equal to the first repeated value.

Source: https://oeis.org/A267231
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267231:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: 4*x*(2 - 54*x + 595*x^2 - 3437*x^3 + 11088*x^4 - 19495*x^5 + 16287*x^6 - 3546*x^7 - 1260*x^8) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)*(1 - 6*x)*(1 - 7*x)^2).
  a(n) = (-7*(70 + 21*2^(1+n) + 35*3^n + 35*2^(1+n)*3^n + 35*4^n + 42*5^n - 627*7^n) + 60*7^n*n)/2940 for n>1.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for n ≥ 2 in ℚ, as printed (at n = 1 it would
give 57/7 instead of a(1) = 8).
Definition (R. H. Hardin's convention for these arrays, as in A267235): an array is
x(0), ..., x(n-1) with entries in 0..7 (a function Fin n → Fin 8, read as the list of its
values). Its first repeated value is x(i) for the least i with x(i) = x(i+1), and the elements
following it are x(i+2), ..., x(n-1). The condition is that none of these is greater than or
equal to x(i), i.e. all of them are less than x(i); an array with no two equal adjacent entries
satisfies it. The function ok below checks this from the left: if the first two entries are
equal, they give the first repeated value and every later entry must be less than it; otherwise
the first repeated value of the array is that of its tail. This reproduces the listed values
8, 64, 476, 3472, 25088, ... for n = 1, 2, 3, ... (checked by direct enumeration up to n = 5 and
through the recurrence a(n+2) = 7a(n+1) + 0^n + 1 + 2^n + ... + 7^n for all listed terms).
-/

namespace OMA.S_oeis_a267231

/-- The condition on the list of values of an array: every element after the first repeated
value is less than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c < x)) else ok l
  | _ => true

/-- A267231: the number of arrays of length n with entries in 0..7 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 8)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 8) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f.
4x(2 - 54x + 595x^2 - 3437x^3 + 11088x^4 - 19495x^5 + 16287x^6 - 3546x^7 - 1260x^8)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)(1 - 6x)(1 - 7x)^2),
and a(n) = (-7(70 + 21*2^(1+n) + 35*3^n + 35*2^(1+n)*3^n + 35*4^n + 42*5^n - 627*7^n) + 60*7^n*n)/2940 for n > 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) * (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) * (1 - 6 * PowerSeries.X) * (1 - 7 * PowerSeries.X) ^ 2) =
      4 * PowerSeries.X * (2 - 54 * PowerSeries.X + 595 * PowerSeries.X ^ 2 - 3437 * PowerSeries.X ^ 3 + 11088 * PowerSeries.X ^ 4 - 19495 * PowerSeries.X ^ 5 + 16287 * PowerSeries.X ^ 6 - 3546 * PowerSeries.X ^ 7 - 1260 * PowerSeries.X ^ 8) ∧
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = (-7 * (70 + 21 * 2 ^ (1 + n) + 35 * 3 ^ n + 35 * 2 ^ (1 + n) * 3 ^ n + 35 * 4 ^ n + 42 * 5 ^ n - 627 * 7 ^ n) + 60 * 7 ^ n * n) / 2940 := by
  sorry

end OMA.S_oeis_a267231
