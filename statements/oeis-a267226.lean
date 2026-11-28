import Mathlib

/-!
# A267226: Number of length-n 0..2 arrays with no following elements greater than or equal to the first repeated value.

Source: https://oeis.org/A267226
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267226:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: x*(3 - 6*x + 2*x^3) / ((1 - x)*(1 - 2*x)^2).
  a(n) = 2^(n+1) + 2^(n-2)*n - 1 for n>1.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for n ≥ 2 in ℚ, as printed (at n = 1 it would
give 7/2 instead of a(1) = 3).
Definition (R. H. Hardin's convention for these arrays, as in A267235): an array is
x(0), ..., x(n-1) with entries in 0..2 (a function Fin n → Fin 3, read as the list of its
values). Its first repeated value is x(i) for the least i with x(i) = x(i+1), and the elements
following it are x(i+2), ..., x(n-1). The condition is that none of these is greater than or
equal to x(i), i.e. all of them are less than x(i); an array with no two equal adjacent entries
satisfies it. The function ok below checks this from the left: if the first two entries are
equal, they give the first repeated value and every later entry must be less than it; otherwise
the first repeated value of the array is that of its tail. This reproduces the listed values
3, 9, 21, 47, 103, ... for n = 1, 2, 3, ... (checked by direct enumeration up to n = 6 and
through the recurrence a(n+2) = 2a(n+1) + 0^n + 1 + 2^n for all listed terms).
-/

namespace OMA.S_oeis_a267226

/-- The condition on the list of values of an array: every element after the first repeated
value is less than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c < x)) else ok l
  | _ => true

/-- A267226: the number of arrays of length n with entries in 0..2 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 3)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 3) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. x(3 - 6x + 2x^3)/((1 - x)(1 - 2x)^2), and
a(n) = 2^(n+1) + 2^(n-2)*n - 1 for n > 1 (n - 2 is a natural number there). -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) ^ 2) =
      PowerSeries.X * (3 - 6 * PowerSeries.X + 2 * PowerSeries.X ^ 3) ∧
    ∀ n : ℕ, 2 ≤ n →
      (a n : ℚ) = 2 ^ (n + 1) + 2 ^ (n - 2) * n - 1 := by
  sorry

end OMA.S_oeis_a267226
