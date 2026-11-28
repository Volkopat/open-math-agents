import Mathlib

/-!
# A267470: Number of length-n 0..7 arrays with no following elements larger than the first repeated value.

Source: https://oeis.org/A267470
Credit: @agchua

Colin Barker (Feb 05 2018), in the formula section of A267470:
  Conjectures from Colin Barker, Feb 05 2018: (Start)
  G.f.: 4*x*(2 - 70*x + 1029*x^2 - 8253*x^3 + 39228*x^4 - 112119*x^5 + 185785*x^6
    - 160106*x^7 + 53244*x^8) / ((1 - x)*(1 - 2*x)*(1 - 3*x)*(1 - 4*x)*(1 - 5*x)*(1 - 6*x)
    *(1 - 7*x)^2*(1 - 8*x)).
  a(n) = (-980 - 147*2^(2+n) - 245*2^(1+2*n) - 490*3^n - 245*2^(2+n)*3^n - 588*5^n
    + 7818*7^n + 735*8^n + 120*7^n*n) / 5880.
  (End)
This file states both parts. The offset is 1, so the g.f. is the series Sum_{n ≥ 1} a(n) X^n =
X * Sum_{n ≥ 0} a(n+1) X^n, stated as an identity of formal power series over ℚ after multiplying
by the denominator, and the closed form is stated for all n ≥ 1 in ℚ.
Definition (as for A267465, the 0..2 case): an array is x(0), ..., x(n-1) with entries in 0..7 (a
function Fin n → Fin 8, read as the list of its values). Its first repeated value is x(i) for the
least i with x(i) = x(i+1); the condition is that no element after it is larger than x(i). Arrays
without a repeated value qualify. The function ok below checks this from the left: if the first
two entries are equal, they give the first repeated value and every later entry must be at most
it; otherwise the first repeated value of the array is that of its tail. This reproduces the
listed values 8, 64, 484, 3592, 26440, ... for n = 1, 2, 3, ... (checked by direct enumeration up
to n = 5 and through the recurrence a(n+2) = 7a(n+1) + 1 + 2^n + ... + 8^n for all listed terms).
-/

namespace OMA.S_oeis_a267470

/-- The condition on the list of values of an array: no element after the first repeated value
is larger than it. -/
def ok : List ℕ → Bool
  | x :: l@(y :: t) => if x = y then t.all (fun c => decide (c ≤ x)) else ok l
  | _ => true

/-- A267470: the number of arrays of length n with entries in 0..7 that satisfy ok. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Fin 8)).filter
    (fun x => ok (List.ofFn (fun i => ((x i : Fin 8) : ℕ))) = true)).card

/-- Barker's conjectures: the g.f. 4x(2 - 70x + 1029x^2 - 8253x^3 + 39228x^4 - 112119x^5 +
185785x^6 - 160106x^7 + 53244x^8)/((1 - x)(1 - 2x)(1 - 3x)(1 - 4x)(1 - 5x)(1 - 6x)(1 - 7x)^2(1 - 8x)),
and a(n) = (-980 - 147*2^(2+n) - 245*2^(1+2n) - 490*3^n - 245*2^(2+n)*3^n - 588*5^n + 7818*7^n +
735*8^n + 120*7^n*n)/5880 for n ≥ 1. -/
theorem main :
    PowerSeries.X * PowerSeries.mk (fun n => (a (n + 1) : ℚ)) *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X) *
          (1 - 4 * PowerSeries.X) * (1 - 5 * PowerSeries.X) * (1 - 6 * PowerSeries.X) *
          (1 - 7 * PowerSeries.X) ^ 2 * (1 - 8 * PowerSeries.X)) =
      4 * PowerSeries.X * (2 - 70 * PowerSeries.X + 1029 * PowerSeries.X ^ 2 -
        8253 * PowerSeries.X ^ 3 + 39228 * PowerSeries.X ^ 4 - 112119 * PowerSeries.X ^ 5 +
        185785 * PowerSeries.X ^ 6 - 160106 * PowerSeries.X ^ 7 + 53244 * PowerSeries.X ^ 8) ∧
    ∀ n : ℕ, 1 ≤ n →
      (a n : ℚ) = (-980 - 147 * 2 ^ (2 + n) - 245 * 2 ^ (1 + 2 * n) - 490 * 3 ^ n -
        245 * 2 ^ (2 + n) * 3 ^ n - 588 * 5 ^ n + 7818 * 7 ^ n + 735 * 8 ^ n +
        120 * 7 ^ n * n) / 5880 := by
  sorry

end OMA.S_oeis_a267470
