import Mathlib

/-!
# A007392: Mathar's recurrence, corrected to n ≥ 13, and generating function

Source: https://oeis.org/A007392
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Oct 30 2009); the entry records it as a conjecture and notes no proof or
verification of it. The recurrence is false as stated at n = 10 (a(10) = 5, right side 0) and at n = 12
(a(12) = 12, right side 15), in agreement with the numerator x^10*(-5+3*x^2) of the conjectured g.f.; `main`
is the corrected recurrence (n ≥ 13) together with the g.f. Both follow from the formula
a(n) = A007387(n) - b(n) recorded in the entry by Sean A. Irvine (Jan 02 2018), which is used here as the
definition.

A007392 (offset 1): number of strict 3rd-order maximal independent sets in cycle graph;
data 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 0, 12, 0, 21, 5, 32, 17, 45, 38, 65, 70, 99, 115, 156, 180, 247, ...

Conjecture (R. J. Mathar, Oct 30 2009):
a(n) = 3*a(n-2) - 3*a(n-4) + a(n-5) + a(n-6) - 2*a(n-7) + a(n-9) with g.f.
x^10*(-5+3*x^2)/((x^5+x^2-1)*(x-1)^2*(1+x)^2).

Formalization: the entry gives a(n) = A007387(n) - b(n) where b(1) = 0, b(2*n+1) = 2*n+1, b(2*n) = 2 (Sean A.
Irvine, Jan 02 2018), and this formula is used as the definition here. A007387 (offset 1; number of 3rd-order
maximal independent sets in cycle graph) is taken from its entry: its terms a(1..8) = 0, 2, 3, 2, 5, 2, 7, 2
and the recurrence a(n) = a(n-2) + a(n-5) for n ≥ 9 recorded there (`e` below; it continues 9, 7, 11, 14, 13,
23, 20, 34, ...). Index 0 is below the offset: e(0) = b(0) = 0 are conventions, so that a(0) = 0 and the
series with coefficients a(n), n ≥ 0, is the generating function Sum_{n>=1} a(n) x^n. `main` has two parts:
the corrected recurrence (n ≥ 13), which is checked by the data, for example at n = 13:
0 = 3*0 - 3*0 + 0 + 0 - 2*0 + 0, and at n = 14: 21 = 3*12 - 3*5 + 0 + 0 - 2*0 + 0; and the g.f. identity,
stated multiplied by its denominator, over ℤ.
-/

namespace OMA.S_oeis_a007392

open PowerSeries

/-- A007387 (offset 1): e(1..8) = 0, 2, 3, 2, 5, 2, 7, 2 and e(n) = e(n-2) + e(n-5) for n ≥ 9;
e(0) = 0 is a convention. -/
def e : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 2
  | 3 => 3
  | 4 => 2
  | 5 => 5
  | 6 => 2
  | 7 => 7
  | 8 => 2
  | (n + 9) => e (n + 7) + e (n + 4)

/-- The correction term of the entry: b(1) = 0, b(2n+1) = 2n+1 and b(2n) = 2; b(0) = 0 is a convention. -/
def b (n : ℕ) : ℤ := if n ≤ 1 then 0 else if n % 2 = 1 then (n : ℤ) else 2

/-- A007392 through the formula of the entry: a(n) = A007387(n) - b(n). -/
def a (n : ℕ) : ℤ := e n - b n

/-- The corrected recurrence (n ≥ 13): Mathar's recurrence, which fails at n = 10 and n = 12; and
Mathar's conjectured generating function for A007392. -/
theorem main :
    (∀ n : ℕ, 13 ≤ n →
      a n = 3 * a (n - 2) - 3 * a (n - 4) + a (n - 5) + a (n - 6) - 2 * a (n - 7) + a (n - 9)) ∧
    (PowerSeries.mk (fun n => a n) * ((X ^ 5 + X ^ 2 - 1) * (X - 1) ^ 2 * (1 + X) ^ 2) =
      (X ^ 10 * (-5 + 3 * X ^ 2) : ℤ⟦X⟧)) := by
  sorry

end OMA.S_oeis_a007392
