import Mathlib

/-!
# A133710: Column l=3 of irregular triangle in A133709.

Source: https://oeis.org/A133710
Credit: @agchua

Colin Barker (Apr 03 2020), in the formula section of A133710:
  Conjectures from Colin Barker, Apr 03 2020: (Start)
  G.f.: x^2*(3 + 14*x - 51*x^2 + 60*x^3 - 31*x^4 + 6*x^5) / (1 - x)^7.
  a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
  (End)
A133710 has offset 1: a(m) = T(m, 3) for m >= 1, where T is the triangle A133709, T(m, l) = number
of labeled covers of size l of a finite set of m unlabeled elements. The triangle is defined here
by the Maple program of A133709 (R. J. Mathar, Nov 23 2011), which the Maple program of A133710
calls as A133709(m,3): T(m, 1) = 1 and, for l >= 2,
  T(m, l) = Sum_{i=0..l-1} (-1)^i*binomial(l,i)*binomial(2^(l-i)+m-2,m)
            - Sum_{i=1..l-1} stirling2(l,i)*T(m,i).
In the Lean definition the second sum runs over i in 0..l-1 with the term i = 0 set to 0, which is
the sum over i = 1..l-1; stirling2 is Nat.stirlingSecond. The definition reproduces the 34 listed
terms of A133709 (rows m = 1..5) and the 30 listed terms 0, 3, 35, 131, 347, ... of A133710.
This file states both conjectures: the recurrence for n > 7 (all its indices are then >= 1), and the
g.f. as an identity of formal power series over Q,
  (sum_{n >= 1} a(n) X^n) * (1 - X)^7 = X^2 (3 + 14X - 51X^2 + 60X^3 - 31X^4 + 6X^5);
the coefficient of X^0 is set to 0 because the sequence starts at n = 1 (offset 1).
-/

namespace OMA.S_oeis_a133710

/-- The triangle A133709 as computed by its Maple program: T(m, 1) = 1 and, for l other than 1,
T(m, l) = Sum_{i=0..l-1} (-1)^i C(l, i) C(2^(l-i) + m - 2, m) - Sum_{i=1..l-1} S2(l, i) T(m, i),
with S2 = Nat.stirlingSecond. -/
def T (m l : ℕ) : ℤ :=
  if l = 1 then 1
  else (∑ i ∈ Finset.range l, (-1) ^ i * (l.choose i : ℤ) * ((2 ^ (l - i) + m - 2).choose m : ℤ)) -
    ∑ i : Fin l, if (i : ℕ) = 0 then 0 else (Nat.stirlingSecond l i : ℤ) * T m i
termination_by l
decreasing_by all_goals omega

/-- A133710(m) = A133709(m, 3), column l = 3 of the triangle (offset 1). -/
def a (m : ℕ) : ℤ := T m 3

/-- Barker's conjectures: the recurrence of order 7 for n > 7, and the g.f.
x^2 (3 + 14x - 51x^2 + 60x^3 - 31x^4 + 6x^5) / (1 - x)^7. -/
theorem main : (∀ n : ℕ, 8 ≤ n →
      a n = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else (a n : ℚ)) * (1 - PowerSeries.X) ^ 7 =
      PowerSeries.X ^ 2 * (3 + 14 * PowerSeries.X - 51 * PowerSeries.X ^ 2 +
        60 * PowerSeries.X ^ 3 - 31 * PowerSeries.X ^ 4 + 6 * PowerSeries.X ^ 5) := by
  sorry

end OMA.S_oeis_a133710
