import Mathlib

/-!
# A028359: Two-bell analog of A028355.

Source: https://oeis.org/A028359
Credit: @agchua

Chai Wah Wu (Apr 18 2024), in the formula section of A028359:
  Conjectures from Chai Wah Wu, Apr 18 2024: (Start)
  a(n) = 101*a(n-3) - 100*a(n-6) for n > 6.
  G.f.: x*(10*x^4 + 20*x^3 + 12*x^2 + 2*x + 1)/(100*x^6 - 101*x^3 + 1). (End)
Definition: A028355 is How the astronomical clock (Orloj) in Prague would strike 1,2,3,...
(digits follow 12343212343..., n-th group adds to n); its two-bell analog A028359 is described in
the comment of Seiichi Manyama (Oct 31 2018): Consider the infinite digits: 121212... . We can
break this into a sequence of integers such that the sum of digits in the n-th value is n.
So the digit string is d(0) d(1) d(2) ... = 1 2 1 2 ..., the first n groups use the first c(n)
digits, where c(n) is the number of digits whose digit sum is 1 + 2 + ... + n = n(n+1)/2 (such
a number exists and is unique, since the digit sums of the prefixes increase strictly), and
a(n) is group n, the digits in positions c(n-1), ..., c(n)-1, read as a decimal number. The
offset is 1. For n = 0 the definition gives the empty group, a(0) = 0, so the power series
Sum a(n) X^n below is the g.f. of the entry, stated as an identity of formal power series over ℚ:
(Sum a(n) X^n) * (100 X^6 - 101 X^3 + 1) = X (10 X^4 + 20 X^3 + 12 X^2 + 2 X + 1).
The recurrence is stated for n > 6, as in the entry, in ℤ.
-/

namespace OMA.S_oeis_a028359

/-- The digit string 1 2 1 2 ...: d(j) is the digit in position j (positions from 0). -/
def d (j : ℕ) : ℕ := if j % 2 = 0 then 1 else 2

/-- S(j) = d(0) + ... + d(j-1), the digit sum of the first j digits. -/
def S (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, d i

/-- c(n): the number of digits in the groups 1, ..., n, i.e. the j with S(j) = n(n+1)/2. -/
noncomputable def c (n : ℕ) : ℕ := sInf {j : ℕ | S j = n * (n + 1) / 2}

/-- A028359: a(n) is group n, the digits d(c(n-1)), ..., d(c(n)-1) read in base 10
(the digit d(c(n)-1-i) has weight 10^i). -/
noncomputable def a (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (c n - c (n - 1)), d (c n - 1 - i) * 10 ^ i

/-- Wu's conjectures: a(n) = 101 a(n-3) - 100 a(n-6) for n > 6, and the g.f.
x(10x^4 + 20x^3 + 12x^2 + 2x + 1)/(100x^6 - 101x^3 + 1). -/
theorem main :
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 101 * (a (n - 3) : ℤ) - 100 * (a (n - 6) : ℤ)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * (100 * PowerSeries.X ^ 6 - 101 * PowerSeries.X ^ 3 + 1) =
      PowerSeries.X * (10 * PowerSeries.X ^ 4 + 20 * PowerSeries.X ^ 3 + 12 * PowerSeries.X ^ 2 +
        2 * PowerSeries.X + 1) := by
  sorry

end OMA.S_oeis_a028359
