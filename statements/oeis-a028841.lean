import Mathlib

/-!
# OEIS A028841: Barker's g.f. and recurrence for the n whose iterated digit sum is Fibonacci

Source: https://oeis.org/A028841 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (N. J. A. Sloane), offset 1: Iterated sum of digits of n is a Fibonacci number. Comment
(Alonso del Arte, Jan 20 2020): Intermediate iterations don't count. For example, with 85, we have
8 + 5 = 13, which is a Fibonacci number, but 1 + 3 = 4, which is not a Fibonacci numbers, so 85 is
not in the sequence. The formula section states: Conjectures from Colin Barker, Feb 18 2020:
(Start) G.f.: x*(1 + x + x^2 + 2*x^3 + 3*x^4 + x^5) / ((1 - x)^2*(1 + x + x^2 + x^3 + x^4)).
a(n) = a(n-1) + a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* The iterated sum of digits applies the decimal digit sum until a single digit remains; only that
  digit is tested, as the comment says. The Fibonacci numbers are the values of `Nat.fib`.
* The terms are positive (a(1) = 1; 0 is not a term); with offset 1, a(n) is `Nat.nth P (n - 1)`.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..6) = 1, 2, 3, 5, 8, 10, as in the entry, and the iterated
  digit sum of 98 is 8 (the entry's example 98 -> 17 -> 8).
-/

namespace OMA.S_oeis_a028841

/-- The decimal digit sum. -/
def ds (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- The iterated sum of digits: apply `ds` until a single digit remains. -/
def idr (n : ℕ) : ℕ := if h : n < 10 then n else idr (ds n)
termination_by n
decreasing_by
  unfold ds
  rw [Nat.digits_def' (by norm_num) (by omega), List.sum_cons]
  have := Nat.digit_sum_le 10 (n / 10)
  omega

/-- The entry's condition for positive `n`: the iterated digit sum is a Fibonacci number. -/
def P (n : ℕ) : Prop := 0 < n ∧ ∃ k, Nat.fib k = idr n

/-- A028841 (offset 1): the `n`-th number with the property, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

open PowerSeries in
/-- Barker's conjectures: the g.f., and a(n) = a(n-1) + a(n-5) - a(n-6) for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
        ((1 - X) ^ 2 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4)) =
      X * (1 + X + X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4 + X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 1) + a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a028841
