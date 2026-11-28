import Mathlib

/-!
# OEIS A053697: Barker's conjectures for a base-11 reverse-and-invert recursion

Source: https://oeis.org/A053697 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A053697 (John W. Layman, Feb 14 2000), offset 1: a(n+1)=a(n)+a^(n), where the addition is
in base 11 and where a^(n) is obtained from a(n) by replacing each digit with its multiplicative
inverse modulo 11. Zero digits, if any, are deleted.
Data: 1, 2, 8, 14, 27, 94, 137, 284, 947, 1384, 2847, 9484, ...
Formula section:
Conjectures from Colin Barker, Feb 15 2016: (Start)
a(n) = a(n-2) + 10*a(n-3) - 10*a(n-5) for n>7.
G.f.: x*(1+2*x+7*x^2+2*x^3-x^4+10*x^5-10*x^6+10*x^8) / ((1-x)*(1+x)*(1-10*x^3)). (End)

Formalization notes:
* The terms are numbers written in base 11 and displayed with their base-11 digits. `v n` is the
  number itself: v(1) = 1 and v(n+1) = v(n) + inv(v(n)), where inv replaces every nonzero base-11
  digit d by its inverse modulo 11 (d^9 mod 11) and deletes the zero digits (`inv`).
* a(n) is the base-11 digit string of v(n) read as a decimal numeral (`Nat.ofDigits 10` of the
  base-11 digits), which is how the entry displays the terms; this reproduces all 30 listed
  terms (no digit 10 occurs there), checked by direct computation.
* The entry starts at n = 1; v 0 = 0 gives a 0 = 0, the coefficient of x^0 of the g.f., which
  starts at x^1, so the g.f. is stated for mk a over the integers as A * D = N (D has constant
  term 1).
* The statement is the conjunction of Barker's recurrence (for n > 7, in the integers) and g.f.
-/

namespace OMA.S_oeis_a053697

open PowerSeries

/-- Replace each nonzero base-11 digit by its inverse modulo 11 and delete the zero digits. -/
def inv (x : ℕ) : ℕ :=
  Nat.ofDigits 11 (((Nat.digits 11 x).filter fun d => d ≠ 0).map fun d => d ^ 9 % 11)

/-- The terms as numbers: v 1 = 1 and v (n + 1) = v n + inv (v n). -/
def v : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => v (n + 1) + inv (v (n + 1))

/-- A053697(n): v(n) displayed with its base-11 digits. -/
def a (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 11 (v n))

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = a (n - 2) + 10 * a (n - 3) - 10 * a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) * (1 + X) * (1 - 10 * X ^ 3)) =
      (X * (1 + 2 * X + 7 * X ^ 2 + 2 * X ^ 3 - X ^ 4 + 10 * X ^ 5 - 10 * X ^ 6 + 10 * X ^ 8) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a053697
