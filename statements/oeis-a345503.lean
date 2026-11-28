import Mathlib

/-!
# OEIS A345503: Wu's recurrence and generating function for sums of nine squares in six ways

Source: https://oeis.org/A345503 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (David Consiglio, Jr., Jun 20 2021), offset 1: Numbers that are the sum of nine squares in
six or more ways. Comment: Numbers n such that A025433(n) >= 6 (David A. Corneth, Apr 26 2024),
where A025433(n) is the number of partitions of n into nine nonzero squares. The formula section
states: Conjectures from Chai Wah Wu, Apr 25 2024: a(n) = 2*a(n-1) - a(n-2) for n > 9. G.f.:
x*(-x^8 + x^7 - x^6 + x^5 - x^4 + x^3 - 7*x^2 - 40*x + 48)/(x - 1)^2.

Formalization notes:
* A way to write n as a sum of nine squares is a partition of n into nine nonzero squares, that
  is, a multiset of nine positive integers whose squares sum to n (an element of
  `(Finset.Icc 1 n).sym 9`); `ways n` counts them, and the terms are the n with `6 <= ways n`.
* a(n) is the term of index n - 1 (from 0) of the terms in increasing order (`Nat.nth`), so
  a(1) is the least term, matching offset 1.
* `main` is the conjunction of both conjectures: the recurrence for every n > 9, stated in the
  integers, and the generating function, stated as the identity
  A(x) (x - 1)^2 = x (-x^8 + x^7 - x^6 + x^5 - x^4 + x^3 - 7x^2 - 40x + 48) in Z[[x]] with
  A(x) = Sum_{n >= 1} a(n) x^n; (x - 1)^2 is invertible in Z[[x]], so this is the stated
  quotient.
* Controls proved in the proof file: a(1..9) = 48, 56, 57, 59, 60, 62, 63, 65, 66, as in the
  entry's data.
-/

namespace OMA.S_oeis_a345503

/-- The number of ways to write n as a sum of nine positive squares: the number of multisets of
nine positive integers whose squares sum to n (A025433). -/
def ways (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n).sym 9).filter
    (fun s : Sym ℕ 9 => ((s : Multiset ℕ).map (· ^ 2)).sum = n)).card

/-- The terms of A345503: the numbers that are the sum of nine squares in six or more ways. -/
def S : Set ℕ := {n | 6 ≤ ways n}

/-- A345503(n), offset 1: the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => m ∈ S) (n - 1)

open PowerSeries in
/-- Wu's conjectures: the recurrence for n > 9 and the generating function. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
        X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 + X ^ 3 - 7 * X ^ 2 - 40 * X + 48) := by
  sorry

end OMA.S_oeis_a345503
