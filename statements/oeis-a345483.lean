import Mathlib

/-!
# OEIS A345483: Wu's conjectures: the recurrence for n > 9 and the generating function

Source: https://oeis.org/A345483 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (David Consiglio, Jr., Jun 20 2021), offset 1: Numbers that are the sum of seven squares in six or more
ways. The formula section states: Conjectures from Chai Wah Wu, Apr 25 2024: a(n) = 2*a(n-1) - a(n-2) for n > 9. G.f.: x*(-x^8 + x^7 - x^6 + x^5 - x^4 - x^3 - 52*x + 55)/(x - 1)^2.

Formalization notes:
* A way to write n as a sum of seven squares is a partition of n into seven nonzero
  squares, that is, a multiset of seven positive integers whose squares sum to n (an element
  of `(Finset.Icc 1 n).sym 7`); `ways n` counts them, and the terms are the n with
  `6 <= ways n`.
* a(n) is the term of index n - 1 (from 0) of the terms in increasing order (`Nat.nth`), so
  a(1) is the least term, matching offset 1.
* `main` is the conjunction of both conjectures: the recurrence for every n > 9, stated in
  the integers, and the generating function, stated as the identity
  A(x) (x - 1)^2 = x (-x^8 + x^7 - x^6 + x^5 - x^4 - x^3 - 52*x + 55) in Z[[x]] with
  A(x) = Sum_{n >= 1} a(n) x^n; (x - 1)^2 is invertible in Z[[x]], so this is the stated
  quotient.
* Controls proved in the proof file: a(1..9) = 55, 58, 61, 63, 64, 66, 67, 69, 70, as in the entry's data.
-/

namespace OMA.S_oeis_a345483

/-- The number of ways to write n as a sum of seven positive squares: the number of multisets of
seven positive integers whose squares sum to n. -/
def ways (n : ℕ) : ℕ :=
  (((Finset.Icc 1 n).sym 7).filter
    (fun s : Sym ℕ 7 => ((s : Multiset ℕ).map (· ^ 2)).sum = n)).card

/-- The terms of A345483: the numbers that are the sum of seven squares in six or more ways. -/
def S : Set ℕ := {n | 6 ≤ ways n}

/-- A345483(n), offset 1: the n-th term in increasing order. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun m => m ∈ S) (n - 1)

open PowerSeries in
/-- Wu's conjectures: the recurrence for n > 9 and the generating function. -/
theorem main :
    (∀ n : ℕ, 9 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2)) ∧
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (X - 1) ^ 2 =
        X * (-X ^ 8 + X ^ 7 - X ^ 6 + X ^ 5 - X ^ 4 - X ^ 3 - 52 * X + 55) := by
  sorry

end OMA.S_oeis_a345483
