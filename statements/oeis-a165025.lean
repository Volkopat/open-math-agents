import Mathlib

/-!
# OEIS A165025: Barker's conjectures for the cycles of the base-4 Kaprekar map

Source: https://oeis.org/A165025 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jaredwilder.

Entry A165025 (Joseph Myers, Sep 04 2009), offset 1: Number of cycles of n-digit numbers
(including fixed points) under the base-4 Kaprekar map A165012.
A165012: image of n under the base-4 Kaprekar map n -> (n with digits sorted into descending
order) - (n with digits sorted into ascending order).
Data: 1, 0, 1, 2, 1, 3, 1, 4, 3, 5, 4, 8, ...
Formula section:
Conjectures from Colin Barker, Jun 01 2017: (Start)
G.f.: x*(1 - x^2 + x^3 - 2*x^6 + 3*x^8 - x^10) / ((1 - x)^3*(1 + x)^2*(1 + x + x^2)).
a(n) = 2*a(n-2) + a(n-3) - a(n-4) - 2*a(n-5) + a(n-7) for n>7.
(End)

Formalization notes:
* An n-digit number is one whose base-4 representation has exactly n digits, 0 counting as a
  1-digit number. On n-digit numbers the map sorts the n digits: `kap n x` is the number with the
  digits of x in descending order minus the number with them in ascending order (`digs n x`
  lists the n digits of x, least significant first; `Nat.ofDigits 4` reads such a list).
* A cycle of n-digit numbers is a cycle of the map all of whose members are n-digit numbers (an
  image with fewer digits leaves the class). Each cycle is counted once, through its least member
  (`IsRep`). This reading gives the listed terms 1, 0, 1, 2, 1, 3, 1 for n = 1..7 (direct
  computation).
* `a 0` = 0: there are no 0-digit numbers; this is the coefficient of x^0 of the g.f., which
  starts at x^1, so the g.f. is stated for mk a over the integers as A * D = N (D has constant
  term 1).
* The statement is the conjunction of Barker's recurrence (for n > 7, in the integers) and g.f.
-/

namespace OMA.S_oeis_a165025

open PowerSeries

/-- The n base-4 digits of x, least significant first. -/
def digs (n x : ℕ) : List ℕ := List.ofFn fun i : Fin n => x / 4 ^ (i : ℕ) % 4

/-- The base-4 Kaprekar map on n-digit numbers: digits in descending order minus digits in
ascending order. -/
def kap (n x : ℕ) : ℕ :=
  Nat.ofDigits 4 ((digs n x).mergeSort fun a b => decide (a ≤ b)) -
    Nat.ofDigits 4 ((digs n x).mergeSort fun a b => decide (b ≤ a))

/-- The number of base-4 digits of x (0 has one digit). -/
def nDigits (x : ℕ) : ℕ := max 1 (Nat.digits 4 x).length

/-- x lies on a cycle of n-digit numbers and is the least member of that cycle. -/
def IsRep (n x : ℕ) : Prop :=
  nDigits x = n ∧
    (∃ k, 1 ≤ k ∧ (kap n)^[k] x = x ∧ ∀ j < k, nDigits ((kap n)^[j] x) = n) ∧
    ∀ j, x ≤ (kap n)^[j] x

/-- A165025(n): the number of cycles of n-digit numbers under the base-4 Kaprekar map. -/
noncomputable def a (n : ℕ) : ℕ := {x : ℕ | IsRep n x}.ncard

/-- Barker's conjectures. -/
theorem main :
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 2 * a (n - 2) + a (n - 3) - a (n - 4) - 2 * a (n - 5) + a (n - 7)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 * (1 + X + X ^ 2)) =
      (X * (1 - X ^ 2 + X ^ 3 - 2 * X ^ 6 + 3 * X ^ 8 - X ^ 10) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a165025
