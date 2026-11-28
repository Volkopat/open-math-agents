import Mathlib

/-!
# OEIS A202456: Barker's recurrence and generating function

Source: https://oeis.org/A202456 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 19 2011), offset 1: Number of (n+2) X 5 binary arrays with consecutive
windows of three bits considered as a binary number nondecreasing in every row and column.
Data: 1000, 1876, 3362, 5735, 9338, 14586, 21972, 32073, ... The formula section states:
Empirical: a(n) = (1/20)*n^5 + 2*n^4 + (275/12)*n^3 + 113*n^2 + (10351/30)*n + 517.
Conjectures from Colin Barker, May 31 2018: (Start) G.f.: x*(1000 - 4124*x + 7106*x^2 -
6297*x^3 + 2838*x^4 - 517*x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) -
15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin (n + 2) → Fin 5 → Bool, with rows x i; row i is the bit string
  `List.ofFn (x i)` and column j is `List.ofFn fun i => x i j`.
* `win b0 b1 b2` is the window b0 b1 b2 read as a binary number, 4 b0 + 2 b1 + b2, and
  `windowsOK s` says that the windows of three consecutive bits of s, from left to right, are
  nondecreasing (it holds trivially for strings of length at most 3). `good x` asks this for
  every row and every column.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..31), all the entry's listed terms, and Hardin's
  empirical polynomial for all n >= 1.
-/

namespace OMA.S_oeis_a202456

open PowerSeries

/-- The window of three bits b0 b1 b2, read as a binary number. -/
def win (b0 b1 b2 : Bool) : ℕ := 4 * b0.toNat + 2 * b1.toNat + b2.toNat

/-- The consecutive windows of three bits of a bit string, read as binary numbers, are
nondecreasing. -/
def windowsOK : List Bool → Bool
  | b0 :: b1 :: b2 :: b3 :: rest => decide (win b0 b1 b2 ≤ win b1 b2 b3) && windowsOK (b1 :: b2 :: b3 :: rest)
  | _ => true

/-- An array with rows x i (each row a function Fin 5 → Bool): in every row and in every column the
consecutive windows of three bits are nondecreasing. -/
def good {r : ℕ} (x : Fin r → Fin 5 → Bool) : Bool :=
  decide (∀ i, windowsOK (List.ofFn (x i)) = true) && decide (∀ j, windowsOK (List.ofFn fun i => x i j) = true)

/-- A202456(n): the number of good (n+2) X 5 binary arrays. -/
def a (n : ℕ) : ℕ := (Finset.univ.filter fun x : Fin (n + 2) → Fin 5 → Bool => good x = true).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
        6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (1000 - 4124 * X + 7106 * X ^ 2 - 6297 * X ^ 3 + 2838 * X ^ 4 - 517 * X ^ 5) := by
  sorry

end OMA.S_oeis_a202456
